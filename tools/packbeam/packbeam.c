/***************************************************************************
 *   Copyright 2018 by Davide Bettio <davide@uninstall.it>                 *
 *                                                                         *
 *   This program is free software; you can redistribute it and/or modify  *
 *   it under the terms of the GNU Lesser General Public License as        *
 *   published by the Free Software Foundation; either version 2 of the    *
 *   License, or (at your option) any later version.                       *
 *                                                                         *
 *   This program is distributed in the hope that it will be useful,       *
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of        *
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *
 *   GNU General Public License for more details.                          *
 *                                                                         *
 *   You should have received a copy of the GNU General Public License     *
 *   along with this program; if not, write to the                         *
 *   Free Software Foundation, Inc.,                                       *
 *   51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA .        *
 ***************************************************************************/

#include <assert.h>
#include <libgen.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#ifdef WITH_ZLIB
#include <zlib.h>
#endif

#include "../../src/libAtomVM/iff.c"
#include "../../src/libAtomVM/avmpack.h"
#include "../../src/platforms/generic_unix/mapped_file.h"

#define LITT_UNCOMPRESSED_SIZE_OFFSET 8
#define LITT_HEADER_SIZE 12

#define END_OF_FILE 0
#define BEAM_START_FLAG 1
#define BEAM_CODE_FLAG 2
#define BUF_SIZE 1024

typedef struct FileData {
    uint8_t *data;
    size_t   size;
} FileData;

static void pad_and_align(FILE *f);
static void *uncompress_literals(const uint8_t *litT, int size, size_t *uncompressedSize);
static void add_module_header(FILE *f, const char *module_name, uint32_t flags);
static void pack_beam_file(FILE *pack, const uint8_t *data, size_t size, const char *filename, int is_entrypoint);

static int do_pack(int argc, char **argv, int is_archive);
static int do_list(int argc, char **argv);

static void usage3(FILE *out, const char *program, const char *msg) {
    if (!IS_NULL_PTR(msg)) {
        fprintf(out, "%s\n", msg);
    }
    fprintf(out, "Usage: %s [-h] [-l] <avm-file> [<options>]\n", program);
    fprintf(out, "    -h                                                Print this help menu.\n");
    fprintf(out, "    -l <input-avm-file>                               List the contents of an AVM file.\n");
    fprintf(out, "    [-a] <output-avm-file> <input-beam-or-avm-file>+  Create an AVM file (archive if -a specified).\n"
    );
}

static void usage(const char *program)
{
    usage3(stdout, program, NULL);
}


int main(int argc, char **argv)
{
    int opt;

    const char *action = "pack";
    int is_archive = 0;
    while ((opt = getopt(argc, argv, "hal")) != -1) {
        switch(opt) {
            case 'h':
                usage(argv[0]);
                return EXIT_SUCCESS;
            case 'a':
                is_archive = 1;
                break;
            case 'l':
                action = "list";
                break;
            case '?': {
                char buf[BUF_SIZE];
                snprintf(buf, BUF_SIZE, "Unknown option: %c", optopt);
                usage3(stderr, argv[0], buf);
                return EXIT_FAILURE;
            }
        }
    }

    int new_argc    = argc - optind;
    char **new_argv = argv + optind;

    if (new_argc < 1) {
        usage3(stderr, argv[0], "Missing avm file.\n");
        return EXIT_FAILURE;
    }

    if (!strcmp(action, "pack")) {
        if (new_argc < 2) {
            usage3(stderr, argv[0], "Missing options for pack\n");
            return EXIT_FAILURE;
        }
        return do_pack(new_argc, new_argv, is_archive);
    } else {
        return do_list(new_argc, new_argv);
    }
}


static void *pack_beam_fun(void *accum, const void *section_ptr, uint32_t section_size, const void *beam_ptr, uint32_t flags, const char *section_name)
{
    UNUSED(beam_ptr);
    UNUSED(flags);
    UNUSED(section_name);

    FILE *pack = (FILE *)accum;
    assert(fwrite(section_ptr, sizeof(unsigned char), section_size, pack) == section_size);
    return accum;
}

FileData read_file_data(FILE *file)
{
    fseek(file, 0, SEEK_END);
    size_t size = ftell(file);
    fseek(file, 0, SEEK_SET);
    uint8_t *data = malloc(size);
    if (!data) {
        fprintf(stderr, "Unable to allocate %zu bytes\n", size);
        exit(EXIT_FAILURE);
    }
    assert(fread(data, sizeof(uint8_t), size, file) == size);

    FileData file_data = {
        .data = data,
        .size = size
    };
    return file_data;
}

static int is_avm_file(FILE *file)
{
    FileData file_data = read_file_data(file);
    int ret = avmpack_is_valid(file_data.data, file_data.size);
    free(file_data.data);
    return ret;
}

static int is_beam_file(FILE *file)
{
    FileData file_data = read_file_data(file);
    int ret = iff_is_valid_beam(file_data.data);
    free(file_data.data);
    return ret;
}

static void validate_pack_options(int argc, char ** argv)
{
    for (int i = 0;  i < argc;  ++i) {
        const char *filename = argv[i];
        FILE *file = fopen(filename, "r");
        if (i == 0) {
            if (file && !is_avm_file(file)) {
                char buf[BUF_SIZE];
                snprintf(buf, BUF_SIZE, "Invalid AVM file: %s", filename);
                usage3(stderr, "PackBeam", buf);
                exit(EXIT_FAILURE);
            }
        } else {
            if (!file) {
                char buf[BUF_SIZE];
                snprintf(buf, BUF_SIZE, "%s does not exist", filename);
                usage3(stderr, "PackBeam", buf);
                exit(EXIT_FAILURE);
            } else if (!is_avm_file(file) && !is_beam_file(file)) {
                char buf[BUF_SIZE];
                snprintf(buf, BUF_SIZE, "Invalid AVM or BEAM file: %s", filename);
                usage3(stderr, "PackBeam", buf);
                exit(EXIT_FAILURE);
            }
        }
    }
}

static int do_pack(int argc, char **argv, int is_archive)
{
    validate_pack_options(argc, argv);

    FILE *pack = fopen(argv[0], "w");
    if (!pack) {
        char buf[BUF_SIZE];
        snprintf(buf, BUF_SIZE, "Cannot open output file for writing %s", argv[0]);
        perror(buf);
        return EXIT_FAILURE;
    }

    const unsigned char pack_header[24] =
    {
        0x23, 0x21, 0x2f, 0x75,
        0x73, 0x72, 0x2f, 0x62,
        0x69, 0x6e, 0x2f, 0x65,
        0x6e, 0x76, 0x20, 0x41,
        0x74, 0x6f, 0x6d, 0x56,
        0x4d, 0x0a, 0x00, 0x00
    };
    assert(fwrite(pack_header, sizeof(unsigned char), 24, pack) == 24);

    for (int i = 1; i < argc; i++) {
        FILE *file = fopen(argv[i], "r");
        if (!file) {
            char buf[BUF_SIZE];
            snprintf(buf, BUF_SIZE, "Cannot open file %s", argv[i]);
            perror(buf);
            return EXIT_FAILURE;
        }

        fseek(file, 0, SEEK_END);
        size_t file_size = ftell(file);
        fseek(file, 0, SEEK_SET);


        uint8_t *file_data = malloc(file_size);
        if (!file_data) {
            fprintf(stderr, "Unable to allocate %zu bytes\n", file_size);
            return EXIT_FAILURE;
        }
        assert(fread(file_data, sizeof(uint8_t), file_size, file) == file_size);
        if (avmpack_is_valid(file_data, file_size)) {
            avmpack_fold(pack, file_data, pack_beam_fun);
        } else {
            char *filename = basename(argv[i]);
            pack_beam_file(pack, file_data, file_size, filename, !is_archive && i == 1);
        }
    }

    add_module_header(pack, "end", END_OF_FILE);
    fclose(pack);

    return EXIT_SUCCESS;
}

static void pack_beam_file(FILE *pack, const uint8_t *data, size_t size, const char *section_name, int is_entrypoint)
{
    size_t zero_pos = ftell(pack);

    if (is_entrypoint) {
        add_module_header(pack, section_name, BEAM_CODE_FLAG | BEAM_START_FLAG);
    } else {
        add_module_header(pack, section_name, BEAM_CODE_FLAG);
    }

    int written_beam_header_pos = ftell(pack);
    const unsigned char beam_header[12] =
    {
        0x46, 0x4f, 0x52, 0x31,
        0x00, 0x00, 0x00, 0x00,
        0x42, 0x45, 0x41, 0x4d
    };
    assert(fwrite(beam_header, 1, 12, pack) == 12);


    unsigned long offsets[MAX_OFFS];
    unsigned long sizes[MAX_SIZES];
    scan_iff(data, size, offsets, sizes);

    if (offsets[AT8U]) {
        assert(fwrite(data + offsets[AT8U], sizeof(uint8_t), sizes[AT8U] + IFF_SECTION_HEADER_SIZE, pack) == sizes[AT8U] + IFF_SECTION_HEADER_SIZE);
        pad_and_align(pack);
    }
    if (offsets[CODE]) {
        fwrite(data + offsets[CODE], sizeof(uint8_t), sizes[CODE] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }
    if (offsets[EXPT]) {
        fwrite(data + offsets[EXPT], sizeof(uint8_t), sizes[EXPT] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }
    if (offsets[LOCT]) {
        fwrite(data + offsets[LOCT], sizeof(uint8_t), sizes[LOCT] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }
    if (offsets[IMPT]) {
        fwrite(data + offsets[IMPT], sizeof(uint8_t), sizes[IMPT] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }
    if (offsets[LITU]) {
        fwrite(data + offsets[LITU], sizeof(uint8_t), sizes[LITU] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }
    if (offsets[FUNT]) {
        fwrite(data + offsets[FUNT], sizeof(uint8_t), sizes[FUNT] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }
    if (offsets[STRT]) {
        fwrite(data + offsets[STRT], sizeof(uint8_t), sizes[STRT] + IFF_SECTION_HEADER_SIZE, pack);
        pad_and_align(pack);
    }

    if (offsets[LITT]) {
        size_t u_size;
        void *deflated = uncompress_literals(data + offsets[LITT], sizes[LITT], &u_size);
        assert(fwrite("LitU", sizeof(uint8_t), 4, pack) == 4);
        uint32_t size_field = ENDIAN_SWAP_32(u_size);
        assert(fwrite(&size_field, sizeof(size_field), 1, pack) == 1);
        assert(fwrite(deflated, sizeof(uint8_t), u_size, pack) == u_size);
        free(deflated);
    }

    pad_and_align(pack);

    size_t end_of_module_pos = ftell(pack);

    size_t rsize = end_of_module_pos - zero_pos;
    uint32_t size_field = ENDIAN_SWAP_32(rsize);
    fseek(pack, zero_pos, SEEK_SET);
    assert(fwrite(&size_field, sizeof(uint32_t), 1, pack) == 1);
    fseek(pack, end_of_module_pos, SEEK_SET);

    int beam_written_size = end_of_module_pos - written_beam_header_pos;
    uint32_t beam_written_size_field = ENDIAN_SWAP_32(beam_written_size);
    fseek(pack, written_beam_header_pos + 4, SEEK_SET);
    assert(fwrite(&beam_written_size_field , sizeof(uint32_t), 1, pack) == 1);
    fseek(pack, end_of_module_pos, SEEK_SET);
}


static void *print_section(void *accum, const void *section_ptr, uint32_t section_size, const void *beam_ptr, uint32_t flags, const char *section_name)
{
    UNUSED(section_ptr);
    UNUSED(section_size);
    UNUSED(beam_ptr);
    printf("%s %s\n", section_name, flags & BEAM_START_FLAG ? "*" : "");
    return accum;
}

static void validate_list_options(const char *filename)
{
    FILE *file = fopen(filename, "r");
    if (!file) {
        char buf[BUF_SIZE];
        snprintf(buf, BUF_SIZE, "%s does not exist", filename);
        usage3(stderr, "PackBeam", buf);
        exit(EXIT_FAILURE);
    } else if (!is_avm_file(file)) {
        char buf[BUF_SIZE];
        snprintf(buf, BUF_SIZE, "Invalid AVM file: %s", filename);
        usage3(stderr, "PackBeam", buf);
        exit(EXIT_FAILURE);
    }
}

static int do_list(int argc, char **argv)
{
    UNUSED(argc);
    validate_list_options(argv[0]);

    MappedFile *mapped_file = mapped_file_open_beam(argv[0]);
    if (IS_NULL_PTR(mapped_file)) {
        char buf[BUF_SIZE];
        snprintf(buf, BUF_SIZE, "Cannot open AVM file %s", argv[0]);
        perror(buf);
        return EXIT_FAILURE;
    }

    int ret = EXIT_SUCCESS;
    if (avmpack_is_valid(mapped_file->mapped, mapped_file->size)) {
        avmpack_fold(NULL, mapped_file->mapped, print_section);
    } else {
        char buf[BUF_SIZE];
        snprintf(buf, BUF_SIZE, "%s is not an AVM file.\n", argv[1]);
        usage3(stderr, "PackBeam", buf);
        ret = EXIT_FAILURE;
    }
    mapped_file_close(mapped_file);

    return ret;
}

static void *uncompress_literals(const uint8_t *litT, int size, size_t *uncompressedSize)
{
    unsigned int required_buf_size = READ_32_ALIGNED(litT + LITT_UNCOMPRESSED_SIZE_OFFSET);

    uint8_t *outBuf = malloc(required_buf_size);
    if (!outBuf) {
        fprintf(stderr, "Cannot allocate temporary buffer (size = %u)", required_buf_size);
        abort();
    }

    z_stream infstream;
    infstream.zalloc = Z_NULL;
    infstream.zfree = Z_NULL;
    infstream.opaque = Z_NULL;
    infstream.avail_in = (uInt) (size - IFF_SECTION_HEADER_SIZE);
    infstream.next_in = (Bytef *) (litT + LITT_HEADER_SIZE);
    infstream.avail_out = (uInt) required_buf_size;
    infstream.next_out = (Bytef *) outBuf;

    int ret = inflateInit(&infstream);
    if (ret != Z_OK) {
        fprintf(stderr, "Failed inflateInit\n");
        abort();
    }
    ret = inflate(&infstream, Z_NO_FLUSH);
    if (ret != Z_OK) {
        fprintf(stderr, "Failed inflate\n");
        abort();
    }
    inflateEnd(&infstream);

    *uncompressedSize = required_buf_size;
    return outBuf;
}

static void pad_and_align(FILE *f)
{
    while ((ftell(f) % 4) != 0) {
        fputc(0, f);
    }
}

static void add_module_header(FILE *f, const char *module_name, uint32_t flags)
{
    uint32_t size_field = 0;
    uint32_t flags_field = ENDIAN_SWAP_32(flags);
    uint32_t reserved = 0;

    assert(fwrite(&size_field, sizeof(uint32_t), 1, f) == 1);
    assert(fwrite(&flags_field, sizeof(uint32_t), 1, f) == 1);
    assert(fwrite(&reserved, sizeof(uint32_t), 1, f) == 1);
    assert(fwrite(module_name, sizeof(char), strlen(module_name) + 1, f) == strlen(module_name) + 1);
    pad_and_align(f);
}
