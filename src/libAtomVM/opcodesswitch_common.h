#pragma once

#define COMPACT_LITERAL 0
#define COMPACT_SMALLINT4 1
#define COMPACT_ATOM 2
#define COMPACT_XREG 3
#define COMPACT_YREG 4
#define COMPACT_EXTENDED 7
#define COMPACT_LARGE_LITERAL 8
#define COMPACT_LARGE_INTEGER 9
#define COMPACT_LARGE_ATOM 10
#define COMPACT_LARGE_YREG 12

#define COMPACT_EXTENDED_LITERAL 0x47

#define COMPACT_LARGE_IMM_MASK 0x18
#define COMPACT_11BITS_VALUE 0x8
#define COMPACT_NBITS_VALUE 0x18

typedef int dreg_t;

static int DECODE_LABEL(const uint8_t *code_chunk, unsigned int base_index, int off, int *next_operand_offset)
{
    uint8_t first_byte = (code_chunk[(base_index) + (off)]);
    switch (((first_byte) >> 3) & 0x3) {
        case 0:
        case 2:
            *next_operand_offset += 1;
            return first_byte >> 4;

        case 1:
            *next_operand_offset += 2;
            return ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1];

        default:
            fprintf(stderr, "Operand not a label: %x, or unsupported encoding\n", (first_byte));
            AVM_ABORT();
    }
}

static int DECODE_ATOM(const uint8_t *code_chunk, unsigned int base_index, int off, int *next_operand_offset)
{
    uint8_t first_byte = (code_chunk[(base_index) + (off)]);
    switch (((first_byte) >> 3) & 0x3) {
        case 0:
        case 2:
            *next_operand_offset += 1;
            return first_byte >> 4;
        case 1:
            *next_operand_offset += 2;
            return ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1];
        default:
            fprintf(stderr, "Operand not a label: %x, or unsupported encoding\n", (first_byte));
            AVM_ABORT();
    }
}

static int DECODE_INTEGER(const uint8_t *code_chunk, unsigned int base_index, int off, int *next_operand_offset)
{
    uint8_t first_byte = (code_chunk[(base_index) + (off)]);
    switch (((first_byte) >> 3) & 0x3) {
        case 0:
        case 2:
            *next_operand_offset += 1;
            return first_byte >> 4;

        case 1:
            *next_operand_offset += 2;
            return ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1];

        default:
            fprintf(stderr, "Operand not an integer: %x, or unsupported encoding\n", (first_byte));
            AVM_ABORT();
    }
}

#define NEXT_INSTRUCTION(operands_size) \
    i += operands_size
