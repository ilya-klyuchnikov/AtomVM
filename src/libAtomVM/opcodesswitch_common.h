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

typedef union
{
    term **ptr;
    int reg_type;
} dreg_type_t;

#define DECODE_LABEL(label, code_chunk, base_index, off, next_operand_offset)                        \
    {                                                                                                \
        uint8_t first_byte = (code_chunk[(base_index) + (off)]);                                     \
        switch (((first_byte) >> 3) & 0x3) {                                                         \
            case 0:                                                                                  \
            case 2:                                                                                  \
                label = first_byte >> 4;                                                             \
                next_operand_offset += 1;                                                            \
                break;                                                                               \
                                                                                                     \
            case 1:                                                                                  \
                label = ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1];           \
                next_operand_offset += 2;                                                            \
                break;                                                                               \
                                                                                                     \
            default:                                                                                 \
                fprintf(stderr, "Operand not a label: %x, or unsupported encoding\n", (first_byte)); \
                AVM_ABORT();                                                                         \
                break;                                                                               \
        }                                                                                            \
    }

#define DECODE_ATOM(atom, code_chunk, base_index, off, next_operand_offset)                          \
    {                                                                                                \
        uint8_t first_byte = (code_chunk[(base_index) + (off)]);                                     \
        switch (((first_byte) >> 3) & 0x3) {                                                         \
            case 0:                                                                                  \
            case 2:                                                                                  \
                atom = first_byte >> 4;                                                              \
                next_operand_offset += 1;                                                            \
                break;                                                                               \
                                                                                                     \
            case 1:                                                                                  \
                atom = ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1];            \
                next_operand_offset += 2;                                                            \
                break;                                                                               \
                                                                                                     \
            default:                                                                                 \
                fprintf(stderr, "Operand not a label: %x, or unsupported encoding\n", (first_byte)); \
                AVM_ABORT();                                                                         \
                break;                                                                               \
        }                                                                                            \
    }

#define DECODE_INTEGER(label, code_chunk, base_index, off, next_operand_offset)                         \
    {                                                                                                   \
        uint8_t first_byte = (code_chunk[(base_index) + (off)]);                                        \
        switch (((first_byte) >> 3) & 0x3) {                                                            \
            case 0:                                                                                     \
            case 2:                                                                                     \
                label = first_byte >> 4;                                                                \
                next_operand_offset += 1;                                                               \
                break;                                                                                  \
                                                                                                        \
            case 1:                                                                                     \
                label = ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1];              \
                next_operand_offset += 2;                                                               \
                break;                                                                                  \
                                                                                                        \
            default:                                                                                    \
                fprintf(stderr, "Operand not an integer: %x, or unsupported encoding\n", (first_byte)); \
                AVM_ABORT();                                                                            \
                break;                                                                                  \
        }                                                                                               \
    }

#define NEXT_INSTRUCTION(operands_size) \
    i += operands_size
