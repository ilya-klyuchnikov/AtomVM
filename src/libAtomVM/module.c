/*
 * This file is part of AtomVM.
 *
 * Copyright 2017 Davide Bettio <davide@uninstall.it>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

#include "module.h"

#include "atom.h"
#include <assert.h>
#include "bif.h"
#include "context.h"
#include "externalterm.h"
#include "iff.h"
#include "nifs.h"
#include "opcodes.h"
#include "opcodesswitch_common.h"
#include "utils.h"

#include <stdio.h>
#include <stdlib.h>

#ifdef WITH_ZLIB
#include <zlib.h>
#endif

#define LITT_UNCOMPRESSED_SIZE_OFFSET 8
#define LITT_HEADER_SIZE 12

#ifdef WITH_ZLIB
    static void *module_uncompress_literals(const uint8_t *litT, int size);
#endif
static struct LiteralEntry *module_build_literals_table(const void *literalsBuf);
static void module_add_label(Module *mod, int index, void *ptr);
static enum ModuleLoadResult module_build_imported_functions_table(Module *this_module, uint8_t *table_data);
static void module_add_label(Module *mod, int index, void *ptr);

static void DECODE_COMPACT_TERM(const uint8_t *code_chunk, unsigned int base_index, int off, int *next_operand_offset)
{
    uint8_t first_byte = (code_chunk[(base_index) + (off)]);
    switch (first_byte & 0xF) {
        case COMPACT_LARGE_LITERAL:
        case COMPACT_LITERAL:
            switch (((first_byte) >> 3) & 0x3) {
                case 0:
                case 2:
                    *next_operand_offset += 1;
                    break;

                case 1:
                    *next_operand_offset += 2;
                    break;

                default:
                    fprintf(stderr, "Operand not literal: %x, or unsupported encoding\n", (first_byte));
                    AVM_ABORT();
                    break;
            }
            break;

        case COMPACT_SMALLINT4:
        case COMPACT_ATOM:
        case COMPACT_XREG:
        case COMPACT_YREG:
            *next_operand_offset += 1;
            break;

        case COMPACT_EXTENDED:
            switch (first_byte) {
                case COMPACT_EXTENDED_LITERAL: {
                    uint8_t ext = (code_chunk[(base_index) + (off) + 1] & 0xF);
                    if (ext == 0) {
                        *next_operand_offset += 2;
                    }else if (ext == 0x8) {
                        *next_operand_offset += 3;
                    } else {
                        AVM_ABORT();
                    }
                    break;
                }
                default:
                    printf("Unexpected %i\n", (int) first_byte);
                    AVM_ABORT();
                    break;
            }
            break;

        case COMPACT_LARGE_INTEGER:
        case COMPACT_LARGE_ATOM:
            switch (first_byte & COMPACT_LARGE_IMM_MASK) {
                case COMPACT_11BITS_VALUE:
                    *next_operand_offset += 2;
                    break;

                case COMPACT_NBITS_VALUE:
                    /* TODO: when first_byte >> 5 is 7, a different encoding is used */
                    *next_operand_offset += (first_byte >> 5) + 3;
                    break;

                default:
                    assert((first_byte & 0x30) != COMPACT_LARGE_INTEGER);
                    break;
            }
            break;

        case COMPACT_LARGE_YREG:
            *next_operand_offset += 2;
            break;

        default:
            fprintf(stderr, "unknown compect term type: %i\n", ((first_byte) & 0xF));
            AVM_ABORT();
            break;
    }
}

static void DECODE_DEST_REGISTER(dreg_t *dreg, int *dreg_type, const uint8_t *code_chunk, unsigned int base_index, int off, int *next_operand_offset)
{
    uint8_t first_byte = code_chunk[(base_index) + (off)];
    uint8_t reg_type = first_byte & 0xF;
    *dreg_type = reg_type;
    switch (reg_type) {
        case COMPACT_XREG:
        case COMPACT_YREG:
            (*dreg) = code_chunk[(base_index) + (off)] >> 4;
            *next_operand_offset += 1;
            break;
        case COMPACT_LARGE_YREG:
            (*dreg) = (((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1]);
            *next_operand_offset += 2;
            break;
        default:
            AVM_ABORT();
    }
}

#pragma GCC diagnostic push
#ifdef __GNUC__
#ifndef __clang__
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#endif

int read_core_chunk(Module *mod)
{
    uint8_t *code = mod->code->code;

    unsigned int i = 0;

    while (1) {

        switch (code[i]) {
            case OP_LABEL: {
                int next_offset = 1;
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                module_add_label(mod, label, &code[i]);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_FUNC_INFO: {
                int next_offset = 1;
                int module_atom = DECODE_ATOM(code, i, next_offset, &next_offset);
                int function_name_atom = DECODE_ATOM(code, i, next_offset, &next_offset);
                int arity = DECODE_INTEGER(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_INT_CALL_END: {
                return i;
            }

            case OP_CALL: {
                int next_offset = 1;
                int arity = DECODE_INTEGER(code, i, next_offset, &next_offset);
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_CALL_LAST: {
                int next_offset = 1;
                int arity = DECODE_INTEGER(code, i, next_offset, &next_offset);
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);
                int n_words = DECODE_INTEGER(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_CALL_ONLY: {
                int next_off = 1;
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_EXT: {
                int next_off = 1;
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                int index = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_EXT_LAST: {
                int next_off = 1;
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                int index = DECODE_INTEGER(code, i, next_off, &next_off);
                int n_words = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_BIF0: {
                int next_off = 1;
                int bif = DECODE_INTEGER(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            // TODO: implement me
            case OP_BIF1: {
                int next_off = 1;
                int fail_label = DECODE_LABEL(code, i, next_off, &next_off);
                int bif = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            // TODO: implement me
            case OP_BIF2: {
                int next_off = 1;
                int fail_label = DECODE_LABEL(code, i, next_off, &next_off);
                int bif = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE: {
                int next_off = 1;
                int stack_need = DECODE_INTEGER(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE_HEAP: {
                int next_off = 1;
                int stack_need = DECODE_ALLOC_LIST(code, i, next_off, &next_off);
                int heap_need = DECODE_ALLOC_LIST(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE_ZERO: {
                int next_off = 1;
                int stack_need = DECODE_INTEGER(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE_HEAP_ZERO: {
                int next_off = 1;
                int stack_need = DECODE_ALLOC_LIST(code, i, next_off, &next_off);
                int heap_need = DECODE_ALLOC_LIST(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TEST_HEAP: {
                int next_offset = 1;
                uint8_t first_byte = (code[(i) + (next_offset)]);
                unsigned int heap_need = DECODE_ALLOC_LIST(code, i, next_offset, &next_offset);
                int live_registers = DECODE_INTEGER(code, i, next_offset, &next_offset);
                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_KILL: {
                int next_offset = 1;
                int target = DECODE_INTEGER(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_DEALLOCATE: {
                int next_off = 1;
                int n_words = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RETURN: {
                NEXT_INSTRUCTION(1);
                break;
            }

            // TODO: implement send/0
            case OP_SEND: {
                NEXT_INSTRUCTION(1);
                break;
            }

            case OP_REMOVE_MESSAGE: {
                NEXT_INSTRUCTION(1);
                break;
            }

            case OP_TIMEOUT: {
                NEXT_INSTRUCTION(1);
                break;
            }

            case OP_LOOP_REC: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_LOOP_REC_END: {
                int next_offset = 1;
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            // TODO: implement wait/1
            case OP_WAIT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            // TODO: implement wait_timeout/2
            case OP_WAIT_TIMEOUT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_LT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_GE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_EQUAL: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NOT_EQUAL: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_EQ_EXACT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_NOT_EQ_EXACT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_INTEGER: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_FLOAT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NUMBER: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_BINARY: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_LIST: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NONEMPTY_LIST: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NIL: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_ATOM: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_PID: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_REFERENCE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_PORT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_TUPLE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label);
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_TEST_ARITY: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_SELECT_VAL: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int default_label = DECODE_LABEL(code, i, next_off, &next_off);
                next_off++; // skip extended list tag
                int size = DECODE_INTEGER(code, i, next_off, &next_off);

                for (int j = 0; j < size / 2; j++) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                    int jmp_label = DECODE_LABEL(code, i, next_off, &next_off);
                }

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_SELECT_TUPLE_ARITY: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int default_label = DECODE_LABEL(code, i, next_off, &next_off);
                next_off++; // skip extended list tag
                int size = DECODE_INTEGER(code, i, next_off, &next_off);

                for (int j = 0; j < size / 2; j++) {
                    int cmp_value = DECODE_INTEGER(code, i, next_off, &next_off);
                    int jmp_label = DECODE_LABEL(code, i, next_off, &next_off);
                }

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_JUMP: {
                int next_offset = 1;
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_MOVE: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GET_LIST: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t head_dreg;
                int head_dreg_type;
                DECODE_DEST_REGISTER(&head_dreg, &head_dreg_type, code, i, next_off, &next_off);
                dreg_t tail_dreg;
                int tail_dreg_type;
                DECODE_DEST_REGISTER(&tail_dreg, &tail_dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GET_TUPLE_ELEMENT: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int element = DECODE_INTEGER(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_SET_TUPLE_ELEMENT: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int position = DECODE_INTEGER(code, i, next_off, &next_off);

                UNUSED(position);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_PUT_LIST: {

                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_PUT_TUPLE: {
                int next_off = 1;
                int size = DECODE_INTEGER(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                for (int j = 0; j < size; j++) {
                    if (code[i + next_off] != OP_PUT) {
                        fprintf(stderr, "Expected put, got opcode: %i\n", code[i + next_off]);
                        AVM_ABORT();
                    }
                    next_off++;
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                }

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BADMATCH: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IF_END: {
                NEXT_INSTRUCTION(1);

                break;
            }

            case OP_CASE_END: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_FUN: {
                int next_off = 1;
                unsigned int args_count = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_FUNCTION: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_EXT_ONLY: {
                int next_off = 1;
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                int index = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_MAKE_FUN2: {
                int next_off = 1;
                int fun_index = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY_END: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY_CASE: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY_CASE_END: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RAISE: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_CATCH: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_CATCH_END: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_ADD: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_INIT2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t words = DECODE_INTEGER(code, i, next_off, &next_off);
                UNUSED(words);
                avm_int_t regs = DECODE_INTEGER(code, i, next_off, &next_off);
                UNUSED(regs);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_INIT_BITS: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int words = DECODE_INTEGER(code, i, next_off, &next_off);
                int regs = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_APPEND: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_PUT_INTEGER: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_PUT_BINARY: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_PUT_STRING: {
                int next_off = 1;
                avm_int_t size = DECODE_INTEGER(code, i, next_off, &next_off);
                avm_int_t offset = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_START_MATCH2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_START_MATCH3: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_POSITION: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_TAIL: {
                int next_off = 1;
                term src;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_SET_POSITION: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_MATCH_STRING: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t bits = DECODE_INTEGER(code, i, next_off, &next_off);
                avm_int_t offset = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_BS_SAVE2: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_RESTORE2: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_SKIP_BITS2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_TEST_UNIT: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_TEST_TAIL2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t bits = DECODE_INTEGER(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_INTEGER2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_BINARY2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                int src_offset = next_off;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                avm_int_t unit = DECODE_INTEGER(code, i, next_off, &next_off);
                term flags;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_CONTEXT_TO_BINARY: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_APPLY: {
                int next_off = 1;
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_APPLY_LAST: {
                int next_off = 1;
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                int n_words = DECODE_INTEGER(code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_BOOLEAN: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_FUNCTION2: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                unsigned int arity = DECODE_INTEGER(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_GC_BIF1: {
                int next_off = 1;
                int f_label = DECODE_LABEL(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);
                int bif = DECODE_INTEGER(code, i, next_off, &next_off); // s?
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                UNUSED(f_label)
                UNUSED(live)
                UNUSED(bif)
                UNUSED(dreg)

                UNUSED(f_label)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GC_BIF2: {
                int next_off = 1;
                int f_label = DECODE_LABEL(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);
                int bif = DECODE_INTEGER(code, i, next_off, &next_off); // s?
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                UNUSED(f_label)
                UNUSED(live)
                UNUSED(bif)
                UNUSED(dreg)

                UNUSED(f_label)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            // TODO: stub, always false
            case OP_IS_BITSTR: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_GC_BIF3: {
                int next_off = 1;
                int f_label = DECODE_LABEL(code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);
                int bif = DECODE_INTEGER(code, i, next_off, &next_off); // s?
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);

                UNUSED(f_label)
                UNUSED(live)
                UNUSED(bif)
                UNUSED(dreg)

                UNUSED(f_label)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRIM: {
                int next_offset = 1;
                int n_words = DECODE_INTEGER(code, i, next_offset, &next_offset);
                int n_remaining = DECODE_INTEGER(code, i, next_offset, &next_offset);

                UNUSED(n_remaining)

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            // TODO: stub, implement recv_mark/1
            // it looks like it can be safely left unimplemented
            case OP_RECV_MARK: {
                int next_offset = 1;
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            // TODO: stub, implement recv_set/1
            // it looks like it can be safely left unimplemented
            case OP_RECV_SET: {
                int next_offset = 1;
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_LINE: {
                int next_offset = 1;
                int line_number = DECODE_INTEGER(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_PUT_MAP_ASSOC: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                int src_offset = next_off;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len = DECODE_INTEGER(code, i, next_off, &next_off);
                int list_off = next_off;
                int num_elements = list_len / 2;
                //
                // Count how many of the entries in list(...) are not already in src
                //
                unsigned new_entries = 0;
                for (int j = 0; j < num_elements; ++j) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                }
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_PUT_MAP_EXACT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                int live = DECODE_INTEGER(code, i, next_off, &next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len = DECODE_INTEGER(code, i, next_off, &next_off);
                int list_off = next_off;
                int num_elements = list_len / 2;
                //
                // Make sure every key from list is in src
                //
                for (int j = 0; j < num_elements; ++j) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                }
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_MAP: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_HAS_MAP_FIELDS: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len = DECODE_INTEGER(code, i, next_off, &next_off);
                int fail = 0;
                for (int j = 0; j < list_len && !fail; ++j) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                }
                if (!fail) {
                    NEXT_INSTRUCTION(next_off);
                }
                break;
            }

            case OP_GET_MAP_ELEMENTS: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len = DECODE_INTEGER(code, i, next_off, &next_off);
                int num_elements = list_len / 2;
                int fail = 0;
                for (int j = 0; j < num_elements && !fail; ++j) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                    dreg_t dreg;
                    int dreg_type;
                    DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                }
                if (!fail) {
                    NEXT_INSTRUCTION(next_off);
                }
                break;
            }

            case OP_IS_TAGGED_TUPLE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                int arity = DECODE_INTEGER(code, i, next_off, &next_off);
                int tag_atom_id = DECODE_ATOM(code, i, next_off, &next_off);

                UNUSED(label)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_GET_HD: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t head_dreg;
                int head_dreg_type;
                DECODE_DEST_REGISTER(&head_dreg, &head_dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GET_TL: {
                int next_off = 1;
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t tail_dreg;
                int tail_dreg_type;
                DECODE_DEST_REGISTER(&tail_dreg, &tail_dreg_type, code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_PUT_TUPLE2: {
                int next_off = 1;
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                next_off++; // skip extended list tag
                int size = DECODE_INTEGER(code, i, next_off, &next_off);

                UNUSED(dreg);

                for (int j = 0; j < size; j++) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                }

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_SWAP: {
                int next_off = 1;
                dreg_t reg_a;
                int reg_a_type;
                DECODE_DEST_REGISTER(&reg_a, &reg_a_type, code, i, next_off, &next_off);
                dreg_t reg_b;
                int reg_b_type;
                DECODE_DEST_REGISTER(&reg_b, &reg_b_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_START_MATCH4: {
                int next_off = 1;
                // fail since OTP 23 might be either 'no_fail', 'resume' or a fail label
                // we are ignoring this right now, but we might use it for future optimizations.
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                dreg_t dreg;
                int dreg_type;
                DECODE_DEST_REGISTER(&dreg, &dreg_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_INIT_YREGS: {
                int next_off = 1;
                next_off++; // skip extended list tag
                int size = DECODE_INTEGER(code, i, next_off, &next_off);
                for (int j = 0; j < size; j++) {
                    DECODE_INTEGER(code, i, next_off, &next_off);
                }
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RECV_MARKER_BIND: {
                int next_off = 1;
                dreg_t reg_a;
                int reg_a_type;
                DECODE_DEST_REGISTER(&reg_a, &reg_a_type, code, i, next_off, &next_off);
                dreg_t reg_b;
                int reg_b_type;
                DECODE_DEST_REGISTER(&reg_b, &reg_b_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RECV_MARKER_CLEAR: {
                int next_off = 1;
                dreg_t reg_a;
                int reg_a_type;
                DECODE_DEST_REGISTER(&reg_a, &reg_a_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RECV_MARKER_RESERVE: {
                int next_off = 1;
                dreg_t reg_a;
                int reg_a_type;
                DECODE_DEST_REGISTER(&reg_a, &reg_a_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RECV_MARKER_USE: {
                int next_off = 1;
                dreg_t reg_a;
                int reg_a_type;
                DECODE_DEST_REGISTER(&reg_a, &reg_a_type, code, i, next_off, &next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_MAKE_FUN3: {
                int next_off = 1;
                int fun_index = DECODE_LABEL(code, i, next_off, &next_off);
                dreg_t reg_a;
                int reg_a_type;
                DECODE_DEST_REGISTER(&reg_a, &reg_a_type, code, i, next_off, &next_off);

                next_off++; // skip extended list tag
                int size = DECODE_INTEGER(code, i, next_off, &next_off);

                for (int j = 0; j < size; j++) {
                    DECODE_COMPACT_TERM(code, i, next_off, &next_off);
                }
                NEXT_INSTRUCTION(next_off);
                break;
            }

            default:
                printf("Undecoded opcode: %i\n", code[i]);
                AVM_ABORT();
                return 1;
        }
    }
}

#pragma GCC diagnostic pop

static enum ModuleLoadResult module_populate_atoms_table(Module *this_module, uint8_t *table_data)
{
    int atoms_count = READ_32_ALIGNED(table_data + 8);
    const char *current_atom = (const char *) table_data + 12;

    this_module->local_atoms_to_global_table = calloc(atoms_count + 1, sizeof(int));
    if (IS_NULL_PTR(this_module->local_atoms_to_global_table)) {
        fprintf(stderr, "Cannot allocate memory while loading module (line: %i).\n", __LINE__);
        return MODULE_ERROR_FAILED_ALLOCATION;
    }

    const char *atom = NULL;
    for (int i = 1; i <= atoms_count; i++) {
        int atom_len = *current_atom;
        atom = current_atom;

        int global_atom_id = globalcontext_insert_atom(this_module->global, (AtomString) atom);
        if (UNLIKELY(global_atom_id < 0)) {
            fprintf(stderr, "Cannot allocate memory while loading module (line: %i).\n", __LINE__);
            return MODULE_ERROR_FAILED_ALLOCATION;
        }

        this_module->local_atoms_to_global_table[i] = global_atom_id;

        current_atom += atom_len + 1;
    }

    return MODULE_LOAD_OK;
}

static enum ModuleLoadResult module_build_imported_functions_table(Module *this_module, uint8_t *table_data)
{
    int functions_count = READ_32_ALIGNED(table_data + 8);

    this_module->imported_funcs = calloc(functions_count, sizeof(void *));
    if (IS_NULL_PTR(this_module->imported_funcs)) {
        fprintf(stderr, "Cannot allocate memory while loading module (line: %i).\n", __LINE__);
        return MODULE_ERROR_FAILED_ALLOCATION;
    }

    for (int i = 0; i < functions_count; i++) {
        int local_module_atom_index = READ_32_ALIGNED(table_data + i * 12 + 12);
        int local_function_atom_index = READ_32_ALIGNED(table_data + i * 12 + 4 + 12);
        AtomString module_atom = module_get_atom_string_by_id(this_module, local_module_atom_index);
        AtomString function_atom = module_get_atom_string_by_id(this_module, local_function_atom_index);
        uint32_t arity = READ_32_ALIGNED(table_data + i * 12 + 8 + 12);

        BifImpl bif_handler = bif_registry_get_handler(module_atom, function_atom, arity);

        if (bif_handler) {
            this_module->imported_funcs[i].bif = bif_handler;
        } else {
            this_module->imported_funcs[i].func = &nifs_get(module_atom, function_atom, arity)->base;
        }

        if (!this_module->imported_funcs[i].func) {
            struct UnresolvedFunctionCall *unresolved = malloc(sizeof(struct UnresolvedFunctionCall));
            if (IS_NULL_PTR(unresolved)) {
                fprintf(stderr, "Cannot allocate memory while loading module (line: %i).\n", __LINE__);
                return MODULE_ERROR_FAILED_ALLOCATION;
            }
            unresolved->base.type = UnresolvedFunctionCall;
            unresolved->module_atom_index = this_module->local_atoms_to_global_table[local_module_atom_index];
            unresolved->function_atom_index = this_module->local_atoms_to_global_table[local_function_atom_index];
            unresolved->arity = arity;

            this_module->imported_funcs[i].func = &unresolved->base;
        }
    }

    return MODULE_LOAD_OK;
}

uint32_t module_search_exported_function(Module *this_module, AtomString func_name, int func_arity)
{
    const uint8_t *table_data = (const uint8_t *) this_module->export_table;
    int functions_count = READ_32_ALIGNED(table_data + 8);

    for (int i = 0; i < functions_count; i++) {
        AtomString function_atom = module_get_atom_string_by_id(this_module, READ_32_ALIGNED(table_data + i * 12 + 12));
        int32_t arity = READ_32_ALIGNED(table_data + i * 12 + 4 + 12);
        if ((func_arity == arity) && atom_are_equals(func_name, function_atom)) {
            uint32_t label = READ_32_ALIGNED(table_data + i * 12 + 8 + 12);
            return label;
        }
    }

    return 0;
}

static void module_add_label(Module *mod, int index, void *ptr)
{
    mod->labels[index] = ptr;
}

Module *module_new_from_iff_binary(GlobalContext *global, const void *iff_binary, unsigned long size)
{
    uint8_t *beam_file = (void *) iff_binary;

    unsigned long offsets[MAX_OFFS];
    unsigned long sizes[MAX_SIZES];
    scan_iff(beam_file, size, offsets, sizes);

    Module *mod = malloc(sizeof(Module));
    if (IS_NULL_PTR(mod)) {
        fprintf(stderr, "Error: Failed to allocate memory: %s:%i.\n", __FILE__, __LINE__);
        return NULL;
    }
    memset(mod, 0, sizeof(Module));

    mod->module_index = -1;
    mod->global = global;

    if (UNLIKELY(module_populate_atoms_table(mod, beam_file + offsets[AT8U]) != MODULE_LOAD_OK)) {
        fprintf(stderr, "Error: Failed to populate atoms table: %s:%i.\n", __FILE__, __LINE__);
        module_destroy(mod);
        return NULL;
    }

    if (UNLIKELY(module_build_imported_functions_table(mod, beam_file + offsets[IMPT]) != MODULE_LOAD_OK)) {
        fprintf(stderr, "Error: Failed to build imported functions table: %s:%i.\n", __FILE__, __LINE__);
        module_destroy(mod);
        return NULL;
    }

    mod->code = (CodeChunk *) (beam_file + offsets[CODE]);
    mod->export_table = beam_file + offsets[EXPT];
    mod->atom_table = beam_file + offsets[AT8U];
    mod->fun_table = beam_file + offsets[FUNT];
    mod->str_table = beam_file + offsets[STRT];
    mod->str_table_len = sizes[STRT];
    mod->labels = calloc(ENDIAN_SWAP_32(mod->code->labels), sizeof(void *));
    if (IS_NULL_PTR(mod->labels)) {
        fprintf(stderr, "Error: Null module labels: %s:%i.\n", __FILE__, __LINE__);
        module_destroy(mod);
        return NULL;
    }

    if (offsets[LITT]) {
        #ifdef WITH_ZLIB
            mod->literals_data = module_uncompress_literals(beam_file + offsets[LITT], sizes[LITT]);
            if (IS_NULL_PTR(mod->literals_data)) {
                module_destroy(mod);
                return NULL;
            }
        #else
            fprintf(stderr, "Error: zlib required to uncompress literals.\n");
            module_destroy(mod);
            return NULL;
        #endif

        mod->literals_table = module_build_literals_table(mod->literals_data);
        mod->free_literals_data = 1;

    } else if (offsets[LITU]) {
        mod->literals_data = beam_file + offsets[LITU] + IFF_SECTION_HEADER_SIZE;
        mod->literals_table = module_build_literals_table(mod->literals_data);
        mod->free_literals_data = 0;

    } else {
        mod->literals_data = NULL;
        mod->literals_table = NULL;
        mod->free_literals_data = 0;
    }

    mod->end_instruction_ii = read_core_chunk(mod);

    return mod;
}

COLD_FUNC void module_destroy(Module *module)
{
    free(module->labels);
    free(module->imported_funcs);
    free(module->literals_table);
    if (module->free_literals_data) {
        free(module->literals_data);
    }
    free(module);
}

#ifdef WITH_ZLIB
static void *module_uncompress_literals(const uint8_t *litT, int size)
{
    unsigned int required_buf_size = READ_32_ALIGNED(litT + LITT_UNCOMPRESSED_SIZE_OFFSET);

    uint8_t *outBuf = malloc(required_buf_size);
    if (IS_NULL_PTR(outBuf)) {
        fprintf(stderr, "Failed to allocate memory: %s:%i.\n", __FILE__, __LINE__);
        return NULL;
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
        return NULL;
    }
    ret = inflate(&infstream, Z_NO_FLUSH);
    if (ret != Z_OK) {
        fprintf(stderr, "Failed inflate\n");
        return NULL;
    }
    inflateEnd(&infstream);

    return outBuf;
}
#endif

static struct LiteralEntry *module_build_literals_table(const void *literalsBuf)
{
    uint32_t terms_count = READ_32_ALIGNED(literalsBuf);

    const uint8_t *pos = (const uint8_t *) literalsBuf + sizeof(uint32_t);

    struct LiteralEntry *literals_table = calloc(terms_count, sizeof(struct LiteralEntry));
    if (IS_NULL_PTR(literals_table)) {
        fprintf(stderr, "Failed to allocate memory: %s:%i.\n", __FILE__, __LINE__);
        return NULL;
    }
    for (uint32_t i = 0; i < terms_count; i++) {
        uint32_t term_size = READ_32_UNALIGNED(pos);
        literals_table[i].size = term_size;
        literals_table[i].data = pos + sizeof(uint32_t);

        pos += term_size + sizeof(uint32_t);
    }

    return literals_table;
}

term module_load_literal(Module *mod, int index, Context *ctx)
{
    term t = externalterm_to_term(mod->literals_table[index].data, mod->literals_table[index].size, ctx, 1);
    if (term_is_invalid_term(t)) {
        fprintf(stderr, "Invalid term reading literals_table[%i] from module\n", index);
        AVM_ABORT();
    }
    return t;
}

const struct ExportedFunction *module_resolve_function(Module *mod, int import_table_index)
{
    struct ExportedFunction *func = (struct ExportedFunction *) mod->imported_funcs[import_table_index].func;
    struct UnresolvedFunctionCall *unresolved = EXPORTED_FUNCTION_TO_UNRESOLVED_FUNCTION_CALL(func);

    AtomString module_name_atom = (AtomString) valueshashtable_get_value(mod->global->atoms_ids_table, unresolved->module_atom_index, (unsigned long) NULL);
    AtomString function_name_atom = (AtomString) valueshashtable_get_value(mod->global->atoms_ids_table, unresolved->function_atom_index, (unsigned long) NULL);
    int arity = unresolved->arity;

    Module *found_module = globalcontext_get_module(mod->global, module_name_atom);

    if (LIKELY(found_module != NULL)) {
        int exported_label = module_search_exported_function(found_module, function_name_atom, arity);
        if (exported_label == 0) {
            char buf[256];
            atom_write_mfa(buf, 256, module_name_atom, function_name_atom, arity);
            fprintf(stderr, "Warning: function %s cannot be resolved.\n", buf);
            return NULL;
        }
        struct ModuleFunction *mfunc = malloc(sizeof(struct ModuleFunction));
        if (IS_NULL_PTR(mfunc)) {
            fprintf(stderr, "Failed to allocate memory: %s:%i.\n", __FILE__, __LINE__);
            return NULL;
        }
        mfunc->base.type = ModuleFunction;
        mfunc->target = found_module;
        mfunc->label = exported_label;

        free(unresolved);
        mod->imported_funcs[import_table_index].func = &mfunc->base;
        return &mfunc->base;
    } else {
        char buf[256];
        atom_string_to_c(module_name_atom, buf, 256);
        fprintf(stderr, "Warning: module %s cannot be resolved.\n", buf);
        return NULL;
    }
}
