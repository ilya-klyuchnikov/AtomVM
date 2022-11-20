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

#include <assert.h>
#include <string.h>

#include "bif.h"
#include "defaultatoms.h"
#include "exportedfunction.h"
#include "nifs.h"
#include "opcodes.h"
#include "opcodesswitch_common.h"
#include "scheduler.h"
#include "utils.h"

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
                int module_atom;
                DECODE_ATOM(module_atom, code, i, next_offset, next_offset)
                int function_name_atom;
                DECODE_ATOM(function_name_atom, code, i, next_offset, next_offset)
                int arity;
                DECODE_INTEGER(arity, code, i, next_offset, next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_INT_CALL_END: {
                return i;
            }

            case OP_CALL: {
                int next_offset = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_offset, next_offset);
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_CALL_LAST: {
                int next_offset = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_offset, next_offset);
                int label = DECODE_LABEL(code, i, next_offset, &next_offset);
                int n_words;
                DECODE_INTEGER(n_words, code, i, next_offset, next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_CALL_ONLY: {
                int next_off = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off);
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_EXT: {
                int next_off = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off);
                int index;
                DECODE_INTEGER(index, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_EXT_LAST: {
                int next_off = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off);
                int index;
                DECODE_INTEGER(index, code, i, next_off, next_off);
                int n_words;
                DECODE_INTEGER(n_words, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_BIF0: {
                int next_off = 1;
                int bif;
                DECODE_INTEGER(bif, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            // TODO: implement me
            case OP_BIF1: {
                int next_off = 1;
                int fail_label = DECODE_LABEL(code, i, next_off, &next_off);
                int bif;
                DECODE_INTEGER(bif, code, i, next_off, next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(arg1);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            // TODO: implement me
            case OP_BIF2: {
                int next_off = 1;
                int fail_label = DECODE_LABEL(code, i, next_off, &next_off);
                int bif;
                DECODE_INTEGER(bif, code, i, next_off, next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(arg1);
                UNUSED(arg2);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE: {
                int next_off = 1;
                int stack_need;
                DECODE_INTEGER(stack_need, code, i, next_off, next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE_HEAP: {
                int next_off = 1;
                int stack_need;
                DECODE_INTEGER(stack_need, code, i, next_off, next_off);
                int heap_need;
                DECODE_INTEGER(heap_need, code, i, next_off, next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE_ZERO: {
                int next_off = 1;
                int stack_need;
                DECODE_INTEGER(stack_need, code, i, next_off, next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_ALLOCATE_HEAP_ZERO: {
                int next_off = 1;
                int stack_need;
                DECODE_INTEGER(stack_need, code, i, next_off, next_off);
                int heap_need;
                DECODE_INTEGER(heap_need, code, i, next_off, next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TEST_HEAP: {
                int next_offset = 1;
                unsigned int heap_need;
                DECODE_INTEGER(heap_need, code, i, next_offset, next_offset);
                int live_registers;
                DECODE_INTEGER(live_registers, code, i, next_offset, next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_KILL: {
                int next_offset = 1;
                int target;
                DECODE_INTEGER(target, code, i, next_offset, next_offset);

                NEXT_INSTRUCTION(next_offset);

                break;
            }

            case OP_DEALLOCATE: {
                int next_off = 1;
                int n_words;
                DECODE_INTEGER(n_words, code, i, next_off, next_off);

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
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

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
                term timeout;
                DECODE_COMPACT_TERM(timeout, code, i, next_off, next_off)

                UNUSED(timeout)

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_LT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);

                UNUSED(arg1)
                UNUSED(arg2)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_GE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);

                UNUSED(arg1)
                UNUSED(arg2)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_EQUAL: {
                term arg1;
                term arg2;
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off)

                UNUSED(arg1)
                UNUSED(arg2)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NOT_EQUAL: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off)

                UNUSED(arg1)
                UNUSED(arg2)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_EQ_EXACT: {
                term arg1;
                term arg2;
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off)

                UNUSED(arg1)
                UNUSED(arg2)
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_NOT_EQ_EXACT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off)

                UNUSED(arg1)
                UNUSED(arg2)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_INTEGER: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_FLOAT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NUMBER: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_BINARY: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_LIST: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NONEMPTY_LIST: {
                term arg1;
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_NIL: {
                term arg1;
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_ATOM: {
                term arg1;
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_PID: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_REFERENCE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_PORT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_TUPLE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_TEST_ARITY: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off);
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off);

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_SELECT_VAL: {
                int next_off = 1;
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off)
                int default_label = DECODE_LABEL(code, i, next_off, &next_off);
                next_off++; // skip extended list tag
                int size;
                DECODE_INTEGER(size, code, i, next_off, next_off)

                UNUSED(src_value);

                for (int j = 0; j < size / 2; j++) {
                    term cmp_value;
                    DECODE_COMPACT_TERM(cmp_value, code, i, next_off, next_off)
                    int jmp_label = DECODE_LABEL(code, i, next_off, &next_off);

                    UNUSED(cmp_value);
                }

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_SELECT_TUPLE_ARITY: {
                int next_off = 1;
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off)
                int default_label = DECODE_LABEL(code, i, next_off, &next_off);
                next_off++; // skip extended list tag
                int size;
                DECODE_INTEGER(size, code, i, next_off, next_off)

                UNUSED(src_value);

                for (int j = 0; j < size / 2; j++) {
                    int cmp_value;
                    DECODE_INTEGER(cmp_value, code, i, next_off, next_off)
                    int jmp_label = DECODE_LABEL(code, i, next_off, &next_off);

                    UNUSED(cmp_value);
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
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(src_value)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GET_LIST: {
                int next_off = 1;
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off)
                dreg_t head_dreg;
                dreg_type_t head_dreg_type;
                DECODE_DEST_REGISTER(head_dreg, head_dreg_type, code, i, next_off, next_off);
                dreg_t tail_dreg;
                dreg_type_t tail_dreg_type;
                DECODE_DEST_REGISTER(tail_dreg, tail_dreg_type, code, i, next_off, next_off);

                UNUSED(src_value)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GET_TUPLE_ELEMENT: {
                int next_off = 1;
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off);
                int element;
                DECODE_INTEGER(element, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(src_value)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_SET_TUPLE_ELEMENT: {
                int next_off = 1;
                term new_element;
                DECODE_COMPACT_TERM(new_element, code, i, next_off, next_off);
                term tuple;
                DECODE_COMPACT_TERM(tuple, code, i, next_off, next_off);
                int position;
                DECODE_INTEGER(position, code, i, next_off, next_off);

                UNUSED(tuple);
                UNUSED(position);
                UNUSED(new_element);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_PUT_LIST: {

                int next_off = 1;
                term head;
                DECODE_COMPACT_TERM(head, code, i, next_off, next_off);
                term tail;
                DECODE_COMPACT_TERM(tail, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(head);
                UNUSED(tail);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_PUT_TUPLE: {
                int next_off = 1;
                int size;
                DECODE_INTEGER(size, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                for (int j = 0; j < size; j++) {
                    if (code[i + next_off] != OP_PUT) {
                        fprintf(stderr, "Expected put, got opcode: %i\n", code[i + next_off]);
                        AVM_ABORT();
                    }
                    next_off++;
                    term put_value;
                    DECODE_COMPACT_TERM(put_value, code, i, next_off, next_off);
                    UNUSED(put_value);
                }

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BADMATCH: {
                int next_off = 1;
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IF_END: {
                NEXT_INSTRUCTION(1);

                break;
            }

            case OP_CASE_END: {
                int next_off = 1;
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_FUN: {
                int next_off = 1;
                unsigned int args_count;
                DECODE_INTEGER(args_count, code, i, next_off, next_off)

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_FUNCTION: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_CALL_EXT_ONLY: {
                int next_off = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off);
                int index;
                DECODE_INTEGER(index, code, i, next_off, next_off);

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
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY_END: {
                int next_off = 1;
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY_CASE: {
                int next_off = 1;
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRY_CASE_END: {
                int next_off = 1;
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_RAISE: {
                int next_off = 1;
                term stacktrace;
                DECODE_COMPACT_TERM(stacktrace, code, i, next_off, next_off);
                UNUSED(stacktrace);
                term exc_value;
                DECODE_COMPACT_TERM(exc_value, code, i, next_off, next_off);

                UNUSED(exc_value);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_CATCH: {
                int next_off = 1;
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                int label = DECODE_LABEL(code, i, next_off, &next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_CATCH_END: {
                int next_off = 1;
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_ADD: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src1;
                DECODE_COMPACT_TERM(src1, code, i, next_off, next_off);
                term src2;
                DECODE_COMPACT_TERM(src2, code, i, next_off, next_off);
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_INIT2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off)
                avm_int_t words;
                UNUSED(words);
                DECODE_INTEGER(words, code, i, next_off, next_off)
                avm_int_t regs;
                UNUSED(regs);
                DECODE_INTEGER(regs, code, i, next_off, next_off)
                term flags;
                UNUSED(flags);
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_INIT_BITS: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off)
                int words;
                DECODE_INTEGER(words, code, i, next_off, next_off)
                int regs;
                DECODE_INTEGER(regs, code, i, next_off, next_off)
                term flags;
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_APPEND: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off)
                term extra;
                UNUSED(extra);
                DECODE_COMPACT_TERM(extra, code, i, next_off, next_off)
                term live;
                UNUSED(live);
                DECODE_COMPACT_TERM(live, code, i, next_off, next_off)
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);
                term src;
                int src_off = next_off;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off)
                term flags;
                UNUSED(flags);
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_PUT_INTEGER: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off)
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);
                term flags;
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_PUT_BINARY: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                int size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off)
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);
                term flags;
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_PUT_STRING: {
                int next_off = 1;
                avm_int_t size;
                DECODE_INTEGER(size, code, i, next_off, next_off);
                avm_int_t offset;
                DECODE_INTEGER(offset, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_START_MATCH2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);
                term slots_term;
                DECODE_COMPACT_TERM(slots_term, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_START_MATCH3: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term live;
                DECODE_COMPACT_TERM(live, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_POSITION: {
                int next_off = 1;
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                term live;
                DECODE_COMPACT_TERM(live, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_TAIL: {
                int next_off = 1;
                term src;
                int src_off = next_off;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                term live;
                DECODE_COMPACT_TERM(live, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_SET_POSITION: {
                int next_off = 1;
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term pos;
                DECODE_COMPACT_TERM(pos, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_MATCH_STRING: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                avm_int_t bits;
                DECODE_INTEGER(bits, code, i, next_off, next_off);
                avm_int_t offset;
                DECODE_INTEGER(offset, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_BS_SAVE2: {
                int next_off = 1;
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term index = 0;
                DECODE_COMPACT_TERM(index, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_RESTORE2: {
                int next_off = 1;
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term index = 0;
                DECODE_COMPACT_TERM(index, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_SKIP_BITS2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off);
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);
                term flags;
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_TEST_UNIT: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_TEST_TAIL2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                avm_int_t bits;
                DECODE_INTEGER(bits, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_INTEGER2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off);
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);
                term flags;
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_GET_BINARY2: {
                int next_off = 1;
                int fail = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                int src_offset = next_off;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);
                term size;
                DECODE_COMPACT_TERM(size, code, i, next_off, next_off);
                avm_int_t unit;
                DECODE_INTEGER(unit, code, i, next_off, next_off);
                term flags;
                DECODE_COMPACT_TERM(flags, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_CONTEXT_TO_BINARY: {
                int next_off = 1;
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_APPLY: {
                int next_off = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off)
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_APPLY_LAST: {
                int next_off = 1;
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off)
                int n_words;
                DECODE_INTEGER(n_words, code, i, next_off, next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_IS_BOOLEAN: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_FUNCTION2: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                unsigned int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_GC_BIF1: {
                int next_off = 1;
                int f_label = DECODE_LABEL(code, i, next_off, &next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);
                int bif;
                DECODE_INTEGER(bif, code, i, next_off, next_off); // s?
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(f_label)
                UNUSED(live)
                UNUSED(bif)
                UNUSED(arg1)
                UNUSED(dreg)

                UNUSED(f_label)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GC_BIF2: {
                int next_off = 1;
                int f_label = DECODE_LABEL(code, i, next_off, &next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);
                int bif;
                DECODE_INTEGER(bif, code, i, next_off, next_off); // s?
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(f_label)
                UNUSED(live)
                UNUSED(bif)
                UNUSED(arg1)
                UNUSED(arg2)
                UNUSED(dreg)

                UNUSED(f_label)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            // TODO: stub, always false
            case OP_IS_BITSTR: {
                term arg1;
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_GC_BIF3: {
                int next_off = 1;
                int f_label = DECODE_LABEL(code, i, next_off, &next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);
                int bif;
                DECODE_INTEGER(bif, code, i, next_off, next_off); // s?
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off);
                term arg2;
                DECODE_COMPACT_TERM(arg2, code, i, next_off, next_off);
                term arg3;
                DECODE_COMPACT_TERM(arg3, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);

                UNUSED(f_label)
                UNUSED(live)
                UNUSED(bif)
                UNUSED(arg1)
                UNUSED(arg2)
                UNUSED(arg3)
                UNUSED(dreg)

                UNUSED(f_label)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_TRIM: {
                int next_offset = 1;
                int n_words;
                DECODE_INTEGER(n_words, code, i, next_offset, next_offset);
                int n_remaining;
                DECODE_INTEGER(n_remaining, code, i, next_offset, next_offset);

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
                int line_number;
                DECODE_INTEGER(line_number, code, i, next_offset, next_offset);

                NEXT_INSTRUCTION(next_offset);
                break;
            }

            case OP_PUT_MAP_ASSOC: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                int src_offset = next_off;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len;
                DECODE_INTEGER(list_len, code, i, next_off, next_off);
                int list_off = next_off;
                int num_elements = list_len / 2;
                //
                // Count how many of the entries in list(...) are not already in src
                //
                unsigned new_entries = 0;
                for (int j = 0; j < num_elements; ++j) {
                    term key, value;
                    DECODE_COMPACT_TERM(key, code, i, next_off, next_off);
                    DECODE_COMPACT_TERM(value, code, i, next_off, next_off);
                }
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_PUT_MAP_EXACT: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                int src_offset = next_off;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                int live;
                DECODE_INTEGER(live, code, i, next_off, next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len;
                DECODE_INTEGER(list_len, code, i, next_off, next_off);
                int list_off = next_off;
                int num_elements = list_len / 2;
                //
                // Make sure every key from list is in src
                //
                for (int j = 0; j < num_elements; ++j) {
                    term key, value;
                    DECODE_COMPACT_TERM(key, code, i, next_off, next_off);
                    DECODE_COMPACT_TERM(value, code, i, next_off, next_off);
                }
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_IS_MAP: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_HAS_MAP_FIELDS: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len;
                DECODE_INTEGER(list_len, code, i, next_off, next_off);
                int fail = 0;
                for (int j = 0; j < list_len && !fail; ++j) {
                    term key;
                    DECODE_COMPACT_TERM(key, code, i, next_off, next_off);
                }
                if (!fail) {
                    NEXT_INSTRUCTION(next_off);
                }
                break;
            }

            case OP_GET_MAP_ELEMENTS: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);

                next_off++; // skip extended list tag {z, 1}
                int list_len;
                DECODE_INTEGER(list_len, code, i, next_off, next_off);
                int num_elements = list_len / 2;
                int fail = 0;
                for (int j = 0; j < num_elements && !fail; ++j) {
                    term key;
                    DECODE_COMPACT_TERM(key, code, i, next_off, next_off);
                    dreg_t dreg;
                    dreg_type_t dreg_type;
                    DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                }
                if (!fail) {
                    NEXT_INSTRUCTION(next_off);
                }
                break;
            }

            case OP_IS_TAGGED_TUPLE: {
                int next_off = 1;
                int label = DECODE_LABEL(code, i, next_off, &next_off);
                term arg1;
                DECODE_COMPACT_TERM(arg1, code, i, next_off, next_off)
                int arity;
                DECODE_INTEGER(arity, code, i, next_off, next_off)
                int tag_atom_id;
                DECODE_ATOM(tag_atom_id, code, i, next_off, next_off)

                UNUSED(label)
                UNUSED(arg1)
                NEXT_INSTRUCTION(next_off);

                break;
            }

            case OP_GET_HD: {
                int next_off = 1;
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off)
                dreg_t head_dreg;
                dreg_type_t head_dreg_type;
                DECODE_DEST_REGISTER(head_dreg, head_dreg_type, code, i, next_off, next_off);

                UNUSED(src_value)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_GET_TL: {
                int next_off = 1;
                term src_value;
                DECODE_COMPACT_TERM(src_value, code, i, next_off, next_off)
                dreg_t tail_dreg;
                dreg_type_t tail_dreg_type;
                DECODE_DEST_REGISTER(tail_dreg, tail_dreg_type, code, i, next_off, next_off);

                UNUSED(src_value)

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_PUT_TUPLE2: {
                int next_off = 1;
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
                next_off++; // skip extended list tag
                int size;
                DECODE_INTEGER(size, code, i, next_off, next_off)

                UNUSED(dreg);

                for (int j = 0; j < size; j++) {
                    term element;
                    DECODE_COMPACT_TERM(element, code, i, next_off, next_off)

                    UNUSED(element);
                }

                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_SWAP: {
                int next_off = 1;
                dreg_t reg_a;
                dreg_type_t reg_a_type;
                DECODE_DEST_REGISTER(reg_a, reg_a_type, code, i, next_off, next_off);
                dreg_t reg_b;
                dreg_type_t reg_b_type;
                DECODE_DEST_REGISTER(reg_b, reg_b_type, code, i, next_off, next_off);
                NEXT_INSTRUCTION(next_off);
                break;
            }

            case OP_BS_START_MATCH4: {
                int next_off = 1;
                // fail since OTP 23 might be either 'no_fail', 'resume' or a fail label
                // we are ignoring this right now, but we might use it for future optimizations.
                term fail;
                DECODE_COMPACT_TERM(fail, code, i, next_off, next_off);
                term live;
                DECODE_COMPACT_TERM(live, code, i, next_off, next_off);
                term src;
                DECODE_COMPACT_TERM(src, code, i, next_off, next_off);
                dreg_t dreg;
                dreg_type_t dreg_type;
                DECODE_DEST_REGISTER(dreg, dreg_type, code, i, next_off, next_off);
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

#undef DECODE_COMPACT_TERM
