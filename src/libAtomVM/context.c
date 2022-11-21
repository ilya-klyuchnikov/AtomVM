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

#include "context.h"

#include "dictionary.h"
#include "globalcontext.h"
#include "list.h"
#include "mailbox.h"
#include "opcodesswitch_common.h"
#include "bitstring.h"

#define T_DEST_REG(dreg_type, dreg) \
    (*dreg_type.ptr == ctx->x) ? 'x' : 'y', (dreg)

#define DECODE_COMPACT_TERM(dest_term, code_chunk, base_index, off, next_operand_offset)                                \
{                                                                                                                       \
    uint8_t first_byte = (code_chunk[(base_index) + (off)]);                                                            \
    switch (first_byte & 0xF) {                                                                                         \
        case COMPACT_LARGE_LITERAL:                                                                                     \
        case COMPACT_LITERAL:                                                                                           \
            switch (((first_byte) >> 3) & 0x3) {                                                                        \
                case 0:                                                                                                 \
                case 2:                                                                                                 \
                    dest_term = term_from_int4(first_byte >> 4);                                                        \
                    next_operand_offset += 1;                                                                           \
                    break;                                                                                              \
                                                                                                                        \
                case 1:                                                                                                 \
                    dest_term = term_from_int4(((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1]);      \
                    next_operand_offset += 2;                                                                           \
                    break;                                                                                              \
                                                                                                                        \
                default:                                                                                                \
                    fprintf(stderr, "Operand not a literal: %x, or unsupported encoding\n", (first_byte));              \
                    AVM_ABORT();                                                                                        \
                    break;                                                                                              \
            }                                                                                                           \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_SMALLINT4:                                                                                         \
            dest_term = term_from_int4(first_byte >> 4);                                                                \
            next_operand_offset += 1;                                                                                   \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_ATOM:                                                                                              \
            if (first_byte == COMPACT_ATOM) {                                                                           \
                dest_term = term_nil();                                                                                 \
            } else {                                                                                                    \
                dest_term = module_get_atom_term_by_id(mod, first_byte >> 4);                                           \
            }                                                                                                           \
            next_operand_offset += 1;                                                                                   \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_XREG:                                                                                              \
            dest_term = ctx->x[first_byte >> 4];                                                                        \
            next_operand_offset += 1;                                                                                   \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_YREG:                                                                                              \
            dest_term = ctx->e[first_byte >> 4];                                                                        \
            next_operand_offset += 1;                                                                                   \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_EXTENDED:                                                                                          \
            switch (first_byte) {                                                                                       \
                case COMPACT_EXTENDED_LITERAL: {                                                                        \
                    uint8_t first_extended_byte = code_chunk[(base_index) + (off) + 1];                                 \
                    if (!(first_extended_byte & 0xF)) {                                                                 \
                        dest_term = module_load_literal(mod, first_extended_byte >> 4, ctx);                            \
                        next_operand_offset += 2;                                                                       \
                    } else if ((first_extended_byte & 0xF) == 0x8) {                                                    \
                        uint8_t byte_1 = code_chunk[(base_index) + (off) + 2];                                          \
                        uint16_t index = (((uint16_t) first_extended_byte & 0xE0) << 3) | byte_1;                       \
                        dest_term = module_load_literal(mod, index, ctx);                                               \
                        next_operand_offset += 3;                                                                       \
                    } else {                                                                                            \
                        VM_ABORT();                                                                                     \
                    }                                                                                                   \
                    if (UNLIKELY(term_is_invalid_term(dest_term))) {                                                    \
                        RAISE_ERROR(OUT_OF_MEMORY_ATOM);                                                                \
                    }                                                                                                   \
                                                                                                                        \
                    break;                                                                                              \
                }                                                                                                       \
                default:                                                                                                \
                    VM_ABORT();                                                                                         \
                    break;                                                                                              \
            }                                                                                                           \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_LARGE_ATOM:                                                                                        \
            switch (first_byte & COMPACT_LARGE_IMM_MASK) {                                                              \
                case COMPACT_11BITS_VALUE:                                                                              \
                    dest_term = module_get_atom_term_by_id(mod, ((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1]); \
                    next_operand_offset += 2;                                                                           \
                    break;                                                                                              \
                                                                                                                        \
                default:                                                                                                \
                    VM_ABORT();                                                                                         \
                    break;                                                                                              \
            }                                                                                                           \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_LARGE_INTEGER:                                                                                     \
            switch (first_byte & COMPACT_LARGE_IMM_MASK) {                                                              \
                case COMPACT_11BITS_VALUE:                                                                              \
                    dest_term = term_from_int11(((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1]);     \
                    next_operand_offset += 2;                                                                           \
                    break;                                                                                              \
                                                                                                                        \
                case COMPACT_NBITS_VALUE:                                                                               \
                    dest_term = large_integer_to_term(ctx, (code_chunk) + (base_index) + (off), &(next_operand_offset));\
                    if (UNLIKELY(term_is_invalid_term(dest_term))) {                                                    \
                        HANDLE_ERROR();                                                                                 \
                    }                                                                                                   \
                    break;                                                                                              \
                                                                                                                        \
                default:                                                                                                \
                    VM_ABORT();                                                                                         \
                    break;                                                                                              \
            }                                                                                                           \
            break;                                                                                                      \
                                                                                                                        \
        case COMPACT_LARGE_YREG:                                                                                        \
            if (LIKELY((first_byte & COMPACT_LARGE_IMM_MASK) == COMPACT_11BITS_VALUE)) {                                \
                dest_term = ctx->e[((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1]];                  \
                next_operand_offset += 2;                                                                               \
            } else {                                                                                                    \
                VM_ABORT();                                                                                             \
            }                                                                                                           \
            break;                                                                                                      \
                                                                                                                        \
        default:                                                                                                        \
            VM_ABORT();                                                                                                 \
    }                                                                                                                   \
}

#define READ_DEST_REGISTER(ptr, dreg) \
    *(*(ptr) + (dreg));


#define WRITE_REGISTER(ptr, dreg, value)                                                      \
{                                                                                                   \
    *(*(ptr) + (dreg)) = value;                                                         \
}

static void DECODE_DEST_REGISTER(dreg_t *dreg, term ***dreg_type, const uint8_t *code_chunk, unsigned int base_index, int off, int *next_operand_offset, term **x_regs, Context *ctx){
    uint8_t first_byte = code_chunk[(base_index) + (off)];
    uint8_t reg_type = first_byte & 0xF;
    uint8_t reg_index = (first_byte >> 4);
    switch (reg_type) {
        case COMPACT_XREG:
            *dreg_type = x_regs;
            (*dreg) = reg_index;
            *next_operand_offset += 1;
            break;
        case COMPACT_YREG:
            *dreg_type = &ctx->e;
            (*dreg) = reg_index;
            *next_operand_offset += 1;
            break;
        case COMPACT_LARGE_YREG:
            if (LIKELY((first_byte & COMPACT_LARGE_IMM_MASK) == COMPACT_11BITS_VALUE)) {
                *dreg_type = &ctx->e;
                (*dreg) = (((first_byte & 0xE0) << 3) | code_chunk[(base_index) + (off) + 1]);
                *next_operand_offset += 2;
            } else {
                abort();
            }
            break;
        default:
            abort();
    }
}


struct Int24
{
    int32_t val24 : 24;
};

struct Int40
{
    int64_t val40 : 40;
};

struct Int48
{
    int64_t val48 : 48;
};

struct Int56
{
    int64_t val56 : 56;
};

#define SWAP_KV_PAIR(I, J)            \
    {                                 \
        struct kv_pair tmp = kv[(I)]; \
        kv[(I)] = kv[(J)];            \
        kv[(J)] = tmp;                \
    }

struct kv_pair
{
    term key;
    term value;
};

static void sort_kv_pairs(Context *ctx, struct kv_pair *kv, int size)
{
    int k = size;
    while (1 < k) {
        int max_pos = 0;
        for (int i = 1; i < k; i++) {
            term t_max = kv[max_pos].key;
            term t = kv[i].key;
            int c = term_compare(t, t_max, ctx);
            if (0 < c) {
                max_pos = i;
            }
        }
        if (max_pos != k - 1) {
            SWAP_KV_PAIR(k - 1, max_pos);
        }
        k--;
        // kv[k..size] sorted
    }
}

#define IMPL_EXECUTE_LOOP
#include "opcodesswitch.h"
#undef IMPL_EXECUTE_LOOP

#define DEFAULT_STACK_SIZE 8
#define BYTES_PER_TERM (TERM_BITS / 8)

static void context_monitors_handle_terminate(Context *ctx);

Context *context_new(GlobalContext *glb)
{
    Context *ctx = malloc(sizeof(Context));
    if (IS_NULL_PTR(ctx)) {
        fprintf(stderr, "Failed to allocate memory: %s:%i.\n", __FILE__, __LINE__);
        return NULL;
    }
    ctx->cp = 0;

    ctx->heap_start = (term *) calloc(DEFAULT_STACK_SIZE, sizeof(term));
    if (IS_NULL_PTR(ctx->heap_start)) {
        fprintf(stderr, "Failed to allocate memory: %s:%i.\n", __FILE__, __LINE__);
        free(ctx);
        return NULL;
    }
    ctx->stack_base = ctx->heap_start + DEFAULT_STACK_SIZE;
    ctx->e = ctx->stack_base;
    ctx->heap_ptr = ctx->heap_start;

    ctx->avail_registers = 16;
    context_clean_registers(ctx, 0);

    ctx->min_heap_size = 0;
    ctx->max_heap_size = 0;
    ctx->has_min_heap_size = 0;
    ctx->has_max_heap_size = 0;

    list_append(&glb->ready_processes, &ctx->processes_list_head);

    list_init(&ctx->mailbox);
    list_init(&ctx->save_queue);
    list_init(&ctx->dictionary);

    ctx->global = glb;

    ctx->process_id = globalcontext_get_new_process_id(glb);
    list_append(&glb->processes_table, &ctx->processes_table_head);

    ctx->native_handler = NULL;

    ctx->saved_ip = NULL;
    ctx->jump_to_on_restore = NULL;

    ctx->leader = 0;

    timer_wheel_item_init(&ctx->timer_wheel_head, NULL, 0);

    list_init(&ctx->monitors_head);

    ctx->trap_exit = false;

    list_init(&ctx->heap_fragments);
    ctx->heap_fragments_size = 0;

    ctx->flags = 0;

    ctx->platform_data = NULL;

    ctx->group_leader = term_from_local_process_id(INVALID_PROCESS_ID);

    ctx->bs = term_invalid_term();
    ctx->bs_offset = 0;

    ctx->exit_reason = NORMAL_ATOM;
    ctx->mso_list = term_nil();

    return ctx;
}

void context_destroy(Context *ctx)
{
    list_remove(&ctx->processes_table_head);

    memory_sweep_mso_list(ctx->mso_list);
    dictionary_destroy(&ctx->dictionary);

    context_monitors_handle_terminate(ctx);

    free(ctx->heap_start);
    free(ctx);
}

size_t context_message_queue_len(Context *ctx)
{
    size_t num_messages = 0;

    struct ListHead *item;
    LIST_FOR_EACH (item, &ctx->mailbox) {
        num_messages++;
    }

    return num_messages;
}

size_t context_size(Context *ctx)
{
    size_t messages_size = 0;

    struct ListHead *item;
    LIST_FOR_EACH (item, &ctx->mailbox) {
        Message *msg = GET_LIST_ENTRY(item, Message, mailbox_list_head);
        messages_size += sizeof(Message) + msg->msg_memory_size;
    }

    // TODO include ctx->platform_data
    return sizeof(Context)
        + messages_size
        + context_memory_size(ctx) * BYTES_PER_TERM;
}

static void context_monitors_handle_terminate(Context *ctx)
{
    struct ListHead *item;
    struct ListHead *tmp;
    MUTABLE_LIST_FOR_EACH (item, tmp, &ctx->monitors_head) {
        struct Monitor *monitor = GET_LIST_ENTRY(item, struct Monitor, monitor_list_head);
        int local_process_id = term_to_local_process_id(monitor->monitor_pid);
        Context *target = globalcontext_get_process(ctx->global, local_process_id);
        if (IS_NULL_PTR(target)) {
            // TODO: we should scan for existing monitors when a context is destroyed
            // otherwise memory might be wasted for long living processes
            free(monitor);
            continue;
        }

        if (monitor->linked && (ctx->exit_reason != NORMAL_ATOM || target->trap_exit)) {
            if (target->trap_exit) {
                if (UNLIKELY(memory_ensure_free(ctx, TUPLE_SIZE(3)) != MEMORY_GC_OK)) {
                    //TODO: handle out of memory here
                    fprintf(stderr, "Cannot handle out of memory.\n");
                    AVM_ABORT();
                }

                // TODO: move it out of heap
                term info_tuple = term_alloc_tuple(3, ctx);
                term_put_tuple_element(info_tuple, 0, EXIT_ATOM);
                term_put_tuple_element(info_tuple, 1, term_from_local_process_id(ctx->process_id));
                term_put_tuple_element(info_tuple, 2, ctx->exit_reason);

                mailbox_send(target, info_tuple);
            } else {
                target->exit_reason = memory_copy_term_tree(&ctx->heap_ptr, ctx->exit_reason, &ctx->mso_list);

                // TODO: this cannot work on multicore systems
                // target context should be marked as killed and terminated during next scheduling
                scheduler_terminate(target);
            }
        } else if (!monitor->linked) {
            int required_terms = REF_SIZE + TUPLE_SIZE(5);
            if (UNLIKELY(memory_ensure_free(ctx, required_terms) != MEMORY_GC_OK)) {
                //TODO: handle out of memory here
                fprintf(stderr, "Cannot handle out of memory.\n");
                AVM_ABORT();
            }

            // TODO: move it out of heap
            term ref = term_from_ref_ticks(monitor->ref_ticks, ctx);

            term info_tuple = term_alloc_tuple(5, ctx);
            term_put_tuple_element(info_tuple, 0, DOWN_ATOM);
            term_put_tuple_element(info_tuple, 1, ref);
            term_put_tuple_element(info_tuple, 2, PROCESS_ATOM);
            term_put_tuple_element(info_tuple, 3, term_from_local_process_id(ctx->process_id));
            term_put_tuple_element(info_tuple, 4, ctx->exit_reason);

            mailbox_send(target, info_tuple);
        }
        free(monitor);
    }
}

uint64_t context_monitor(Context *ctx, term monitor_pid, bool linked)
{
    uint64_t ref_ticks = globalcontext_get_ref_ticks(ctx->global);

    struct Monitor *monitor = malloc(sizeof(struct Monitor));
    if (IS_NULL_PTR(monitor)) {
        return 0;
    }
    monitor->monitor_pid = monitor_pid;
    monitor->ref_ticks = ref_ticks;
    monitor->linked = linked;
    list_append(&ctx->monitors_head, &monitor->monitor_list_head);

    return ref_ticks;
}

void context_demonitor(Context *ctx, term monitor_pid, bool linked)
{
    struct ListHead *item;
    LIST_FOR_EACH (item, &ctx->monitors_head) {
        struct Monitor *monitor = GET_LIST_ENTRY(item, struct Monitor, monitor_list_head);
        if ((monitor->monitor_pid == monitor_pid) && (monitor->linked == linked)) {
            list_remove(&monitor->monitor_list_head);
            free(monitor);
            return;
        }
    }
}
