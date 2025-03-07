/*
 * This file is part of AtomVM.
 *
 * Copyright 2019 Fred Dushin <fred@dushin.net>
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

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include "atom.h"
#include "defaultatoms.h"
#include "esp32_sys.h"
#include "interop.h"
#include "memory.h"
#include "nifs.h"
#include "platform_defaultatoms.h"
#include "term.h"

#include "esp_log.h"
#include "esp_mac.h"
#include <esp_partition.h>
#include <esp_sleep.h>
#include <esp_system.h>
#include <mbedtls/md5.h>
#include <mbedtls/sha1.h>
#include <mbedtls/sha256.h>
#include <mbedtls/sha512.h>
#include <soc/soc.h>
#include <stdlib.h>

// introduced starting with 4.4
#if ESP_IDF_VERSION_MAJOR >= 5
#include <esp_random.h>
#endif

//#define ENABLE_TRACE
#include "trace.h"

#define TAG "atomvm"

#define MAX_MD_SIZE 64

static const char *const esp_rst_unknown_atom   = "\xF"  "esp_rst_unknown";
static const char *const esp_rst_poweron        = "\xF"  "esp_rst_poweron";
static const char *const esp_rst_ext            = "\xB"  "esp_rst_ext";
static const char *const esp_rst_sw             = "\xA"  "esp_rst_sw";
static const char *const esp_rst_panic          = "\xD"  "esp_rst_panic";
static const char *const esp_rst_int_wdt        = "\xF"  "esp_rst_int_wdt";
static const char *const esp_rst_task_wdt       = "\x10" "esp_rst_task_wdt";
static const char *const esp_rst_wdt            = "\xB"  "esp_rst_wdt";
static const char *const esp_rst_deepsleep      = "\x11" "esp_rst_deepsleep";
static const char *const esp_rst_brownout       = "\x10" "esp_rst_brownout";
static const char *const esp_rst_sdio           = "\xC"  "esp_rst_sdio";
//                                                        123456789ABCDEF01

enum NetworkInterface {
    WifiSTAInterface,
    WifiSoftAPInterface,
    InvalidInterface
};

static const AtomStringIntPair interface_table[] = {
    { ATOM_STR("\x8", "wifi_sta"), WifiSTAInterface },
    { ATOM_STR("\xB", "wifi_softap"), WifiSoftAPInterface },
    SELECT_INT_DEFAULT(InvalidInterface)
};

enum crypto_algorithm
{
    CryptoInvalidAlgorithm = 0,
    CryptoMd5,
    CryptoSha1,
    CryptoSha224,
    CryptoSha256,
    CryptoSha384,
    CryptoSha512
};

static const AtomStringIntPair crypto_algorithm_table[] = {
    { ATOM_STR("\x3", "md5"), CryptoMd5 },
    { ATOM_STR("\x3", "sha"), CryptoSha1 },
    { ATOM_STR("\x6", "sha224"), CryptoSha224 },
    { ATOM_STR("\x6", "sha256"), CryptoSha256 },
    { ATOM_STR("\x6", "sha384"), CryptoSha384 },
    { ATOM_STR("\x6", "sha512"), CryptoSha512 },
    SELECT_INT_DEFAULT(CryptoInvalidAlgorithm)
};

#if defined __has_include
#if __has_include(<esp_idf_version.h>)
#include <esp_idf_version.h>
#endif
#endif

//
// NIFs
//

static term nif_esp_random(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);
    UNUSED(argv);
    uint32_t r = esp_random();
    if (UNLIKELY(memory_ensure_free(ctx, BOXED_INT_SIZE) != MEMORY_GC_OK)) {
        RAISE_ERROR(OUT_OF_MEMORY_ATOM);
    }
    return term_make_boxed_int(r, &ctx->heap);
}

static term nif_esp_random_bytes(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);
    VALIDATE_VALUE(argv[0], term_is_integer);

    avm_int_t len = term_to_int(argv[0]);
    if (len < 0) {
        RAISE_ERROR(BADARG_ATOM);
    }
    if (len == 0) {
        if (UNLIKELY(memory_ensure_free(ctx, term_binary_heap_size(0)) != MEMORY_GC_OK)) {
            RAISE_ERROR(OUT_OF_MEMORY_ATOM);
        }
        term binary = term_create_empty_binary(0, &ctx->heap, ctx->global);
        return binary;
    } else {
        uint8_t *buf = malloc(len);
        if (UNLIKELY(IS_NULL_PTR(buf))) {
            RAISE_ERROR(OUT_OF_MEMORY_ATOM);
        }
        esp_fill_random(buf, len);
        if (UNLIKELY(memory_ensure_free(ctx, term_binary_heap_size(len)) != MEMORY_GC_OK)) {
            RAISE_ERROR(OUT_OF_MEMORY_ATOM);
        }
        term binary = term_from_literal_binary(buf, len, &ctx->heap, ctx->global);
        free(buf);
        return binary;
    }
}

static term nif_esp_restart(Context *ctx, int argc, term argv[])
{
    UNUSED(ctx);
    UNUSED(argc);
    UNUSED(argv);
    esp_restart();
    return OK_ATOM;
}

static term nif_esp_reset_reason(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);
    UNUSED(argv);
    esp_reset_reason_t reason = esp_reset_reason();
    switch (reason) {
        case ESP_RST_UNKNOWN:
            return globalcontext_make_atom(ctx->global, esp_rst_unknown_atom);
        case ESP_RST_POWERON:
            return globalcontext_make_atom(ctx->global, esp_rst_poweron);
        case ESP_RST_EXT:
            return globalcontext_make_atom(ctx->global, esp_rst_ext);
        case ESP_RST_SW:
            return globalcontext_make_atom(ctx->global, esp_rst_sw);
        case ESP_RST_PANIC:
            return globalcontext_make_atom(ctx->global, esp_rst_panic);
        case ESP_RST_INT_WDT:
            return globalcontext_make_atom(ctx->global, esp_rst_int_wdt);
        case ESP_RST_TASK_WDT:
            return globalcontext_make_atom(ctx->global, esp_rst_task_wdt);
        case ESP_RST_WDT:
            return globalcontext_make_atom(ctx->global, esp_rst_wdt);
        case ESP_RST_DEEPSLEEP:
            return globalcontext_make_atom(ctx->global, esp_rst_deepsleep);
        case ESP_RST_BROWNOUT:
            return globalcontext_make_atom(ctx->global, esp_rst_brownout);
        case ESP_RST_SDIO:
            return globalcontext_make_atom(ctx->global, esp_rst_sdio);
        default:
            return UNDEFINED_ATOM;
    }
}

static term nif_esp_freq_hz(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);
    UNUSED(argv);

    return term_from_int(APB_CLK_FREQ);
}

static const esp_partition_t *get_partition(term partition_name_term, bool *valid_string)
{
    int ok;
    char *partition_name = interop_term_to_string(partition_name_term, &ok);
    if (UNLIKELY(!ok)) {
        *valid_string = false;
        return NULL;
    }
    *valid_string = true;

    const esp_partition_t *partition = esp_partition_find_first(ESP_PARTITION_TYPE_DATA, ESP_PARTITION_SUBTYPE_ANY, partition_name);

    free(partition_name);

    return partition;
}

static term nif_esp_partition_erase_range(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    bool valid_partition_string;
    const esp_partition_t *partition = get_partition(argv[0], &valid_partition_string);
    if (UNLIKELY(!valid_partition_string)) {
        RAISE_ERROR(BADARG_ATOM);
    }
    if (IS_NULL_PTR(partition)) {
        return ERROR_ATOM;
    }

    VALIDATE_VALUE(argv[1], term_is_integer);
    avm_int_t offset = term_to_int(argv[1]);

    avm_int_t size = 0;
    if (argc == 3) {
        VALIDATE_VALUE(argv[2], term_is_integer);
        size = term_to_int(argv[2]);
    } else {
        size = partition->size - offset;
    }

    esp_err_t res = esp_partition_erase_range(partition, offset, size);
    if (UNLIKELY(res != ESP_OK)) {
        return ERROR_ATOM;
    }

    return OK_ATOM;
}

static term nif_esp_partition_write(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    bool valid_partition_string;
    const esp_partition_t *partition = get_partition(argv[0], &valid_partition_string);
    if (UNLIKELY(!valid_partition_string)) {
        RAISE_ERROR(BADARG_ATOM);
    }
    if (IS_NULL_PTR(partition)) {
        return ERROR_ATOM;
    }

    VALIDATE_VALUE(argv[1], term_is_integer);
    avm_int_t offset = term_to_int(argv[1]);

    term binary_term = argv[2];
    VALIDATE_VALUE(binary_term, term_is_binary);
    avm_int_t size = term_binary_size(binary_term);
    const char *data = term_binary_data(binary_term);

    esp_err_t res = esp_partition_write(partition, offset, data, size);
    if (UNLIKELY(res != ESP_OK)) {
        return ERROR_ATOM;
    }

    return OK_ATOM;
}

static term nif_esp_partition_list(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    size_t needed = 0;

    for (esp_partition_iterator_t it
         = esp_partition_find(ESP_PARTITION_TYPE_ANY, ESP_PARTITION_SUBTYPE_ANY, NULL);
         it != NULL; it = esp_partition_next(it)) {
        const esp_partition_t *partition = esp_partition_get(it);
        // {name, type, subtype, offset, size, props}
        // TODO: right now props is empty, so it doesn't take space
        // all integers are < 27 bits, so we are safe
        // * 2 is for accounting the reversed list
        int label_len = strlen(partition->label);
        needed += CONS_SIZE * 2 + TUPLE_SIZE(6) + TERM_BINARY_HEAP_SIZE(label_len);
    }

    if (UNLIKELY(memory_ensure_free(ctx, needed) != MEMORY_GC_OK)) {
        RAISE_ERROR(OUT_OF_MEMORY_ATOM);
    }

    term l = term_nil();
    for (esp_partition_iterator_t it
         = esp_partition_find(ESP_PARTITION_TYPE_ANY, ESP_PARTITION_SUBTYPE_ANY, NULL);
         it != NULL; it = esp_partition_next(it)) {
        const esp_partition_t *partition = esp_partition_get(it);
        // {name, type, subtype, offset, size, props}
        int len = strlen(partition->label);
        term label_bin = term_from_literal_binary(partition->label, len, &ctx->heap, ctx->global);
        term t = term_alloc_tuple(6, &ctx->heap);
        term_put_tuple_element(t, 0, label_bin);
        term_put_tuple_element(t, 1, term_from_int(partition->type));
        term_put_tuple_element(t, 2, term_from_int(partition->subtype));
        term_put_tuple_element(t, 3, term_from_int(partition->address));
        term_put_tuple_element(t, 4, term_from_int(partition->size));
        term_put_tuple_element(t, 5, term_nil());
        l = term_list_prepend(t, l, &ctx->heap);
    }

    term return_list = term_nil();
    for (term li = l; li != term_nil(); li = term_get_list_tail(li)) {
        return_list = term_list_prepend(term_get_list_head(li), return_list, &ctx->heap);
    }

    return return_list;
}

static term nif_esp_deep_sleep(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    VALIDATE_VALUE(argv[0], term_is_any_integer);
    avm_int64_t msecs = term_maybe_unbox_int64(argv[0]);

    esp_deep_sleep(msecs * 1000ULL);

    // technically, this function does not return
    return OK_ATOM;
}
#if SOC_PM_SUPPORT_EXT_WAKEUP
static const char *const sleep_wakeup_ext0_atom = "\x11" "sleep_wakeup_ext0";
static const char *const sleep_wakeup_ext1_atom = "\x11" "sleep_wakeup_ext1";
#endif
static const char *const sleep_wakeup_timer_atom = "\x12" "sleep_wakeup_timer";
static const char *const sleep_wakeup_touchpad_atom = "\x15" "sleep_wakeup_touchpad";
static const char *const sleep_wakeup_ulp_atom = "\x10" "sleep_wakeup_ulp";
static const char *const sleep_wakeup_gpio_atom = "\x11" "sleep_wakeup_gpio";
static const char *const sleep_wakeup_uart_atom = "\x11" "sleep_wakeup_uart";
#ifdef ESP_SLEEP_WAKEUP_WIFI
static const char *const sleep_wakeup_wifi_atom = "\x11" "sleep_wakeup_wifi";
#endif
#ifdef ESP_SLEEP_WAKEUP_COCPU
static const char *const sleep_wakeup_cocpu_atom = "\x12" "sleep_wakeup_cocpu";
#endif
#ifdef ESP_SLEEP_WAKEUP_COCPU_TRAP_TRIG
static const char *const sleep_wakeup_cocpu_trap_trig_atom = "\x1C" "sleep_wakeup_cocpu_trap_trig";
#endif
#ifdef ESP_SLEEP_WAKEUP_BT
static const char *const sleep_wakeup_bt_atom = "\xF" "sleep_wakeup_bt";
#endif

static term nif_esp_sleep_get_wakeup_cause(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);
    UNUSED(argv);

    esp_sleep_wakeup_cause_t cause = esp_sleep_get_wakeup_cause();

    switch (cause) {
        case ESP_SLEEP_WAKEUP_UNDEFINED:
            return UNDEFINED_ATOM;
#if SOC_PM_SUPPORT_EXT_WAKEUP
        case ESP_SLEEP_WAKEUP_EXT0:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_ext0_atom);
        case ESP_SLEEP_WAKEUP_EXT1:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_ext1_atom);
#endif
        case ESP_SLEEP_WAKEUP_TIMER:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_timer_atom);
        case ESP_SLEEP_WAKEUP_TOUCHPAD:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_touchpad_atom);
        case ESP_SLEEP_WAKEUP_ULP:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_ulp_atom);
        case ESP_SLEEP_WAKEUP_GPIO:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_gpio_atom);
        case ESP_SLEEP_WAKEUP_UART:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_uart_atom);
#ifdef ESP_SLEEP_WAKEUP_WIFI
        case ESP_SLEEP_WAKEUP_WIFI:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_wifi_atom);
#endif
#ifdef ESP_SLEEP_WAKEUP_COCPU
        case ESP_SLEEP_WAKEUP_COCPU:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_cocpu_atom);
#endif
#ifdef ESP_SLEEP_WAKEUP_COCPU_TRAP_TRIG
        case ESP_SLEEP_WAKEUP_COCPU_TRAP_TRIG:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_cocpu_trap_trig_atom);
#endif
#ifdef ESP_SLEEP_WAKEUP_BT
        case ESP_SLEEP_WAKEUP_BT:
            return globalcontext_make_atom(ctx->global, sleep_wakeup_bt_atom);
#endif
        default:
            return ERROR_ATOM;
    }
}

#if SOC_PM_SUPPORT_EXT_WAKEUP

static term nif_esp_sleep_enable_ext0_wakeup(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    VALIDATE_VALUE(argv[0], term_is_integer);
    VALIDATE_VALUE(argv[1], term_is_integer);
    gpio_num_t pin = term_to_int(argv[0]);
    int level = term_to_int(argv[1]);
    esp_err_t err = esp_sleep_enable_ext0_wakeup(pin, level);
    if (UNLIKELY(err == ESP_ERR_INVALID_ARG)) {
        RAISE_ERROR(BADARG_ATOM);
    }
    if (UNLIKELY(err != ESP_OK)) {
        return ERROR_ATOM;
    }
    return OK_ATOM;
}

static term nif_esp_sleep_enable_ext1_wakeup(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    VALIDATE_VALUE(argv[0], term_is_any_integer);
    VALIDATE_VALUE(argv[1], term_is_integer);
    avm_int64_t mask = term_maybe_unbox_int64(argv[0]);
    esp_sleep_ext1_wakeup_mode_t mode = term_to_int(argv[1]);
    esp_err_t err = esp_sleep_enable_ext1_wakeup(mask, mode);
    if (UNLIKELY(err == ESP_ERR_INVALID_ARG)) {
        RAISE_ERROR(BADARG_ATOM);
    }
    if (UNLIKELY(err != ESP_OK)) {
        return ERROR_ATOM;
    }
    return OK_ATOM;
}

#endif

#define DEFINE_DO_HASH(ALGORITHM, SUFFIX)                                                                      \
    static InteropFunctionResult ALGORITHM##_hash_fold_fun(term t, void *accum)                                \
    {                                                                                                          \
        mbedtls_##ALGORITHM##_context *md_ctx = (mbedtls_##ALGORITHM##_context *) accum;                       \
        if (term_is_integer(t)) {                                                                              \
            avm_int64_t tmp = term_maybe_unbox_int64(t);                                                       \
            if (tmp < 0 || tmp > 255) {                                                                        \
                return InteropBadArg;                                                                          \
            }                                                                                                  \
            uint8_t val = (uint8_t) tmp;                                                                       \
            mbedtls_##ALGORITHM##_update##SUFFIX(md_ctx, &val, 1);                                             \
        } else /* term_is_binary(t) */ {                                                                       \
            mbedtls_##ALGORITHM##_update(md_ctx, (uint8_t *) term_binary_data(t), term_binary_size(t));        \
        }                                                                                                      \
        return InteropOk;                                                                                      \
    }                                                                                                          \
                                                                                                               \
    static bool do_##ALGORITHM##_hash(term data, unsigned char *dst)                                           \
    {                                                                                                          \
        mbedtls_##ALGORITHM##_context md_ctx;                                                                  \
                                                                                                               \
        mbedtls_##ALGORITHM##_init(&md_ctx);                                                                   \
        mbedtls_##ALGORITHM##_starts##SUFFIX(&md_ctx);                                                         \
                                                                                                               \
        InteropFunctionResult result = interop_chardata_fold(data, ALGORITHM##_hash_fold_fun, NULL, (void *) &md_ctx); \
        if (UNLIKELY(result != InteropOk)) {                                                                   \
            return false;                                                                                      \
        }                                                                                                      \
                                                                                                               \
        if (UNLIKELY(mbedtls_##ALGORITHM##_finish##SUFFIX(&md_ctx, dst) != 0)) {                               \
            return false;                                                                                      \
        }                                                                                                      \
                                                                                                               \
        return true;                                                                                           \
    }

#define DEFINE_DO_HASH2(ALGORITHM, SUFFIX, IS_OTHER)                                                           \
    static InteropFunctionResult ALGORITHM##_hash_fold_fun_##IS_OTHER(term t, void *accum)                     \
    {                                                                                                          \
        mbedtls_##ALGORITHM##_context *md_ctx = (mbedtls_##ALGORITHM##_context *) accum;                       \
        if (term_is_any_integer(t)) {                                                                          \
            avm_int64_t tmp = term_maybe_unbox_int64(t);                                                       \
            if (tmp < 0 || tmp > 255) {                                                                        \
                return InteropBadArg;                                                                          \
            }                                                                                                  \
            uint8_t val = (avm_int64_t) tmp;                                                                   \
            mbedtls_##ALGORITHM##_update##SUFFIX(md_ctx, &val, 1);                                             \
        } else /* term_is_binary(t) */ {                                                                       \
            mbedtls_##ALGORITHM##_update(md_ctx, (uint8_t *) term_binary_data(t), term_binary_size(t));        \
        }                                                                                                      \
        return InteropOk;                                                                                      \
    }                                                                                                          \
                                                                                                               \
    static bool do_##ALGORITHM##_hash_##IS_OTHER(term data, unsigned char *dst)                                \
    {                                                                                                          \
        mbedtls_##ALGORITHM##_context md_ctx;                                                                  \
                                                                                                               \
        mbedtls_##ALGORITHM##_init(&md_ctx);                                                                   \
        mbedtls_##ALGORITHM##_starts##SUFFIX(&md_ctx, IS_OTHER);                                               \
                                                                                                               \
        InteropFunctionResult result = interop_chardata_fold(data, ALGORITHM##_hash_fold_fun_##IS_OTHER, NULL, (void *) &md_ctx); \
        if (UNLIKELY(result != InteropOk)) {                                                                   \
            return false;                                                                                      \
        }                                                                                                      \
                                                                                                               \
        if (UNLIKELY(mbedtls_##ALGORITHM##_finish##SUFFIX(&md_ctx, dst) != 0)) {                               \
            return false;                                                                                      \
        }                                                                                                      \
                                                                                                               \
        return true;                                                                                           \
    }

#if ESP_IDF_VERSION < ESP_IDF_VERSION_VAL(5, 0, 0)

DEFINE_DO_HASH(md5, _ret)
DEFINE_DO_HASH(sha1, _ret)
DEFINE_DO_HASH2(sha256, _ret, true)
DEFINE_DO_HASH2(sha256, _ret, false)
DEFINE_DO_HASH2(sha512, _ret, true)
DEFINE_DO_HASH2(sha512, _ret, false)

#else

DEFINE_DO_HASH(md5, )
DEFINE_DO_HASH(sha1, )
DEFINE_DO_HASH2(sha256, , true)
DEFINE_DO_HASH2(sha256, , false)
DEFINE_DO_HASH2(sha512, , true)
DEFINE_DO_HASH2(sha512, , false)

#endif

static term nif_crypto_hash(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);
    term type = argv[0];
    VALIDATE_VALUE(type, term_is_atom);
    term data = argv[1];

    unsigned char digest[MAX_MD_SIZE];
    size_t digest_len = 0;

    enum crypto_algorithm algo = interop_atom_term_select_int(crypto_algorithm_table, type, ctx->global);
    switch (algo) {
        case CryptoMd5: {
            if (UNLIKELY(!do_md5_hash(data, digest))) {
                RAISE_ERROR(BADARG_ATOM)
            }
            digest_len = 16;
            break;
        }
        case CryptoSha1: {
            if (UNLIKELY(!do_sha1_hash(data, digest))) {
                RAISE_ERROR(BADARG_ATOM)
            }
            digest_len = 20;
            break;
        }
        case CryptoSha224: {
            if (UNLIKELY(!do_sha256_hash_true(data, digest))) {
                RAISE_ERROR(BADARG_ATOM)
            }
            digest_len = 28;
            break;
        }
        case CryptoSha256: {
            if (UNLIKELY(!do_sha256_hash_false(data, digest))) {
                RAISE_ERROR(BADARG_ATOM)
            }
            digest_len = 32;
            break;
        }
        case CryptoSha384: {
            if (UNLIKELY(!do_sha512_hash_true(data, digest))) {
                RAISE_ERROR(BADARG_ATOM)
            }
            digest_len = 48;
            break;
        }
        case CryptoSha512: {
            if (UNLIKELY(!do_sha512_hash_false(data, digest))) {
                RAISE_ERROR(BADARG_ATOM)
            }
            digest_len = 64;
            break;
        }
        default:
            RAISE_ERROR(BADARG_ATOM);
    }

    if (UNLIKELY(memory_ensure_free(ctx, term_binary_heap_size(digest_len)) != MEMORY_GC_OK)) {
        RAISE_ERROR(OUT_OF_MEMORY_ATOM);
    }
    return term_from_literal_binary(digest, digest_len, &ctx->heap, ctx->global);
}

static term nif_atomvm_platform(Context *ctx, int argc, term argv[])
{
    UNUSED(ctx);
    UNUSED(argc);
    UNUSED(argv);
    return ESP32_ATOM;
}

static term nif_esp_get_mac(Context *ctx, int argc, term argv[])
{
    UNUSED(argc);

    GlobalContext *global = ctx->global;

    int network_interface = interop_atom_term_select_int(interface_table, argv[0], global);
    esp_mac_type_t interface;
    switch (network_interface) {
        case WifiSTAInterface:
           interface = ESP_MAC_WIFI_STA;
           break;
        case WifiSoftAPInterface:
           interface = ESP_MAC_WIFI_SOFTAP;
           break;
        default:
            // TODO add support for BT, ETH, etc
            RAISE_ERROR(BADARG_ATOM);
    }

    uint8_t mac[6];
    esp_err_t err = esp_read_mac(mac, interface);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Unable to read mac.  err=%i", err);
        RAISE_ERROR(BADARG_ATOM);
    }

    if (UNLIKELY(memory_ensure_free(ctx, term_binary_heap_size(6)) != MEMORY_GC_OK)) {
        RAISE_ERROR(OUT_OF_MEMORY_ATOM);
    }

    return term_from_literal_binary(mac, 6, &ctx->heap, ctx->global);
}

//
// NIF structures and dispatch
//

static const struct Nif esp_random_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_random
};
static const struct Nif esp_random_bytes_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_random_bytes
};
static const struct Nif esp_restart_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_restart
};
static const struct Nif esp_reset_reason_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_reset_reason
};
static const struct Nif esp_freq_hz_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_freq_hz
};
static const struct Nif esp_partition_erase_range_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_partition_erase_range
};
static const struct Nif esp_partition_write_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_partition_write
};
static const struct Nif esp_partition_list_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_partition_list
};
static const struct Nif esp_deep_sleep_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_deep_sleep
};
static const struct Nif esp_sleep_get_wakeup_cause_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_sleep_get_wakeup_cause
};
#if SOC_PM_SUPPORT_EXT_WAKEUP
static const struct Nif esp_sleep_enable_ext0_wakeup_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_sleep_enable_ext0_wakeup
};
static const struct Nif esp_sleep_enable_ext1_wakeup_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_sleep_enable_ext1_wakeup
};
#endif
static const struct Nif crypto_hash_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_crypto_hash
};
static const struct Nif atomvm_platform_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_atomvm_platform
};
static const struct Nif esp_get_mac_nif =
{
    .base.type = NIFFunctionType,
    .nif_ptr = nif_esp_get_mac
};

const struct Nif *platform_nifs_get_nif(const char *nifname)
{
    if (strcmp("atomvm:random/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_random_nif;
    }
    if (strcmp("atomvm:rand_bytes/1", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_random_bytes_nif;
    }
    if (strcmp("esp:restart/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_restart_nif;
    }
    if (strcmp("esp:reset_reason/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_reset_reason_nif;
    }
    if (strcmp("esp:freq_hz/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_freq_hz_nif;
    }
    if (strcmp("esp:partition_erase_range/2", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_partition_erase_range_nif;
    }
    if (strcmp("esp:partition_erase_range/3", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_partition_erase_range_nif;
    }
    if (strcmp("esp:partition_write/3", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_partition_write_nif;
    }
    if (strcmp("esp:partition_list/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_partition_list_nif;
    }
    if (strcmp("esp:deep_sleep/1", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_deep_sleep_nif;
    }
    if (strcmp("esp:sleep_get_wakeup_cause/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_sleep_get_wakeup_cause_nif;
    }
#if SOC_PM_SUPPORT_EXT_WAKEUP
    if (strcmp("esp:sleep_enable_ext0_wakeup/2", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_sleep_enable_ext0_wakeup_nif;
    }
    if (strcmp("esp:sleep_enable_ext1_wakeup/2", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_sleep_enable_ext1_wakeup_nif;
    }
#endif
    if (strcmp("crypto:hash/2", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &crypto_hash_nif;
    }
    if (strcmp("atomvm:platform/0", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &atomvm_platform_nif;
    }
    if (strcmp("esp:get_mac/1", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &esp_get_mac_nif;
    }
    const struct Nif *nif = nif_collection_resolve_nif(nifname);
    if (nif) {
        return nif;
    }
    return NULL;
}
