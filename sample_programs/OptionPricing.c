
// We need to define _GNU_SOURCE before
// _any_ headers files are imported to get
// the usage statistics of a thread (i.e. have RUSAGE_THREAD) on GNU/Linux
// https://manpages.courier-mta.org/htmlman2/getrusage.2.html
#ifndef _GNU_SOURCE // Avoid possible double-definition warning.
#define _GNU_SOURCE
#endif

#ifdef __clang__
#pragma clang diagnostic ignored "-Wunused-function"
#pragma clang diagnostic ignored "-Wunused-variable"
#pragma clang diagnostic ignored "-Wparentheses"
#pragma clang diagnostic ignored "-Wunused-label"
#elif __GNUC__
#pragma GCC diagnostic ignored "-Wunused-function"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wparentheses"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif

// Headers\n")
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>
#include <float.h>

#ifdef __cplusplus
extern "C" {
#endif

// Initialisation
struct futhark_context_config;
struct futhark_context_config *futhark_context_config_new(void);
void futhark_context_config_free(struct futhark_context_config *cfg);
void futhark_context_config_set_debugging(struct futhark_context_config *cfg,
                                          int flag);
void futhark_context_config_set_profiling(struct futhark_context_config *cfg,
                                          int flag);
void futhark_context_config_set_logging(struct futhark_context_config *cfg,
                                        int flag);
struct futhark_context;
struct futhark_context *futhark_context_new(struct futhark_context_config *cfg);
void futhark_context_free(struct futhark_context *ctx);
int futhark_context_config_set_tuning_param(struct futhark_context_config *cfg,
                                            const char *param_name,
                                            size_t param_value);
int futhark_get_tuning_param_count(void);
const char *futhark_get_tuning_param_name(int);
const char *futhark_get_tuning_param_class(int);

// Arrays
struct futhark_f32_1d;
struct futhark_f32_1d *futhark_new_f32_1d(struct futhark_context *ctx, const
                                          float *data, int64_t dim0);
struct futhark_f32_1d *futhark_new_raw_f32_1d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0);
int futhark_free_f32_1d(struct futhark_context *ctx,
                        struct futhark_f32_1d *arr);
int futhark_values_f32_1d(struct futhark_context *ctx,
                          struct futhark_f32_1d *arr, float *data);
unsigned char *futhark_values_raw_f32_1d(struct futhark_context *ctx,
                                         struct futhark_f32_1d *arr);
const int64_t *futhark_shape_f32_1d(struct futhark_context *ctx,
                                    struct futhark_f32_1d *arr);
struct futhark_f32_2d;
struct futhark_f32_2d *futhark_new_f32_2d(struct futhark_context *ctx, const
                                          float *data, int64_t dim0,
                                          int64_t dim1);
struct futhark_f32_2d *futhark_new_raw_f32_2d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0,
                                              int64_t dim1);
int futhark_free_f32_2d(struct futhark_context *ctx,
                        struct futhark_f32_2d *arr);
int futhark_values_f32_2d(struct futhark_context *ctx,
                          struct futhark_f32_2d *arr, float *data);
unsigned char *futhark_values_raw_f32_2d(struct futhark_context *ctx,
                                         struct futhark_f32_2d *arr);
const int64_t *futhark_shape_f32_2d(struct futhark_context *ctx,
                                    struct futhark_f32_2d *arr);
struct futhark_f32_3d;
struct futhark_f32_3d *futhark_new_f32_3d(struct futhark_context *ctx, const
                                          float *data, int64_t dim0,
                                          int64_t dim1, int64_t dim2);
struct futhark_f32_3d *futhark_new_raw_f32_3d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0,
                                              int64_t dim1, int64_t dim2);
int futhark_free_f32_3d(struct futhark_context *ctx,
                        struct futhark_f32_3d *arr);
int futhark_values_f32_3d(struct futhark_context *ctx,
                          struct futhark_f32_3d *arr, float *data);
unsigned char *futhark_values_raw_f32_3d(struct futhark_context *ctx,
                                         struct futhark_f32_3d *arr);
const int64_t *futhark_shape_f32_3d(struct futhark_context *ctx,
                                    struct futhark_f32_3d *arr);
struct futhark_i32_2d;
struct futhark_i32_2d *futhark_new_i32_2d(struct futhark_context *ctx, const
                                          int32_t *data, int64_t dim0,
                                          int64_t dim1);
struct futhark_i32_2d *futhark_new_raw_i32_2d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0,
                                              int64_t dim1);
int futhark_free_i32_2d(struct futhark_context *ctx,
                        struct futhark_i32_2d *arr);
int futhark_values_i32_2d(struct futhark_context *ctx,
                          struct futhark_i32_2d *arr, int32_t *data);
unsigned char *futhark_values_raw_i32_2d(struct futhark_context *ctx,
                                         struct futhark_i32_2d *arr);
const int64_t *futhark_shape_i32_2d(struct futhark_context *ctx,
                                    struct futhark_i32_2d *arr);

// Opaque values


// Entry points
int futhark_entry_main(struct futhark_context *ctx,
                       struct futhark_f32_1d **out0, const int32_t in0, const
                       int32_t in1, const struct futhark_i32_2d *in2, const
                       struct futhark_f32_3d *in3, const
                       struct futhark_f32_3d *in4, const
                       struct futhark_f32_3d *in5, const
                       struct futhark_f32_2d *in6, const
                       struct futhark_f32_2d *in7, const
                       struct futhark_f32_2d *in8, const
                       struct futhark_i32_2d *in9, const
                       struct futhark_f32_2d *in10);

// Miscellaneous
int futhark_context_sync(struct futhark_context *ctx);
char *futhark_context_report(struct futhark_context *ctx);
char *futhark_context_get_error(struct futhark_context *ctx);
void futhark_context_set_logging_file(struct futhark_context *ctx, FILE *f);
void futhark_context_pause_profiling(struct futhark_context *ctx);
void futhark_context_unpause_profiling(struct futhark_context *ctx);
int futhark_context_clear_caches(struct futhark_context *ctx);
#define FUTHARK_BACKEND_c
#define FUTHARK_SUCCESS 0
#define FUTHARK_PROGRAM_ERROR 2
#define FUTHARK_OUT_OF_MEMORY 3

#ifdef __cplusplus
}
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>
#include <stdint.h>
// If NDEBUG is set, the assert() macro will do nothing. Since Futhark
// (unfortunately) makes use of assert() for error detection (and even some
// side effects), we want to avoid that.
#undef NDEBUG
#include <assert.h>
#include <stdarg.h>
// Start of util.h.
//
// Various helper functions that are useful in all generated C code.

#include <errno.h>
#include <string.h>

static const char *fut_progname = "(embedded Futhark)";

static void futhark_panic(int eval, const char *fmt, ...) __attribute__((noreturn));
static char* msgprintf(const char *s, ...);
static void* slurp_file(const char *filename, size_t *size);
static int dump_file(const char *file, const void *buf, size_t n);
struct str_builder;
static void str_builder_init(struct str_builder *b);
static void str_builder(struct str_builder *b, const char *s, ...);

static void futhark_panic(int eval, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  fprintf(stderr, "%s: ", fut_progname);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  exit(eval);
}

// For generating arbitrary-sized error messages.  It is the callers
// responsibility to free the buffer at some point.
static char* msgprintf(const char *s, ...) {
  va_list vl;
  va_start(vl, s);
  size_t needed = 1 + (size_t)vsnprintf(NULL, 0, s, vl);
  char *buffer = (char*) malloc(needed);
  va_start(vl, s); // Must re-init.
  vsnprintf(buffer, needed, s, vl);
  return buffer;
}

static inline void check_err(int errval, int sets_errno, const char *fun, int line,
                             const char *msg, ...) {
  if (errval) {
    char errnum[10];

    va_list vl;
    va_start(vl, msg);

    fprintf(stderr, "ERROR: ");
    vfprintf(stderr, msg, vl);
    fprintf(stderr, " in %s() at line %d with error code %s\n",
            fun, line,
            sets_errno ? strerror(errno) : errnum);
    exit(errval);
  }
}

#define CHECK_ERR(err, ...) check_err(err, 0, __func__, __LINE__, __VA_ARGS__)
#define CHECK_ERRNO(err, ...) check_err(err, 1, __func__, __LINE__, __VA_ARGS__)

// Read the rest of an open file into a NUL-terminated string; returns
// NULL on error.
static void* fslurp_file(FILE *f, size_t *size) {
  long start = ftell(f);
  fseek(f, 0, SEEK_END);
  long src_size = ftell(f)-start;
  fseek(f, start, SEEK_SET);
  unsigned char *s = (unsigned char*) malloc((size_t)src_size + 1);
  if (fread(s, 1, (size_t)src_size, f) != (size_t)src_size) {
    free(s);
    s = NULL;
  } else {
    s[src_size] = '\0';
  }

  if (size) {
    *size = (size_t)src_size;
  }

  return s;
}

// Read a file into a NUL-terminated string; returns NULL on error.
static void* slurp_file(const char *filename, size_t *size) {
  FILE *f = fopen(filename, "rb"); // To avoid Windows messing with linebreaks.
  if (f == NULL) return NULL;
  unsigned char *s = fslurp_file(f, size);
  fclose(f);
  return s;
}

// Dump 'n' bytes from 'buf' into the file at the designated location.
// Returns 0 on success.
static int dump_file(const char *file, const void *buf, size_t n) {
  FILE *f = fopen(file, "w");

  if (f == NULL) {
    return 1;
  }

  if (fwrite(buf, sizeof(char), n, f) != n) {
    return 1;
  }

  if (fclose(f) != 0) {
    return 1;
  }

  return 0;
}

struct str_builder {
  char *str;
  size_t capacity; // Size of buffer.
  size_t used; // Bytes used, *not* including final zero.
};

static void str_builder_init(struct str_builder *b) {
  b->capacity = 10;
  b->used = 0;
  b->str = malloc(b->capacity);
  b->str[0] = 0;
}

static void str_builder(struct str_builder *b, const char *s, ...) {
  va_list vl;
  va_start(vl, s);
  size_t needed = (size_t)vsnprintf(NULL, 0, s, vl);

  while (b->capacity < b->used + needed + 1) {
    b->capacity *= 2;
    b->str = realloc(b->str, b->capacity);
  }

  va_start(vl, s); // Must re-init.
  vsnprintf(b->str+b->used, b->capacity-b->used, s, vl);
  b->used += needed;
}

static int lexical_realloc(char **error, unsigned char **ptr, size_t *old_size, size_t new_size) {
  unsigned char *new = realloc(*ptr, new_size);
  if (new == NULL) {
    *error = msgprintf("Failed to allocate memory.\nAttempted allocation: %12lld bytes\n",
                       (long long) new_size);
    return FUTHARK_OUT_OF_MEMORY;
  } else {
    *ptr = new;
    *old_size = new_size;
    return FUTHARK_SUCCESS;
  }
}

// End of util.h.
// Start of half.h.

// Conversion functions are from http://half.sourceforge.net/, but
// translated to C.
//
// Copyright (c) 2012-2021 Christian Rau
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

#ifndef __OPENCL_VERSION__
#define __constant
#endif

__constant static const uint16_t base_table[512] = {
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0001, 0x0002, 0x0004, 0x0008, 0x0010, 0x0020, 0x0040, 0x0080, 0x0100,
  0x0200, 0x0400, 0x0800, 0x0C00, 0x1000, 0x1400, 0x1800, 0x1C00, 0x2000, 0x2400, 0x2800, 0x2C00, 0x3000, 0x3400, 0x3800, 0x3C00,
  0x4000, 0x4400, 0x4800, 0x4C00, 0x5000, 0x5400, 0x5800, 0x5C00, 0x6000, 0x6400, 0x6800, 0x6C00, 0x7000, 0x7400, 0x7800, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00, 0x7C00,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000,
  0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8000, 0x8001, 0x8002, 0x8004, 0x8008, 0x8010, 0x8020, 0x8040, 0x8080, 0x8100,
  0x8200, 0x8400, 0x8800, 0x8C00, 0x9000, 0x9400, 0x9800, 0x9C00, 0xA000, 0xA400, 0xA800, 0xAC00, 0xB000, 0xB400, 0xB800, 0xBC00,
  0xC000, 0xC400, 0xC800, 0xCC00, 0xD000, 0xD400, 0xD800, 0xDC00, 0xE000, 0xE400, 0xE800, 0xEC00, 0xF000, 0xF400, 0xF800, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00,
  0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00, 0xFC00 };

__constant static const unsigned char shift_table[512] = {
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 13,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 13 };

__constant static const uint32_t mantissa_table[2048] = {
  0x00000000, 0x33800000, 0x34000000, 0x34400000, 0x34800000, 0x34A00000, 0x34C00000, 0x34E00000, 0x35000000, 0x35100000, 0x35200000, 0x35300000, 0x35400000, 0x35500000, 0x35600000, 0x35700000,
  0x35800000, 0x35880000, 0x35900000, 0x35980000, 0x35A00000, 0x35A80000, 0x35B00000, 0x35B80000, 0x35C00000, 0x35C80000, 0x35D00000, 0x35D80000, 0x35E00000, 0x35E80000, 0x35F00000, 0x35F80000,
  0x36000000, 0x36040000, 0x36080000, 0x360C0000, 0x36100000, 0x36140000, 0x36180000, 0x361C0000, 0x36200000, 0x36240000, 0x36280000, 0x362C0000, 0x36300000, 0x36340000, 0x36380000, 0x363C0000,
  0x36400000, 0x36440000, 0x36480000, 0x364C0000, 0x36500000, 0x36540000, 0x36580000, 0x365C0000, 0x36600000, 0x36640000, 0x36680000, 0x366C0000, 0x36700000, 0x36740000, 0x36780000, 0x367C0000,
  0x36800000, 0x36820000, 0x36840000, 0x36860000, 0x36880000, 0x368A0000, 0x368C0000, 0x368E0000, 0x36900000, 0x36920000, 0x36940000, 0x36960000, 0x36980000, 0x369A0000, 0x369C0000, 0x369E0000,
  0x36A00000, 0x36A20000, 0x36A40000, 0x36A60000, 0x36A80000, 0x36AA0000, 0x36AC0000, 0x36AE0000, 0x36B00000, 0x36B20000, 0x36B40000, 0x36B60000, 0x36B80000, 0x36BA0000, 0x36BC0000, 0x36BE0000,
  0x36C00000, 0x36C20000, 0x36C40000, 0x36C60000, 0x36C80000, 0x36CA0000, 0x36CC0000, 0x36CE0000, 0x36D00000, 0x36D20000, 0x36D40000, 0x36D60000, 0x36D80000, 0x36DA0000, 0x36DC0000, 0x36DE0000,
  0x36E00000, 0x36E20000, 0x36E40000, 0x36E60000, 0x36E80000, 0x36EA0000, 0x36EC0000, 0x36EE0000, 0x36F00000, 0x36F20000, 0x36F40000, 0x36F60000, 0x36F80000, 0x36FA0000, 0x36FC0000, 0x36FE0000,
  0x37000000, 0x37010000, 0x37020000, 0x37030000, 0x37040000, 0x37050000, 0x37060000, 0x37070000, 0x37080000, 0x37090000, 0x370A0000, 0x370B0000, 0x370C0000, 0x370D0000, 0x370E0000, 0x370F0000,
  0x37100000, 0x37110000, 0x37120000, 0x37130000, 0x37140000, 0x37150000, 0x37160000, 0x37170000, 0x37180000, 0x37190000, 0x371A0000, 0x371B0000, 0x371C0000, 0x371D0000, 0x371E0000, 0x371F0000,
  0x37200000, 0x37210000, 0x37220000, 0x37230000, 0x37240000, 0x37250000, 0x37260000, 0x37270000, 0x37280000, 0x37290000, 0x372A0000, 0x372B0000, 0x372C0000, 0x372D0000, 0x372E0000, 0x372F0000,
  0x37300000, 0x37310000, 0x37320000, 0x37330000, 0x37340000, 0x37350000, 0x37360000, 0x37370000, 0x37380000, 0x37390000, 0x373A0000, 0x373B0000, 0x373C0000, 0x373D0000, 0x373E0000, 0x373F0000,
  0x37400000, 0x37410000, 0x37420000, 0x37430000, 0x37440000, 0x37450000, 0x37460000, 0x37470000, 0x37480000, 0x37490000, 0x374A0000, 0x374B0000, 0x374C0000, 0x374D0000, 0x374E0000, 0x374F0000,
  0x37500000, 0x37510000, 0x37520000, 0x37530000, 0x37540000, 0x37550000, 0x37560000, 0x37570000, 0x37580000, 0x37590000, 0x375A0000, 0x375B0000, 0x375C0000, 0x375D0000, 0x375E0000, 0x375F0000,
  0x37600000, 0x37610000, 0x37620000, 0x37630000, 0x37640000, 0x37650000, 0x37660000, 0x37670000, 0x37680000, 0x37690000, 0x376A0000, 0x376B0000, 0x376C0000, 0x376D0000, 0x376E0000, 0x376F0000,
  0x37700000, 0x37710000, 0x37720000, 0x37730000, 0x37740000, 0x37750000, 0x37760000, 0x37770000, 0x37780000, 0x37790000, 0x377A0000, 0x377B0000, 0x377C0000, 0x377D0000, 0x377E0000, 0x377F0000,
  0x37800000, 0x37808000, 0x37810000, 0x37818000, 0x37820000, 0x37828000, 0x37830000, 0x37838000, 0x37840000, 0x37848000, 0x37850000, 0x37858000, 0x37860000, 0x37868000, 0x37870000, 0x37878000,
  0x37880000, 0x37888000, 0x37890000, 0x37898000, 0x378A0000, 0x378A8000, 0x378B0000, 0x378B8000, 0x378C0000, 0x378C8000, 0x378D0000, 0x378D8000, 0x378E0000, 0x378E8000, 0x378F0000, 0x378F8000,
  0x37900000, 0x37908000, 0x37910000, 0x37918000, 0x37920000, 0x37928000, 0x37930000, 0x37938000, 0x37940000, 0x37948000, 0x37950000, 0x37958000, 0x37960000, 0x37968000, 0x37970000, 0x37978000,
  0x37980000, 0x37988000, 0x37990000, 0x37998000, 0x379A0000, 0x379A8000, 0x379B0000, 0x379B8000, 0x379C0000, 0x379C8000, 0x379D0000, 0x379D8000, 0x379E0000, 0x379E8000, 0x379F0000, 0x379F8000,
  0x37A00000, 0x37A08000, 0x37A10000, 0x37A18000, 0x37A20000, 0x37A28000, 0x37A30000, 0x37A38000, 0x37A40000, 0x37A48000, 0x37A50000, 0x37A58000, 0x37A60000, 0x37A68000, 0x37A70000, 0x37A78000,
  0x37A80000, 0x37A88000, 0x37A90000, 0x37A98000, 0x37AA0000, 0x37AA8000, 0x37AB0000, 0x37AB8000, 0x37AC0000, 0x37AC8000, 0x37AD0000, 0x37AD8000, 0x37AE0000, 0x37AE8000, 0x37AF0000, 0x37AF8000,
  0x37B00000, 0x37B08000, 0x37B10000, 0x37B18000, 0x37B20000, 0x37B28000, 0x37B30000, 0x37B38000, 0x37B40000, 0x37B48000, 0x37B50000, 0x37B58000, 0x37B60000, 0x37B68000, 0x37B70000, 0x37B78000,
  0x37B80000, 0x37B88000, 0x37B90000, 0x37B98000, 0x37BA0000, 0x37BA8000, 0x37BB0000, 0x37BB8000, 0x37BC0000, 0x37BC8000, 0x37BD0000, 0x37BD8000, 0x37BE0000, 0x37BE8000, 0x37BF0000, 0x37BF8000,
  0x37C00000, 0x37C08000, 0x37C10000, 0x37C18000, 0x37C20000, 0x37C28000, 0x37C30000, 0x37C38000, 0x37C40000, 0x37C48000, 0x37C50000, 0x37C58000, 0x37C60000, 0x37C68000, 0x37C70000, 0x37C78000,
  0x37C80000, 0x37C88000, 0x37C90000, 0x37C98000, 0x37CA0000, 0x37CA8000, 0x37CB0000, 0x37CB8000, 0x37CC0000, 0x37CC8000, 0x37CD0000, 0x37CD8000, 0x37CE0000, 0x37CE8000, 0x37CF0000, 0x37CF8000,
  0x37D00000, 0x37D08000, 0x37D10000, 0x37D18000, 0x37D20000, 0x37D28000, 0x37D30000, 0x37D38000, 0x37D40000, 0x37D48000, 0x37D50000, 0x37D58000, 0x37D60000, 0x37D68000, 0x37D70000, 0x37D78000,
  0x37D80000, 0x37D88000, 0x37D90000, 0x37D98000, 0x37DA0000, 0x37DA8000, 0x37DB0000, 0x37DB8000, 0x37DC0000, 0x37DC8000, 0x37DD0000, 0x37DD8000, 0x37DE0000, 0x37DE8000, 0x37DF0000, 0x37DF8000,
  0x37E00000, 0x37E08000, 0x37E10000, 0x37E18000, 0x37E20000, 0x37E28000, 0x37E30000, 0x37E38000, 0x37E40000, 0x37E48000, 0x37E50000, 0x37E58000, 0x37E60000, 0x37E68000, 0x37E70000, 0x37E78000,
  0x37E80000, 0x37E88000, 0x37E90000, 0x37E98000, 0x37EA0000, 0x37EA8000, 0x37EB0000, 0x37EB8000, 0x37EC0000, 0x37EC8000, 0x37ED0000, 0x37ED8000, 0x37EE0000, 0x37EE8000, 0x37EF0000, 0x37EF8000,
  0x37F00000, 0x37F08000, 0x37F10000, 0x37F18000, 0x37F20000, 0x37F28000, 0x37F30000, 0x37F38000, 0x37F40000, 0x37F48000, 0x37F50000, 0x37F58000, 0x37F60000, 0x37F68000, 0x37F70000, 0x37F78000,
  0x37F80000, 0x37F88000, 0x37F90000, 0x37F98000, 0x37FA0000, 0x37FA8000, 0x37FB0000, 0x37FB8000, 0x37FC0000, 0x37FC8000, 0x37FD0000, 0x37FD8000, 0x37FE0000, 0x37FE8000, 0x37FF0000, 0x37FF8000,
  0x38000000, 0x38004000, 0x38008000, 0x3800C000, 0x38010000, 0x38014000, 0x38018000, 0x3801C000, 0x38020000, 0x38024000, 0x38028000, 0x3802C000, 0x38030000, 0x38034000, 0x38038000, 0x3803C000,
  0x38040000, 0x38044000, 0x38048000, 0x3804C000, 0x38050000, 0x38054000, 0x38058000, 0x3805C000, 0x38060000, 0x38064000, 0x38068000, 0x3806C000, 0x38070000, 0x38074000, 0x38078000, 0x3807C000,
  0x38080000, 0x38084000, 0x38088000, 0x3808C000, 0x38090000, 0x38094000, 0x38098000, 0x3809C000, 0x380A0000, 0x380A4000, 0x380A8000, 0x380AC000, 0x380B0000, 0x380B4000, 0x380B8000, 0x380BC000,
  0x380C0000, 0x380C4000, 0x380C8000, 0x380CC000, 0x380D0000, 0x380D4000, 0x380D8000, 0x380DC000, 0x380E0000, 0x380E4000, 0x380E8000, 0x380EC000, 0x380F0000, 0x380F4000, 0x380F8000, 0x380FC000,
  0x38100000, 0x38104000, 0x38108000, 0x3810C000, 0x38110000, 0x38114000, 0x38118000, 0x3811C000, 0x38120000, 0x38124000, 0x38128000, 0x3812C000, 0x38130000, 0x38134000, 0x38138000, 0x3813C000,
  0x38140000, 0x38144000, 0x38148000, 0x3814C000, 0x38150000, 0x38154000, 0x38158000, 0x3815C000, 0x38160000, 0x38164000, 0x38168000, 0x3816C000, 0x38170000, 0x38174000, 0x38178000, 0x3817C000,
  0x38180000, 0x38184000, 0x38188000, 0x3818C000, 0x38190000, 0x38194000, 0x38198000, 0x3819C000, 0x381A0000, 0x381A4000, 0x381A8000, 0x381AC000, 0x381B0000, 0x381B4000, 0x381B8000, 0x381BC000,
  0x381C0000, 0x381C4000, 0x381C8000, 0x381CC000, 0x381D0000, 0x381D4000, 0x381D8000, 0x381DC000, 0x381E0000, 0x381E4000, 0x381E8000, 0x381EC000, 0x381F0000, 0x381F4000, 0x381F8000, 0x381FC000,
  0x38200000, 0x38204000, 0x38208000, 0x3820C000, 0x38210000, 0x38214000, 0x38218000, 0x3821C000, 0x38220000, 0x38224000, 0x38228000, 0x3822C000, 0x38230000, 0x38234000, 0x38238000, 0x3823C000,
  0x38240000, 0x38244000, 0x38248000, 0x3824C000, 0x38250000, 0x38254000, 0x38258000, 0x3825C000, 0x38260000, 0x38264000, 0x38268000, 0x3826C000, 0x38270000, 0x38274000, 0x38278000, 0x3827C000,
  0x38280000, 0x38284000, 0x38288000, 0x3828C000, 0x38290000, 0x38294000, 0x38298000, 0x3829C000, 0x382A0000, 0x382A4000, 0x382A8000, 0x382AC000, 0x382B0000, 0x382B4000, 0x382B8000, 0x382BC000,
  0x382C0000, 0x382C4000, 0x382C8000, 0x382CC000, 0x382D0000, 0x382D4000, 0x382D8000, 0x382DC000, 0x382E0000, 0x382E4000, 0x382E8000, 0x382EC000, 0x382F0000, 0x382F4000, 0x382F8000, 0x382FC000,
  0x38300000, 0x38304000, 0x38308000, 0x3830C000, 0x38310000, 0x38314000, 0x38318000, 0x3831C000, 0x38320000, 0x38324000, 0x38328000, 0x3832C000, 0x38330000, 0x38334000, 0x38338000, 0x3833C000,
  0x38340000, 0x38344000, 0x38348000, 0x3834C000, 0x38350000, 0x38354000, 0x38358000, 0x3835C000, 0x38360000, 0x38364000, 0x38368000, 0x3836C000, 0x38370000, 0x38374000, 0x38378000, 0x3837C000,
  0x38380000, 0x38384000, 0x38388000, 0x3838C000, 0x38390000, 0x38394000, 0x38398000, 0x3839C000, 0x383A0000, 0x383A4000, 0x383A8000, 0x383AC000, 0x383B0000, 0x383B4000, 0x383B8000, 0x383BC000,
  0x383C0000, 0x383C4000, 0x383C8000, 0x383CC000, 0x383D0000, 0x383D4000, 0x383D8000, 0x383DC000, 0x383E0000, 0x383E4000, 0x383E8000, 0x383EC000, 0x383F0000, 0x383F4000, 0x383F8000, 0x383FC000,
  0x38400000, 0x38404000, 0x38408000, 0x3840C000, 0x38410000, 0x38414000, 0x38418000, 0x3841C000, 0x38420000, 0x38424000, 0x38428000, 0x3842C000, 0x38430000, 0x38434000, 0x38438000, 0x3843C000,
  0x38440000, 0x38444000, 0x38448000, 0x3844C000, 0x38450000, 0x38454000, 0x38458000, 0x3845C000, 0x38460000, 0x38464000, 0x38468000, 0x3846C000, 0x38470000, 0x38474000, 0x38478000, 0x3847C000,
  0x38480000, 0x38484000, 0x38488000, 0x3848C000, 0x38490000, 0x38494000, 0x38498000, 0x3849C000, 0x384A0000, 0x384A4000, 0x384A8000, 0x384AC000, 0x384B0000, 0x384B4000, 0x384B8000, 0x384BC000,
  0x384C0000, 0x384C4000, 0x384C8000, 0x384CC000, 0x384D0000, 0x384D4000, 0x384D8000, 0x384DC000, 0x384E0000, 0x384E4000, 0x384E8000, 0x384EC000, 0x384F0000, 0x384F4000, 0x384F8000, 0x384FC000,
  0x38500000, 0x38504000, 0x38508000, 0x3850C000, 0x38510000, 0x38514000, 0x38518000, 0x3851C000, 0x38520000, 0x38524000, 0x38528000, 0x3852C000, 0x38530000, 0x38534000, 0x38538000, 0x3853C000,
  0x38540000, 0x38544000, 0x38548000, 0x3854C000, 0x38550000, 0x38554000, 0x38558000, 0x3855C000, 0x38560000, 0x38564000, 0x38568000, 0x3856C000, 0x38570000, 0x38574000, 0x38578000, 0x3857C000,
  0x38580000, 0x38584000, 0x38588000, 0x3858C000, 0x38590000, 0x38594000, 0x38598000, 0x3859C000, 0x385A0000, 0x385A4000, 0x385A8000, 0x385AC000, 0x385B0000, 0x385B4000, 0x385B8000, 0x385BC000,
  0x385C0000, 0x385C4000, 0x385C8000, 0x385CC000, 0x385D0000, 0x385D4000, 0x385D8000, 0x385DC000, 0x385E0000, 0x385E4000, 0x385E8000, 0x385EC000, 0x385F0000, 0x385F4000, 0x385F8000, 0x385FC000,
  0x38600000, 0x38604000, 0x38608000, 0x3860C000, 0x38610000, 0x38614000, 0x38618000, 0x3861C000, 0x38620000, 0x38624000, 0x38628000, 0x3862C000, 0x38630000, 0x38634000, 0x38638000, 0x3863C000,
  0x38640000, 0x38644000, 0x38648000, 0x3864C000, 0x38650000, 0x38654000, 0x38658000, 0x3865C000, 0x38660000, 0x38664000, 0x38668000, 0x3866C000, 0x38670000, 0x38674000, 0x38678000, 0x3867C000,
  0x38680000, 0x38684000, 0x38688000, 0x3868C000, 0x38690000, 0x38694000, 0x38698000, 0x3869C000, 0x386A0000, 0x386A4000, 0x386A8000, 0x386AC000, 0x386B0000, 0x386B4000, 0x386B8000, 0x386BC000,
  0x386C0000, 0x386C4000, 0x386C8000, 0x386CC000, 0x386D0000, 0x386D4000, 0x386D8000, 0x386DC000, 0x386E0000, 0x386E4000, 0x386E8000, 0x386EC000, 0x386F0000, 0x386F4000, 0x386F8000, 0x386FC000,
  0x38700000, 0x38704000, 0x38708000, 0x3870C000, 0x38710000, 0x38714000, 0x38718000, 0x3871C000, 0x38720000, 0x38724000, 0x38728000, 0x3872C000, 0x38730000, 0x38734000, 0x38738000, 0x3873C000,
  0x38740000, 0x38744000, 0x38748000, 0x3874C000, 0x38750000, 0x38754000, 0x38758000, 0x3875C000, 0x38760000, 0x38764000, 0x38768000, 0x3876C000, 0x38770000, 0x38774000, 0x38778000, 0x3877C000,
  0x38780000, 0x38784000, 0x38788000, 0x3878C000, 0x38790000, 0x38794000, 0x38798000, 0x3879C000, 0x387A0000, 0x387A4000, 0x387A8000, 0x387AC000, 0x387B0000, 0x387B4000, 0x387B8000, 0x387BC000,
  0x387C0000, 0x387C4000, 0x387C8000, 0x387CC000, 0x387D0000, 0x387D4000, 0x387D8000, 0x387DC000, 0x387E0000, 0x387E4000, 0x387E8000, 0x387EC000, 0x387F0000, 0x387F4000, 0x387F8000, 0x387FC000,
  0x38000000, 0x38002000, 0x38004000, 0x38006000, 0x38008000, 0x3800A000, 0x3800C000, 0x3800E000, 0x38010000, 0x38012000, 0x38014000, 0x38016000, 0x38018000, 0x3801A000, 0x3801C000, 0x3801E000,
  0x38020000, 0x38022000, 0x38024000, 0x38026000, 0x38028000, 0x3802A000, 0x3802C000, 0x3802E000, 0x38030000, 0x38032000, 0x38034000, 0x38036000, 0x38038000, 0x3803A000, 0x3803C000, 0x3803E000,
  0x38040000, 0x38042000, 0x38044000, 0x38046000, 0x38048000, 0x3804A000, 0x3804C000, 0x3804E000, 0x38050000, 0x38052000, 0x38054000, 0x38056000, 0x38058000, 0x3805A000, 0x3805C000, 0x3805E000,
  0x38060000, 0x38062000, 0x38064000, 0x38066000, 0x38068000, 0x3806A000, 0x3806C000, 0x3806E000, 0x38070000, 0x38072000, 0x38074000, 0x38076000, 0x38078000, 0x3807A000, 0x3807C000, 0x3807E000,
  0x38080000, 0x38082000, 0x38084000, 0x38086000, 0x38088000, 0x3808A000, 0x3808C000, 0x3808E000, 0x38090000, 0x38092000, 0x38094000, 0x38096000, 0x38098000, 0x3809A000, 0x3809C000, 0x3809E000,
  0x380A0000, 0x380A2000, 0x380A4000, 0x380A6000, 0x380A8000, 0x380AA000, 0x380AC000, 0x380AE000, 0x380B0000, 0x380B2000, 0x380B4000, 0x380B6000, 0x380B8000, 0x380BA000, 0x380BC000, 0x380BE000,
  0x380C0000, 0x380C2000, 0x380C4000, 0x380C6000, 0x380C8000, 0x380CA000, 0x380CC000, 0x380CE000, 0x380D0000, 0x380D2000, 0x380D4000, 0x380D6000, 0x380D8000, 0x380DA000, 0x380DC000, 0x380DE000,
  0x380E0000, 0x380E2000, 0x380E4000, 0x380E6000, 0x380E8000, 0x380EA000, 0x380EC000, 0x380EE000, 0x380F0000, 0x380F2000, 0x380F4000, 0x380F6000, 0x380F8000, 0x380FA000, 0x380FC000, 0x380FE000,
  0x38100000, 0x38102000, 0x38104000, 0x38106000, 0x38108000, 0x3810A000, 0x3810C000, 0x3810E000, 0x38110000, 0x38112000, 0x38114000, 0x38116000, 0x38118000, 0x3811A000, 0x3811C000, 0x3811E000,
  0x38120000, 0x38122000, 0x38124000, 0x38126000, 0x38128000, 0x3812A000, 0x3812C000, 0x3812E000, 0x38130000, 0x38132000, 0x38134000, 0x38136000, 0x38138000, 0x3813A000, 0x3813C000, 0x3813E000,
  0x38140000, 0x38142000, 0x38144000, 0x38146000, 0x38148000, 0x3814A000, 0x3814C000, 0x3814E000, 0x38150000, 0x38152000, 0x38154000, 0x38156000, 0x38158000, 0x3815A000, 0x3815C000, 0x3815E000,
  0x38160000, 0x38162000, 0x38164000, 0x38166000, 0x38168000, 0x3816A000, 0x3816C000, 0x3816E000, 0x38170000, 0x38172000, 0x38174000, 0x38176000, 0x38178000, 0x3817A000, 0x3817C000, 0x3817E000,
  0x38180000, 0x38182000, 0x38184000, 0x38186000, 0x38188000, 0x3818A000, 0x3818C000, 0x3818E000, 0x38190000, 0x38192000, 0x38194000, 0x38196000, 0x38198000, 0x3819A000, 0x3819C000, 0x3819E000,
  0x381A0000, 0x381A2000, 0x381A4000, 0x381A6000, 0x381A8000, 0x381AA000, 0x381AC000, 0x381AE000, 0x381B0000, 0x381B2000, 0x381B4000, 0x381B6000, 0x381B8000, 0x381BA000, 0x381BC000, 0x381BE000,
  0x381C0000, 0x381C2000, 0x381C4000, 0x381C6000, 0x381C8000, 0x381CA000, 0x381CC000, 0x381CE000, 0x381D0000, 0x381D2000, 0x381D4000, 0x381D6000, 0x381D8000, 0x381DA000, 0x381DC000, 0x381DE000,
  0x381E0000, 0x381E2000, 0x381E4000, 0x381E6000, 0x381E8000, 0x381EA000, 0x381EC000, 0x381EE000, 0x381F0000, 0x381F2000, 0x381F4000, 0x381F6000, 0x381F8000, 0x381FA000, 0x381FC000, 0x381FE000,
  0x38200000, 0x38202000, 0x38204000, 0x38206000, 0x38208000, 0x3820A000, 0x3820C000, 0x3820E000, 0x38210000, 0x38212000, 0x38214000, 0x38216000, 0x38218000, 0x3821A000, 0x3821C000, 0x3821E000,
  0x38220000, 0x38222000, 0x38224000, 0x38226000, 0x38228000, 0x3822A000, 0x3822C000, 0x3822E000, 0x38230000, 0x38232000, 0x38234000, 0x38236000, 0x38238000, 0x3823A000, 0x3823C000, 0x3823E000,
  0x38240000, 0x38242000, 0x38244000, 0x38246000, 0x38248000, 0x3824A000, 0x3824C000, 0x3824E000, 0x38250000, 0x38252000, 0x38254000, 0x38256000, 0x38258000, 0x3825A000, 0x3825C000, 0x3825E000,
  0x38260000, 0x38262000, 0x38264000, 0x38266000, 0x38268000, 0x3826A000, 0x3826C000, 0x3826E000, 0x38270000, 0x38272000, 0x38274000, 0x38276000, 0x38278000, 0x3827A000, 0x3827C000, 0x3827E000,
  0x38280000, 0x38282000, 0x38284000, 0x38286000, 0x38288000, 0x3828A000, 0x3828C000, 0x3828E000, 0x38290000, 0x38292000, 0x38294000, 0x38296000, 0x38298000, 0x3829A000, 0x3829C000, 0x3829E000,
  0x382A0000, 0x382A2000, 0x382A4000, 0x382A6000, 0x382A8000, 0x382AA000, 0x382AC000, 0x382AE000, 0x382B0000, 0x382B2000, 0x382B4000, 0x382B6000, 0x382B8000, 0x382BA000, 0x382BC000, 0x382BE000,
  0x382C0000, 0x382C2000, 0x382C4000, 0x382C6000, 0x382C8000, 0x382CA000, 0x382CC000, 0x382CE000, 0x382D0000, 0x382D2000, 0x382D4000, 0x382D6000, 0x382D8000, 0x382DA000, 0x382DC000, 0x382DE000,
  0x382E0000, 0x382E2000, 0x382E4000, 0x382E6000, 0x382E8000, 0x382EA000, 0x382EC000, 0x382EE000, 0x382F0000, 0x382F2000, 0x382F4000, 0x382F6000, 0x382F8000, 0x382FA000, 0x382FC000, 0x382FE000,
  0x38300000, 0x38302000, 0x38304000, 0x38306000, 0x38308000, 0x3830A000, 0x3830C000, 0x3830E000, 0x38310000, 0x38312000, 0x38314000, 0x38316000, 0x38318000, 0x3831A000, 0x3831C000, 0x3831E000,
  0x38320000, 0x38322000, 0x38324000, 0x38326000, 0x38328000, 0x3832A000, 0x3832C000, 0x3832E000, 0x38330000, 0x38332000, 0x38334000, 0x38336000, 0x38338000, 0x3833A000, 0x3833C000, 0x3833E000,
  0x38340000, 0x38342000, 0x38344000, 0x38346000, 0x38348000, 0x3834A000, 0x3834C000, 0x3834E000, 0x38350000, 0x38352000, 0x38354000, 0x38356000, 0x38358000, 0x3835A000, 0x3835C000, 0x3835E000,
  0x38360000, 0x38362000, 0x38364000, 0x38366000, 0x38368000, 0x3836A000, 0x3836C000, 0x3836E000, 0x38370000, 0x38372000, 0x38374000, 0x38376000, 0x38378000, 0x3837A000, 0x3837C000, 0x3837E000,
  0x38380000, 0x38382000, 0x38384000, 0x38386000, 0x38388000, 0x3838A000, 0x3838C000, 0x3838E000, 0x38390000, 0x38392000, 0x38394000, 0x38396000, 0x38398000, 0x3839A000, 0x3839C000, 0x3839E000,
  0x383A0000, 0x383A2000, 0x383A4000, 0x383A6000, 0x383A8000, 0x383AA000, 0x383AC000, 0x383AE000, 0x383B0000, 0x383B2000, 0x383B4000, 0x383B6000, 0x383B8000, 0x383BA000, 0x383BC000, 0x383BE000,
  0x383C0000, 0x383C2000, 0x383C4000, 0x383C6000, 0x383C8000, 0x383CA000, 0x383CC000, 0x383CE000, 0x383D0000, 0x383D2000, 0x383D4000, 0x383D6000, 0x383D8000, 0x383DA000, 0x383DC000, 0x383DE000,
  0x383E0000, 0x383E2000, 0x383E4000, 0x383E6000, 0x383E8000, 0x383EA000, 0x383EC000, 0x383EE000, 0x383F0000, 0x383F2000, 0x383F4000, 0x383F6000, 0x383F8000, 0x383FA000, 0x383FC000, 0x383FE000,
  0x38400000, 0x38402000, 0x38404000, 0x38406000, 0x38408000, 0x3840A000, 0x3840C000, 0x3840E000, 0x38410000, 0x38412000, 0x38414000, 0x38416000, 0x38418000, 0x3841A000, 0x3841C000, 0x3841E000,
  0x38420000, 0x38422000, 0x38424000, 0x38426000, 0x38428000, 0x3842A000, 0x3842C000, 0x3842E000, 0x38430000, 0x38432000, 0x38434000, 0x38436000, 0x38438000, 0x3843A000, 0x3843C000, 0x3843E000,
  0x38440000, 0x38442000, 0x38444000, 0x38446000, 0x38448000, 0x3844A000, 0x3844C000, 0x3844E000, 0x38450000, 0x38452000, 0x38454000, 0x38456000, 0x38458000, 0x3845A000, 0x3845C000, 0x3845E000,
  0x38460000, 0x38462000, 0x38464000, 0x38466000, 0x38468000, 0x3846A000, 0x3846C000, 0x3846E000, 0x38470000, 0x38472000, 0x38474000, 0x38476000, 0x38478000, 0x3847A000, 0x3847C000, 0x3847E000,
  0x38480000, 0x38482000, 0x38484000, 0x38486000, 0x38488000, 0x3848A000, 0x3848C000, 0x3848E000, 0x38490000, 0x38492000, 0x38494000, 0x38496000, 0x38498000, 0x3849A000, 0x3849C000, 0x3849E000,
  0x384A0000, 0x384A2000, 0x384A4000, 0x384A6000, 0x384A8000, 0x384AA000, 0x384AC000, 0x384AE000, 0x384B0000, 0x384B2000, 0x384B4000, 0x384B6000, 0x384B8000, 0x384BA000, 0x384BC000, 0x384BE000,
  0x384C0000, 0x384C2000, 0x384C4000, 0x384C6000, 0x384C8000, 0x384CA000, 0x384CC000, 0x384CE000, 0x384D0000, 0x384D2000, 0x384D4000, 0x384D6000, 0x384D8000, 0x384DA000, 0x384DC000, 0x384DE000,
  0x384E0000, 0x384E2000, 0x384E4000, 0x384E6000, 0x384E8000, 0x384EA000, 0x384EC000, 0x384EE000, 0x384F0000, 0x384F2000, 0x384F4000, 0x384F6000, 0x384F8000, 0x384FA000, 0x384FC000, 0x384FE000,
  0x38500000, 0x38502000, 0x38504000, 0x38506000, 0x38508000, 0x3850A000, 0x3850C000, 0x3850E000, 0x38510000, 0x38512000, 0x38514000, 0x38516000, 0x38518000, 0x3851A000, 0x3851C000, 0x3851E000,
  0x38520000, 0x38522000, 0x38524000, 0x38526000, 0x38528000, 0x3852A000, 0x3852C000, 0x3852E000, 0x38530000, 0x38532000, 0x38534000, 0x38536000, 0x38538000, 0x3853A000, 0x3853C000, 0x3853E000,
  0x38540000, 0x38542000, 0x38544000, 0x38546000, 0x38548000, 0x3854A000, 0x3854C000, 0x3854E000, 0x38550000, 0x38552000, 0x38554000, 0x38556000, 0x38558000, 0x3855A000, 0x3855C000, 0x3855E000,
  0x38560000, 0x38562000, 0x38564000, 0x38566000, 0x38568000, 0x3856A000, 0x3856C000, 0x3856E000, 0x38570000, 0x38572000, 0x38574000, 0x38576000, 0x38578000, 0x3857A000, 0x3857C000, 0x3857E000,
  0x38580000, 0x38582000, 0x38584000, 0x38586000, 0x38588000, 0x3858A000, 0x3858C000, 0x3858E000, 0x38590000, 0x38592000, 0x38594000, 0x38596000, 0x38598000, 0x3859A000, 0x3859C000, 0x3859E000,
  0x385A0000, 0x385A2000, 0x385A4000, 0x385A6000, 0x385A8000, 0x385AA000, 0x385AC000, 0x385AE000, 0x385B0000, 0x385B2000, 0x385B4000, 0x385B6000, 0x385B8000, 0x385BA000, 0x385BC000, 0x385BE000,
  0x385C0000, 0x385C2000, 0x385C4000, 0x385C6000, 0x385C8000, 0x385CA000, 0x385CC000, 0x385CE000, 0x385D0000, 0x385D2000, 0x385D4000, 0x385D6000, 0x385D8000, 0x385DA000, 0x385DC000, 0x385DE000,
  0x385E0000, 0x385E2000, 0x385E4000, 0x385E6000, 0x385E8000, 0x385EA000, 0x385EC000, 0x385EE000, 0x385F0000, 0x385F2000, 0x385F4000, 0x385F6000, 0x385F8000, 0x385FA000, 0x385FC000, 0x385FE000,
  0x38600000, 0x38602000, 0x38604000, 0x38606000, 0x38608000, 0x3860A000, 0x3860C000, 0x3860E000, 0x38610000, 0x38612000, 0x38614000, 0x38616000, 0x38618000, 0x3861A000, 0x3861C000, 0x3861E000,
  0x38620000, 0x38622000, 0x38624000, 0x38626000, 0x38628000, 0x3862A000, 0x3862C000, 0x3862E000, 0x38630000, 0x38632000, 0x38634000, 0x38636000, 0x38638000, 0x3863A000, 0x3863C000, 0x3863E000,
  0x38640000, 0x38642000, 0x38644000, 0x38646000, 0x38648000, 0x3864A000, 0x3864C000, 0x3864E000, 0x38650000, 0x38652000, 0x38654000, 0x38656000, 0x38658000, 0x3865A000, 0x3865C000, 0x3865E000,
  0x38660000, 0x38662000, 0x38664000, 0x38666000, 0x38668000, 0x3866A000, 0x3866C000, 0x3866E000, 0x38670000, 0x38672000, 0x38674000, 0x38676000, 0x38678000, 0x3867A000, 0x3867C000, 0x3867E000,
  0x38680000, 0x38682000, 0x38684000, 0x38686000, 0x38688000, 0x3868A000, 0x3868C000, 0x3868E000, 0x38690000, 0x38692000, 0x38694000, 0x38696000, 0x38698000, 0x3869A000, 0x3869C000, 0x3869E000,
  0x386A0000, 0x386A2000, 0x386A4000, 0x386A6000, 0x386A8000, 0x386AA000, 0x386AC000, 0x386AE000, 0x386B0000, 0x386B2000, 0x386B4000, 0x386B6000, 0x386B8000, 0x386BA000, 0x386BC000, 0x386BE000,
  0x386C0000, 0x386C2000, 0x386C4000, 0x386C6000, 0x386C8000, 0x386CA000, 0x386CC000, 0x386CE000, 0x386D0000, 0x386D2000, 0x386D4000, 0x386D6000, 0x386D8000, 0x386DA000, 0x386DC000, 0x386DE000,
  0x386E0000, 0x386E2000, 0x386E4000, 0x386E6000, 0x386E8000, 0x386EA000, 0x386EC000, 0x386EE000, 0x386F0000, 0x386F2000, 0x386F4000, 0x386F6000, 0x386F8000, 0x386FA000, 0x386FC000, 0x386FE000,
  0x38700000, 0x38702000, 0x38704000, 0x38706000, 0x38708000, 0x3870A000, 0x3870C000, 0x3870E000, 0x38710000, 0x38712000, 0x38714000, 0x38716000, 0x38718000, 0x3871A000, 0x3871C000, 0x3871E000,
  0x38720000, 0x38722000, 0x38724000, 0x38726000, 0x38728000, 0x3872A000, 0x3872C000, 0x3872E000, 0x38730000, 0x38732000, 0x38734000, 0x38736000, 0x38738000, 0x3873A000, 0x3873C000, 0x3873E000,
  0x38740000, 0x38742000, 0x38744000, 0x38746000, 0x38748000, 0x3874A000, 0x3874C000, 0x3874E000, 0x38750000, 0x38752000, 0x38754000, 0x38756000, 0x38758000, 0x3875A000, 0x3875C000, 0x3875E000,
  0x38760000, 0x38762000, 0x38764000, 0x38766000, 0x38768000, 0x3876A000, 0x3876C000, 0x3876E000, 0x38770000, 0x38772000, 0x38774000, 0x38776000, 0x38778000, 0x3877A000, 0x3877C000, 0x3877E000,
  0x38780000, 0x38782000, 0x38784000, 0x38786000, 0x38788000, 0x3878A000, 0x3878C000, 0x3878E000, 0x38790000, 0x38792000, 0x38794000, 0x38796000, 0x38798000, 0x3879A000, 0x3879C000, 0x3879E000,
  0x387A0000, 0x387A2000, 0x387A4000, 0x387A6000, 0x387A8000, 0x387AA000, 0x387AC000, 0x387AE000, 0x387B0000, 0x387B2000, 0x387B4000, 0x387B6000, 0x387B8000, 0x387BA000, 0x387BC000, 0x387BE000,
  0x387C0000, 0x387C2000, 0x387C4000, 0x387C6000, 0x387C8000, 0x387CA000, 0x387CC000, 0x387CE000, 0x387D0000, 0x387D2000, 0x387D4000, 0x387D6000, 0x387D8000, 0x387DA000, 0x387DC000, 0x387DE000,
  0x387E0000, 0x387E2000, 0x387E4000, 0x387E6000, 0x387E8000, 0x387EA000, 0x387EC000, 0x387EE000, 0x387F0000, 0x387F2000, 0x387F4000, 0x387F6000, 0x387F8000, 0x387FA000, 0x387FC000, 0x387FE000 };
__constant static const uint32_t exponent_table[64] = {
  0x00000000, 0x00800000, 0x01000000, 0x01800000, 0x02000000, 0x02800000, 0x03000000, 0x03800000, 0x04000000, 0x04800000, 0x05000000, 0x05800000, 0x06000000, 0x06800000, 0x07000000, 0x07800000,
  0x08000000, 0x08800000, 0x09000000, 0x09800000, 0x0A000000, 0x0A800000, 0x0B000000, 0x0B800000, 0x0C000000, 0x0C800000, 0x0D000000, 0x0D800000, 0x0E000000, 0x0E800000, 0x0F000000, 0x47800000,
  0x80000000, 0x80800000, 0x81000000, 0x81800000, 0x82000000, 0x82800000, 0x83000000, 0x83800000, 0x84000000, 0x84800000, 0x85000000, 0x85800000, 0x86000000, 0x86800000, 0x87000000, 0x87800000,
  0x88000000, 0x88800000, 0x89000000, 0x89800000, 0x8A000000, 0x8A800000, 0x8B000000, 0x8B800000, 0x8C000000, 0x8C800000, 0x8D000000, 0x8D800000, 0x8E000000, 0x8E800000, 0x8F000000, 0xC7800000 };
__constant static const unsigned short offset_table[64] = {
  0, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024,
  0, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024 };

static uint16_t float2halfbits(float value) {
  union { float x; uint32_t y; } u;
  u.x = value;
  uint32_t bits = u.y;

  uint16_t hbits = base_table[bits>>23] + (uint16_t)((bits&0x7FFFFF)>>shift_table[bits>>23]);;

  return hbits;
}

static float halfbits2float(uint16_t value) {
  uint32_t bits = mantissa_table[offset_table[value>>10]+(value&0x3FF)] + exponent_table[value>>10];

  union { uint32_t x; float y; } u;
  u.x = bits;
  return u.y;
}

// End of half.h.
// Start of timing.h.

// The function get_wall_time() returns the wall time in microseconds
// (with an unspecified offset).

#ifdef _WIN32

#include <windows.h>

static int64_t get_wall_time(void) {
  LARGE_INTEGER time,freq;
  assert(QueryPerformanceFrequency(&freq));
  assert(QueryPerformanceCounter(&time));
  return ((double)time.QuadPart / freq.QuadPart) * 1000000;
}

#else
// Assuming POSIX

#include <time.h>
#include <sys/time.h>

static int64_t get_wall_time(void) {
  struct timeval time;
  assert(gettimeofday(&time,NULL) == 0);
  return time.tv_sec * 1000000 + time.tv_usec;
}

static int64_t get_wall_time_ns(void) {
  struct timespec time;
  assert(clock_gettime(CLOCK_REALTIME, &time) == 0);
  return time.tv_sec * 1000000000 + time.tv_nsec;
}

#endif

// End of timing.h.
#include <getopt.h>
#include <ctype.h>
#include <inttypes.h>
#include <unistd.h>
// Start of values.h.

//// Text I/O

typedef int (*writer)(FILE*, const void*);
typedef int (*bin_reader)(void*);
typedef int (*str_reader)(const char *, void*);

struct array_reader {
  char* elems;
  int64_t n_elems_space;
  int64_t elem_size;
  int64_t n_elems_used;
  int64_t *shape;
  str_reader elem_reader;
};

static void skipspaces(FILE *f) {
  int c;
  do {
    c = getc(f);
  } while (isspace(c));

  if (c != EOF) {
    ungetc(c, f);
  }
}

static int constituent(char c) {
  return isalnum(c) || c == '.' || c == '-' || c == '+' || c == '_';
}

// Produces an empty token only on EOF.
static void next_token(FILE *f, char *buf, int bufsize) {
 start:
  skipspaces(f);

  int i = 0;
  while (i < bufsize) {
    int c = getc(f);
    buf[i] = (char)c;

    if (c == EOF) {
      buf[i] = 0;
      return;
    } else if (c == '-' && i == 1 && buf[0] == '-') {
      // Line comment, so skip to end of line and start over.
      for (; c != '\n' && c != EOF; c = getc(f));
      goto start;
    } else if (!constituent((char)c)) {
      if (i == 0) {
        // We permit single-character tokens that are not
        // constituents; this lets things like ']' and ',' be
        // tokens.
        buf[i+1] = 0;
        return;
      } else {
        ungetc(c, f);
        buf[i] = 0;
        return;
      }
    }

    i++;
  }

  buf[bufsize-1] = 0;
}

static int next_token_is(FILE *f, char *buf, int bufsize, const char* expected) {
  next_token(f, buf, bufsize);
  return strcmp(buf, expected) == 0;
}

static void remove_underscores(char *buf) {
  char *w = buf;

  for (char *r = buf; *r; r++) {
    if (*r != '_') {
      *w++ = *r;
    }
  }

  *w++ = 0;
}

static int read_str_elem(char *buf, struct array_reader *reader) {
  int ret;
  if (reader->n_elems_used == reader->n_elems_space) {
    reader->n_elems_space *= 2;
    reader->elems = (char*) realloc(reader->elems,
                                    (size_t)(reader->n_elems_space * reader->elem_size));
  }

  ret = reader->elem_reader(buf, reader->elems + reader->n_elems_used * reader->elem_size);

  if (ret == 0) {
    reader->n_elems_used++;
  }

  return ret;
}

static int read_str_array_elems(FILE *f,
                                char *buf, int bufsize,
                                struct array_reader *reader, int64_t dims) {
  int ret;
  int first = 1;
  char *knows_dimsize = (char*) calloc((size_t)dims, sizeof(char));
  int cur_dim = (int)dims-1;
  int64_t *elems_read_in_dim = (int64_t*) calloc((size_t)dims, sizeof(int64_t));

  while (1) {
    next_token(f, buf, bufsize);

    if (strcmp(buf, "]") == 0) {
      if (knows_dimsize[cur_dim]) {
        if (reader->shape[cur_dim] != elems_read_in_dim[cur_dim]) {
          ret = 1;
          break;
        }
      } else {
        knows_dimsize[cur_dim] = 1;
        reader->shape[cur_dim] = elems_read_in_dim[cur_dim];
      }
      if (cur_dim == 0) {
        ret = 0;
        break;
      } else {
        cur_dim--;
        elems_read_in_dim[cur_dim]++;
      }
    } else if (strcmp(buf, ",") == 0) {
      next_token(f, buf, bufsize);
      if (strcmp(buf, "[") == 0) {
        if (cur_dim == dims - 1) {
          ret = 1;
          break;
        }
        first = 1;
        cur_dim++;
        elems_read_in_dim[cur_dim] = 0;
      } else if (cur_dim == dims - 1) {
        ret = read_str_elem(buf, reader);
        if (ret != 0) {
          break;
        }
        elems_read_in_dim[cur_dim]++;
      } else {
        ret = 1;
        break;
      }
    } else if (strlen(buf) == 0) {
      // EOF
      ret = 1;
      break;
    } else if (first) {
      if (strcmp(buf, "[") == 0) {
        if (cur_dim == dims - 1) {
          ret = 1;
          break;
        }
        cur_dim++;
        elems_read_in_dim[cur_dim] = 0;
      } else {
        ret = read_str_elem(buf, reader);
        if (ret != 0) {
          break;
        }
        elems_read_in_dim[cur_dim]++;
        first = 0;
      }
    } else {
      ret = 1;
      break;
    }
  }

  free(knows_dimsize);
  free(elems_read_in_dim);
  return ret;
}

static int read_str_empty_array(FILE *f, char *buf, int bufsize,
                                const char *type_name, int64_t *shape, int64_t dims) {
  if (strlen(buf) == 0) {
    // EOF
    return 1;
  }

  if (strcmp(buf, "empty") != 0) {
    return 1;
  }

  if (!next_token_is(f, buf, bufsize, "(")) {
    return 1;
  }

  for (int i = 0; i < dims; i++) {
    if (!next_token_is(f, buf, bufsize, "[")) {
      return 1;
    }

    next_token(f, buf, bufsize);

    if (sscanf(buf, "%"SCNu64, (uint64_t*)&shape[i]) != 1) {
      return 1;
    }

    if (!next_token_is(f, buf, bufsize, "]")) {
      return 1;
    }
  }

  if (!next_token_is(f, buf, bufsize, type_name)) {
    return 1;
  }


  if (!next_token_is(f, buf, bufsize, ")")) {
    return 1;
  }

  // Check whether the array really is empty.
  for (int i = 0; i < dims; i++) {
    if (shape[i] == 0) {
      return 0;
    }
  }

  // Not an empty array!
  return 1;
}

static int read_str_array(FILE *f,
                          int64_t elem_size, str_reader elem_reader,
                          const char *type_name,
                          void **data, int64_t *shape, int64_t dims) {
  int ret;
  struct array_reader reader;
  char buf[100];

  int dims_seen;
  for (dims_seen = 0; dims_seen < dims; dims_seen++) {
    if (!next_token_is(f, buf, sizeof(buf), "[")) {
      break;
    }
  }

  if (dims_seen == 0) {
    return read_str_empty_array(f, buf, sizeof(buf), type_name, shape, dims);
  }

  if (dims_seen != dims) {
    return 1;
  }

  reader.shape = shape;
  reader.n_elems_used = 0;
  reader.elem_size = elem_size;
  reader.n_elems_space = 16;
  reader.elems = (char*) realloc(*data, (size_t)(elem_size*reader.n_elems_space));
  reader.elem_reader = elem_reader;

  ret = read_str_array_elems(f, buf, sizeof(buf), &reader, dims);

  *data = reader.elems;

  return ret;
}

#define READ_STR(MACRO, PTR, SUFFIX)                                   \
  remove_underscores(buf);                                              \
  int j;                                                                \
  if (sscanf(buf, "%"MACRO"%n", (PTR*)dest, &j) == 1) {                 \
    return !(strcmp(buf+j, "") == 0 || strcmp(buf+j, SUFFIX) == 0);     \
  } else {                                                              \
    return 1;                                                           \
  }

static int read_str_i8(char *buf, void* dest) {
  // Some platforms (WINDOWS) does not support scanf %hhd or its
  // cousin, %SCNi8.  Read into int first to avoid corrupting
  // memory.
  //
  // https://gcc.gnu.org/bugzilla/show_bug.cgi?id=63417
  remove_underscores(buf);
  int j, x;
  if (sscanf(buf, "%i%n", &x, &j) == 1) {
    *(int8_t*)dest = (int8_t)x;
    return !(strcmp(buf+j, "") == 0 || strcmp(buf+j, "i8") == 0);
  } else {
    return 1;
  }
}

static int read_str_u8(char *buf, void* dest) {
  // Some platforms (WINDOWS) does not support scanf %hhd or its
  // cousin, %SCNu8.  Read into int first to avoid corrupting
  // memory.
  //
  // https://gcc.gnu.org/bugzilla/show_bug.cgi?id=63417
  remove_underscores(buf);
  int j, x;
  if (sscanf(buf, "%i%n", &x, &j) == 1) {
    *(uint8_t*)dest = (uint8_t)x;
    return !(strcmp(buf+j, "") == 0 || strcmp(buf+j, "u8") == 0);
  } else {
    return 1;
  }
}

static int read_str_i16(char *buf, void* dest) {
  READ_STR(SCNi16, int16_t, "i16");
}

static int read_str_u16(char *buf, void* dest) {
  READ_STR(SCNi16, int16_t, "u16");
}

static int read_str_i32(char *buf, void* dest) {
  READ_STR(SCNi32, int32_t, "i32");
}

static int read_str_u32(char *buf, void* dest) {
  READ_STR(SCNi32, int32_t, "u32");
}

static int read_str_i64(char *buf, void* dest) {
  READ_STR(SCNi64, int64_t, "i64");
}

static int read_str_u64(char *buf, void* dest) {
  // FIXME: This is not correct, as SCNu64 only permits decimal
  // literals.  However, SCNi64 does not handle very large numbers
  // correctly (it's really for signed numbers, so that's fair).
  READ_STR(SCNu64, uint64_t, "u64");
}

static int read_str_f16(char *buf, void* dest) {
  remove_underscores(buf);
  if (strcmp(buf, "f16.nan") == 0) {
    *(uint16_t*)dest = float2halfbits(NAN);
    return 0;
  } else if (strcmp(buf, "f16.inf") == 0) {
    *(uint16_t*)dest = float2halfbits(INFINITY);
    return 0;
  } else if (strcmp(buf, "-f16.inf") == 0) {
    *(uint16_t*)dest = float2halfbits(-INFINITY);
    return 0;
  } else {
    int j;
    float x;
    if (sscanf(buf, "%f%n", &x, &j) == 1) {
      if (strcmp(buf+j, "") == 0 || strcmp(buf+j, "f16") == 0) {
        *(uint16_t*)dest = float2halfbits(x);
        return 0;
      }
    }
    return 1;
  }
}

static int read_str_f32(char *buf, void* dest) {
  remove_underscores(buf);
  if (strcmp(buf, "f32.nan") == 0) {
    *(float*)dest = (float)NAN;
    return 0;
  } else if (strcmp(buf, "f32.inf") == 0) {
    *(float*)dest = (float)INFINITY;
    return 0;
  } else if (strcmp(buf, "-f32.inf") == 0) {
    *(float*)dest = (float)-INFINITY;
    return 0;
  } else {
    READ_STR("f", float, "f32");
  }
}

static int read_str_f64(char *buf, void* dest) {
  remove_underscores(buf);
  if (strcmp(buf, "f64.nan") == 0) {
    *(double*)dest = (double)NAN;
    return 0;
  } else if (strcmp(buf, "f64.inf") == 0) {
    *(double*)dest = (double)INFINITY;
    return 0;
  } else if (strcmp(buf, "-f64.inf") == 0) {
    *(double*)dest = (double)-INFINITY;
    return 0;
  } else {
    READ_STR("lf", double, "f64");
  }
}

static int read_str_bool(char *buf, void* dest) {
  if (strcmp(buf, "true") == 0) {
    *(char*)dest = 1;
    return 0;
  } else if (strcmp(buf, "false") == 0) {
    *(char*)dest = 0;
    return 0;
  } else {
    return 1;
  }
}

static int write_str_i8(FILE *out, int8_t *src) {
  return fprintf(out, "%hhdi8", *src);
}

static int write_str_u8(FILE *out, uint8_t *src) {
  return fprintf(out, "%hhuu8", *src);
}

static int write_str_i16(FILE *out, int16_t *src) {
  return fprintf(out, "%hdi16", *src);
}

static int write_str_u16(FILE *out, uint16_t *src) {
  return fprintf(out, "%huu16", *src);
}

static int write_str_i32(FILE *out, int32_t *src) {
  return fprintf(out, "%di32", *src);
}

static int write_str_u32(FILE *out, uint32_t *src) {
  return fprintf(out, "%uu32", *src);
}

static int write_str_i64(FILE *out, int64_t *src) {
  return fprintf(out, "%"PRIi64"i64", *src);
}

static int write_str_u64(FILE *out, uint64_t *src) {
  return fprintf(out, "%"PRIu64"u64", *src);
}

static int write_str_f16(FILE *out, uint16_t *src) {
  float x = halfbits2float(*src);
  if (isnan(x)) {
    return fprintf(out, "f16.nan");
  } else if (isinf(x) && x >= 0) {
    return fprintf(out, "f16.inf");
  } else if (isinf(x)) {
    return fprintf(out, "-f16.inf");
  } else {
    return fprintf(out, "%.6ff16", x);
  }
}

static int write_str_f32(FILE *out, float *src) {
  float x = *src;
  if (isnan(x)) {
    return fprintf(out, "f32.nan");
  } else if (isinf(x) && x >= 0) {
    return fprintf(out, "f32.inf");
  } else if (isinf(x)) {
    return fprintf(out, "-f32.inf");
  } else {
    return fprintf(out, "%.6ff32", x);
  }
}

static int write_str_f64(FILE *out, double *src) {
  double x = *src;
  if (isnan(x)) {
    return fprintf(out, "f64.nan");
  } else if (isinf(x) && x >= 0) {
    return fprintf(out, "f64.inf");
  } else if (isinf(x)) {
    return fprintf(out, "-f64.inf");
  } else {
    return fprintf(out, "%.6ff64", *src);
  }
}

static int write_str_bool(FILE *out, void *src) {
  return fprintf(out, *(char*)src ? "true" : "false");
}

//// Binary I/O

#define BINARY_FORMAT_VERSION 2
#define IS_BIG_ENDIAN (!*(unsigned char *)&(uint16_t){1})

static void flip_bytes(size_t elem_size, unsigned char *elem) {
  for (size_t j=0; j<elem_size/2; j++) {
    unsigned char head = elem[j];
    size_t tail_index = elem_size-1-j;
    elem[j] = elem[tail_index];
    elem[tail_index] = head;
  }
}

// On Windows we need to explicitly set the file mode to not mangle
// newline characters.  On *nix there is no difference.
#ifdef _WIN32
#include <io.h>
#include <fcntl.h>
static void set_binary_mode(FILE *f) {
  setmode(fileno(f), O_BINARY);
}
#else
static void set_binary_mode(FILE *f) {
  (void)f;
}
#endif

static int read_byte(FILE *f, void* dest) {
  size_t num_elems_read = fread(dest, 1, 1, f);
  return num_elems_read == 1 ? 0 : 1;
}

//// Types

struct primtype_info_t {
  const char binname[4]; // Used for parsing binary data.
  const char* type_name; // Same name as in Futhark.
  const int64_t size; // in bytes
  const writer write_str; // Write in text format.
  const str_reader read_str; // Read in text format.
};

static const struct primtype_info_t i8_info =
  {.binname = "  i8", .type_name = "i8",   .size = 1,
   .write_str = (writer)write_str_i8, .read_str = (str_reader)read_str_i8};
static const struct primtype_info_t i16_info =
  {.binname = " i16", .type_name = "i16",  .size = 2,
   .write_str = (writer)write_str_i16, .read_str = (str_reader)read_str_i16};
static const struct primtype_info_t i32_info =
  {.binname = " i32", .type_name = "i32",  .size = 4,
   .write_str = (writer)write_str_i32, .read_str = (str_reader)read_str_i32};
static const struct primtype_info_t i64_info =
  {.binname = " i64", .type_name = "i64",  .size = 8,
   .write_str = (writer)write_str_i64, .read_str = (str_reader)read_str_i64};
static const struct primtype_info_t u8_info =
  {.binname = "  u8", .type_name = "u8",   .size = 1,
   .write_str = (writer)write_str_u8, .read_str = (str_reader)read_str_u8};
static const struct primtype_info_t u16_info =
  {.binname = " u16", .type_name = "u16",  .size = 2,
   .write_str = (writer)write_str_u16, .read_str = (str_reader)read_str_u16};
static const struct primtype_info_t u32_info =
  {.binname = " u32", .type_name = "u32",  .size = 4,
   .write_str = (writer)write_str_u32, .read_str = (str_reader)read_str_u32};
static const struct primtype_info_t u64_info =
  {.binname = " u64", .type_name = "u64",  .size = 8,
   .write_str = (writer)write_str_u64, .read_str = (str_reader)read_str_u64};
static const struct primtype_info_t f16_info =
  {.binname = " f16", .type_name = "f16",  .size = 2,
   .write_str = (writer)write_str_f16, .read_str = (str_reader)read_str_f16};
static const struct primtype_info_t f32_info =
  {.binname = " f32", .type_name = "f32",  .size = 4,
   .write_str = (writer)write_str_f32, .read_str = (str_reader)read_str_f32};
static const struct primtype_info_t f64_info =
  {.binname = " f64", .type_name = "f64",  .size = 8,
   .write_str = (writer)write_str_f64, .read_str = (str_reader)read_str_f64};
static const struct primtype_info_t bool_info =
  {.binname = "bool", .type_name = "bool", .size = 1,
   .write_str = (writer)write_str_bool, .read_str = (str_reader)read_str_bool};

static const struct primtype_info_t* primtypes[] = {
  &i8_info, &i16_info, &i32_info, &i64_info,
  &u8_info, &u16_info, &u32_info, &u64_info,
  &f16_info, &f32_info, &f64_info,
  &bool_info,
  NULL // NULL-terminated
};

// General value interface.  All endian business taken care of at
// lower layers.

static int read_is_binary(FILE *f) {
  skipspaces(f);
  int c = getc(f);
  if (c == 'b') {
    int8_t bin_version;
    int ret = read_byte(f, &bin_version);

    if (ret != 0) { futhark_panic(1, "binary-input: could not read version.\n"); }

    if (bin_version != BINARY_FORMAT_VERSION) {
      futhark_panic(1, "binary-input: File uses version %i, but I only understand version %i.\n",
            bin_version, BINARY_FORMAT_VERSION);
    }

    return 1;
  }
  ungetc(c, f);
  return 0;
}

static const struct primtype_info_t* read_bin_read_type_enum(FILE *f) {
  char read_binname[4];

  int num_matched = fscanf(f, "%4c", read_binname);
  if (num_matched != 1) { futhark_panic(1, "binary-input: Couldn't read element type.\n"); }

  const struct primtype_info_t **type = primtypes;

  for (; *type != NULL; type++) {
    // I compare the 4 characters manually instead of using strncmp because
    // this allows any value to be used, also NULL bytes
    if (memcmp(read_binname, (*type)->binname, 4) == 0) {
      return *type;
    }
  }
  futhark_panic(1, "binary-input: Did not recognize the type '%s'.\n", read_binname);
  return NULL;
}

static void read_bin_ensure_scalar(FILE *f, const struct primtype_info_t *expected_type) {
  int8_t bin_dims;
  int ret = read_byte(f, &bin_dims);
  if (ret != 0) { futhark_panic(1, "binary-input: Couldn't get dims.\n"); }

  if (bin_dims != 0) {
    futhark_panic(1, "binary-input: Expected scalar (0 dimensions), but got array with %i dimensions.\n",
          bin_dims);
  }

  const struct primtype_info_t *bin_type = read_bin_read_type_enum(f);
  if (bin_type != expected_type) {
    futhark_panic(1, "binary-input: Expected scalar of type %s but got scalar of type %s.\n",
          expected_type->type_name,
          bin_type->type_name);
  }
}

//// High-level interface

static int read_bin_array(FILE *f,
                          const struct primtype_info_t *expected_type, void **data, int64_t *shape, int64_t dims) {
  int ret;

  int8_t bin_dims;
  ret = read_byte(f, &bin_dims);
  if (ret != 0) { futhark_panic(1, "binary-input: Couldn't get dims.\n"); }

  if (bin_dims != dims) {
    futhark_panic(1, "binary-input: Expected %i dimensions, but got array with %i dimensions.\n",
          dims, bin_dims);
  }

  const struct primtype_info_t *bin_primtype = read_bin_read_type_enum(f);
  if (expected_type != bin_primtype) {
    futhark_panic(1, "binary-input: Expected %iD-array with element type '%s' but got %iD-array with element type '%s'.\n",
          dims, expected_type->type_name, dims, bin_primtype->type_name);
  }

  int64_t elem_count = 1;
  for (int i=0; i<dims; i++) {
    int64_t bin_shape;
    ret = (int)fread(&bin_shape, sizeof(bin_shape), 1, f);
    if (ret != 1) {
      futhark_panic(1, "binary-input: Couldn't read size for dimension %i of array.\n", i);
    }
    if (IS_BIG_ENDIAN) {
      flip_bytes(sizeof(bin_shape), (unsigned char*) &bin_shape);
    }
    elem_count *= bin_shape;
    shape[i] = bin_shape;
  }

  int64_t elem_size = expected_type->size;
  void* tmp = realloc(*data, (size_t)(elem_count * elem_size));
  if (tmp == NULL) {
    futhark_panic(1, "binary-input: Failed to allocate array of size %i.\n",
          elem_count * elem_size);
  }
  *data = tmp;

  int64_t num_elems_read = (int64_t)fread(*data, (size_t)elem_size, (size_t)elem_count, f);
  if (num_elems_read != elem_count) {
    futhark_panic(1, "binary-input: tried to read %i elements of an array, but only got %i elements.\n",
          elem_count, num_elems_read);
  }

  // If we're on big endian platform we must change all multibyte elements
  // from using little endian to big endian
  if (IS_BIG_ENDIAN && elem_size != 1) {
    flip_bytes((size_t)elem_size, (unsigned char*) *data);
  }

  return 0;
}

static int read_array(FILE *f, const struct primtype_info_t *expected_type, void **data, int64_t *shape, int64_t dims) {
  if (!read_is_binary(f)) {
    return read_str_array(f, expected_type->size, (str_reader)expected_type->read_str, expected_type->type_name, data, shape, dims);
  } else {
    return read_bin_array(f, expected_type, data, shape, dims);
  }
}

static int end_of_input(FILE *f) {
  skipspaces(f);
  char token[2];
  next_token(f, token, sizeof(token));
  if (strcmp(token, "") == 0) {
    return 0;
  } else {
    return 1;
  }
}

static int write_str_array(FILE *out,
                           const struct primtype_info_t *elem_type,
                           const unsigned char *data,
                           const int64_t *shape,
                           int8_t rank) {
  if (rank==0) {
    elem_type->write_str(out, (const void*)data);
  } else {
    int64_t len = (int64_t)shape[0];
    int64_t slice_size = 1;

    int64_t elem_size = elem_type->size;
    for (int8_t i = 1; i < rank; i++) {
      slice_size *= shape[i];
    }

    if (len*slice_size == 0) {
      fprintf(out, "empty(");
      for (int64_t i = 0; i < rank; i++) {
        fprintf(out, "[%"PRIi64"]", shape[i]);
      }
      fprintf(out, "%s", elem_type->type_name);
      fprintf(out, ")");
    } else if (rank==1) {
      fputc('[', out);
      for (int64_t i = 0; i < len; i++) {
        elem_type->write_str(out, (const void*) (data + i * elem_size));
        if (i != len-1) {
          fprintf(out, ", ");
        }
      }
      fputc(']', out);
    } else {
      fputc('[', out);
      for (int64_t i = 0; i < len; i++) {
        write_str_array(out, elem_type, data + i * slice_size * elem_size, shape+1, rank-1);
        if (i != len-1) {
          fprintf(out, ", ");
        }
      }
      fputc(']', out);
    }
  }
  return 0;
}

static int write_bin_array(FILE *out,
                           const struct primtype_info_t *elem_type,
                           const unsigned char *data,
                           const int64_t *shape,
                           int8_t rank) {
  int64_t num_elems = 1;
  for (int64_t i = 0; i < rank; i++) {
    num_elems *= shape[i];
  }

  fputc('b', out);
  fputc((char)BINARY_FORMAT_VERSION, out);
  fwrite(&rank, sizeof(int8_t), 1, out);
  fwrite(elem_type->binname, 4, 1, out);
  if (shape != NULL) {
    fwrite(shape, sizeof(int64_t), (size_t)rank, out);
  }

  if (IS_BIG_ENDIAN) {
    for (int64_t i = 0; i < num_elems; i++) {
      const unsigned char *elem = data+i*elem_type->size;
      for (int64_t j = 0; j < elem_type->size; j++) {
        fwrite(&elem[elem_type->size-j], 1, 1, out);
      }
    }
  } else {
    fwrite(data, (size_t)elem_type->size, (size_t)num_elems, out);
  }

  return 0;
}

static int write_array(FILE *out, int write_binary,
                       const struct primtype_info_t *elem_type,
                       const void *data,
                       const int64_t *shape,
                       const int8_t rank) {
  if (write_binary) {
    return write_bin_array(out, elem_type, data, shape, rank);
  } else {
    return write_str_array(out, elem_type, data, shape, rank);
  }
}

static int read_scalar(FILE *f,
                       const struct primtype_info_t *expected_type, void *dest) {
  if (!read_is_binary(f)) {
    char buf[100];
    next_token(f, buf, sizeof(buf));
    return expected_type->read_str(buf, dest);
  } else {
    read_bin_ensure_scalar(f, expected_type);
    size_t elem_size = (size_t)expected_type->size;
    size_t num_elems_read = fread(dest, elem_size, 1, f);
    if (IS_BIG_ENDIAN) {
      flip_bytes(elem_size, (unsigned char*) dest);
    }
    return num_elems_read == 1 ? 0 : 1;
  }
}

static int write_scalar(FILE *out, int write_binary, const struct primtype_info_t *type, void *src) {
  if (write_binary) {
    return write_bin_array(out, type, src, NULL, 0);
  } else {
    return type->write_str(out, src);
  }
}

// End of values.h.

static int binary_output = 0;
static int print_result = 1;
static FILE *runtime_file;
static int perform_warmup = 0;
static int num_runs = 1;
static const char *entry_point = "main";
// Start of tuning.h.

static char* load_tuning_file(const char *fname,
                              void *cfg,
                              int (*set_tuning_param)(void*, const char*, size_t)) {
  const int max_line_len = 1024;
  char* line = (char*) malloc(max_line_len);

  FILE *f = fopen(fname, "r");

  if (f == NULL) {
    snprintf(line, max_line_len, "Cannot open file: %s", strerror(errno));
    return line;
  }

  int lineno = 0;
  while (fgets(line, max_line_len, f) != NULL) {
    lineno++;
    char *eql = strstr(line, "=");
    if (eql) {
      *eql = 0;
      int value = atoi(eql+1);
      if (set_tuning_param(cfg, line, (size_t)value) != 0) {
        char* err = (char*) malloc(max_line_len + 50);
        snprintf(err, max_line_len + 50, "Unknown name '%s' on line %d.", line, lineno);
        free(line);
        return err;
      }
    } else {
      snprintf(line, max_line_len, "Invalid line %d (must be of form 'name=int').",
               lineno);
      return line;
    }
  }

  free(line);

  return NULL;
}

// End of tuning.h.

int parse_options(struct futhark_context_config *cfg, int argc,
                  char *const argv[])
{
    int ch;
    static struct option long_options[] = {{"write-runtime-to",
                                            required_argument, NULL, 1},
                                           {"runs", required_argument, NULL, 2},
                                           {"debugging", no_argument, NULL, 3},
                                           {"log", no_argument, NULL, 4},
                                           {"entry-point", required_argument,
                                            NULL, 5}, {"binary-output",
                                                       no_argument, NULL, 6},
                                           {"no-print-result", no_argument,
                                            NULL, 7}, {"help", no_argument,
                                                       NULL, 8},
                                           {"print-params", no_argument, NULL,
                                            9}, {"param", required_argument,
                                                 NULL, 10}, {"tuning",
                                                             required_argument,
                                                             NULL, 11}, {0, 0,
                                                                         0, 0}};
    static char *option_descriptions =
                "  -t/--write-runtime-to FILE Print the time taken to execute the program to the indicated file, an integral number of microseconds.\n  -r/--runs INT              Perform NUM runs of the program.\n  -D/--debugging             Perform possibly expensive internal correctness checks and verbose logging.\n  -L/--log                   Print various low-overhead logging information to stderr while running.\n  -e/--entry-point NAME      The entry point to run. Defaults to main.\n  -b/--binary-output         Print the program result in the binary output format.\n  -n/--no-print-result       Do not print the program result.\n  -h/--help                  Print help information and exit.\n  --print-params             Print all tuning parameters that can be set with --param or --tuning.\n  --param ASSIGNMENT         Set a tuning parameter to the given value.\n  --tuning FILE              Read size=value assignments from the given file.\n";
    
    while ((ch = getopt_long(argc, argv, ":t:r:DLe:bnh", long_options, NULL)) !=
           -1) {
        if (ch == 1 || ch == 't') {
            runtime_file = fopen(optarg, "w");
            if (runtime_file == NULL)
                futhark_panic(1, "Cannot open %s: %s\n", optarg,
                              strerror(errno));
        }
        if (ch == 2 || ch == 'r') {
            num_runs = atoi(optarg);
            perform_warmup = 1;
            if (num_runs <= 0)
                futhark_panic(1, "Need a positive number of runs, not %s\n",
                              optarg);
        }
        if (ch == 3 || ch == 'D')
            futhark_context_config_set_debugging(cfg, 1);
        if (ch == 4 || ch == 'L')
            futhark_context_config_set_logging(cfg, 1);
        if (ch == 5 || ch == 'e') {
            if (entry_point != NULL)
                entry_point = optarg;
        }
        if (ch == 6 || ch == 'b')
            binary_output = 1;
        if (ch == 7 || ch == 'n')
            print_result = 0;
        if (ch == 8 || ch == 'h') {
            printf("Usage: %s [OPTION]...\nOptions:\n\n%s\nFor more information, consult the Futhark User's Guide or the man pages.\n",
                   fut_progname, option_descriptions);
            exit(0);
        }
        if (ch == 9) {
            int n = futhark_get_tuning_param_count();
            
            for (int i = 0; i < n; i++)
                printf("%s (%s)\n", futhark_get_tuning_param_name(i),
                       futhark_get_tuning_param_class(i));
            exit(0);
        }
        if (ch == 10) {
            char *name = optarg;
            char *equals = strstr(optarg, "=");
            char *value_str = equals != NULL ? equals + 1 : optarg;
            int value = atoi(value_str);
            
            if (equals != NULL) {
                *equals = 0;
                if (futhark_context_config_set_tuning_param(cfg, name,
                                                            (size_t) value) !=
                    0)
                    futhark_panic(1, "Unknown size: %s\n", name);
            } else
                futhark_panic(1, "Invalid argument for size option: %s\n",
                              optarg);
        }
        if (ch == 11) {
            char *ret = load_tuning_file(optarg, cfg, (int (*)(void *, const
                                                               char *,
                                                               size_t)) futhark_context_config_set_tuning_param);
            
            if (ret != NULL)
                futhark_panic(1, "When loading tuning from '%s': %s\n", optarg,
                              ret);
        }
        if (ch == ':')
            futhark_panic(-1, "Missing argument for option %s\n", argv[optind -
                                                                       1]);
        if (ch == '?') {
            fprintf(stderr, "Usage: %s [OPTIONS]...\nOptions:\n\n%s\n",
                    fut_progname,
                    "  -t/--write-runtime-to FILE Print the time taken to execute the program to the indicated file, an integral number of microseconds.\n  -r/--runs INT              Perform NUM runs of the program.\n  -D/--debugging             Perform possibly expensive internal correctness checks and verbose logging.\n  -L/--log                   Print various low-overhead logging information to stderr while running.\n  -e/--entry-point NAME      The entry point to run. Defaults to main.\n  -b/--binary-output         Print the program result in the binary output format.\n  -n/--no-print-result       Do not print the program result.\n  -h/--help                  Print help information and exit.\n  --print-params             Print all tuning parameters that can be set with --param or --tuning.\n  --param ASSIGNMENT         Set a tuning parameter to the given value.\n  --tuning FILE              Read size=value assignments from the given file.\n");
            futhark_panic(1, "Unknown option: %s\n", argv[optind - 1]);
        }
    }
    return optind;
}
static void futrts_cli_entry_main(struct futhark_context *ctx)
{
    int64_t t_start, t_end;
    int time_runs = 0, profile_run = 0;
    
    // We do not want to profile all the initialisation.
    futhark_context_pause_profiling(ctx);
    // Declare and read input.
    set_binary_mode(stdin);
    
    int32_t read_value_0;
    
    if (read_scalar(stdin, &i32_info, &read_value_0) != 0)
        futhark_panic(1,
                      "Error when reading input #%d of type %s (errno: %s).\n",
                      0, "i32", strerror(errno));
    ;
    
    int32_t read_value_1;
    
    if (read_scalar(stdin, &i32_info, &read_value_1) != 0)
        futhark_panic(1,
                      "Error when reading input #%d of type %s (errno: %s).\n",
                      1, "i32", strerror(errno));
    ;
    
    struct futhark_i32_2d * read_value_2;
    int64_t read_shape_2[2];
    int32_t *read_arr_2 = NULL;
    
    errno = 0;
    if (read_array(stdin, &i32_info, (void **) &read_arr_2, read_shape_2, 2) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 2,
                      "[][]i32", strerror(errno));
    
    struct futhark_f32_3d * read_value_3;
    int64_t read_shape_3[3];
    float *read_arr_3 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_3, read_shape_3, 3) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 3,
                      "[][][]f32", strerror(errno));
    
    struct futhark_f32_3d * read_value_4;
    int64_t read_shape_4[3];
    float *read_arr_4 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_4, read_shape_4, 3) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 4,
                      "[][][]f32", strerror(errno));
    
    struct futhark_f32_3d * read_value_5;
    int64_t read_shape_5[3];
    float *read_arr_5 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_5, read_shape_5, 3) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 5,
                      "[][][]f32", strerror(errno));
    
    struct futhark_f32_2d * read_value_6;
    int64_t read_shape_6[2];
    float *read_arr_6 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_6, read_shape_6, 2) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 6,
                      "[][]f32", strerror(errno));
    
    struct futhark_f32_2d * read_value_7;
    int64_t read_shape_7[2];
    float *read_arr_7 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_7, read_shape_7, 2) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 7,
                      "[][]f32", strerror(errno));
    
    struct futhark_f32_2d * read_value_8;
    int64_t read_shape_8[2];
    float *read_arr_8 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_8, read_shape_8, 2) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 8,
                      "[][]f32", strerror(errno));
    
    struct futhark_i32_2d * read_value_9;
    int64_t read_shape_9[2];
    int32_t *read_arr_9 = NULL;
    
    errno = 0;
    if (read_array(stdin, &i32_info, (void **) &read_arr_9, read_shape_9, 2) !=
        0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 9,
                      "[][]i32", strerror(errno));
    
    struct futhark_f32_2d * read_value_10;
    int64_t read_shape_10[2];
    float *read_arr_10 = NULL;
    
    errno = 0;
    if (read_array(stdin, &f32_info, (void **) &read_arr_10, read_shape_10,
                   2) != 0)
        futhark_panic(1, "Cannot read input #%d of type %s (errno: %s).\n", 10,
                      "[][]f32", strerror(errno));
    if (end_of_input(stdin) != 0)
        futhark_panic(1,
                      "Expected EOF on stdin after reading input for \"%s\".\n",
                      "main");
    
    struct futhark_f32_1d * result_0;
    
    if (perform_warmup) {
        int r;
        
        ;
        ;
        assert((read_value_2 = futhark_new_i32_2d(ctx, read_arr_2,
                                                  read_shape_2[0],
                                                  read_shape_2[1])) != NULL);
        assert((read_value_3 = futhark_new_f32_3d(ctx, read_arr_3,
                                                  read_shape_3[0],
                                                  read_shape_3[1],
                                                  read_shape_3[2])) != NULL);
        assert((read_value_4 = futhark_new_f32_3d(ctx, read_arr_4,
                                                  read_shape_4[0],
                                                  read_shape_4[1],
                                                  read_shape_4[2])) != NULL);
        assert((read_value_5 = futhark_new_f32_3d(ctx, read_arr_5,
                                                  read_shape_5[0],
                                                  read_shape_5[1],
                                                  read_shape_5[2])) != NULL);
        assert((read_value_6 = futhark_new_f32_2d(ctx, read_arr_6,
                                                  read_shape_6[0],
                                                  read_shape_6[1])) != NULL);
        assert((read_value_7 = futhark_new_f32_2d(ctx, read_arr_7,
                                                  read_shape_7[0],
                                                  read_shape_7[1])) != NULL);
        assert((read_value_8 = futhark_new_f32_2d(ctx, read_arr_8,
                                                  read_shape_8[0],
                                                  read_shape_8[1])) != NULL);
        assert((read_value_9 = futhark_new_i32_2d(ctx, read_arr_9,
                                                  read_shape_9[0],
                                                  read_shape_9[1])) != NULL);
        assert((read_value_10 = futhark_new_f32_2d(ctx, read_arr_10,
                                                   read_shape_10[0],
                                                   read_shape_10[1])) != NULL);
        if (futhark_context_sync(ctx) != 0)
            futhark_panic(1, "%s", futhark_context_get_error(ctx));
        ;
        // Only profile last run.
        if (profile_run)
            futhark_context_unpause_profiling(ctx);
        t_start = get_wall_time();
        r = futhark_entry_main(ctx, &result_0, read_value_0, read_value_1,
                               read_value_2, read_value_3, read_value_4,
                               read_value_5, read_value_6, read_value_7,
                               read_value_8, read_value_9, read_value_10);
        if (r != 0)
            futhark_panic(1, "%s", futhark_context_get_error(ctx));
        if (futhark_context_sync(ctx) != 0)
            futhark_panic(1, "%s", futhark_context_get_error(ctx));
        ;
        if (profile_run)
            futhark_context_pause_profiling(ctx);
        t_end = get_wall_time();
        
        long elapsed_usec = t_end - t_start;
        
        if (time_runs && runtime_file != NULL) {
            fprintf(runtime_file, "%lld\n", (long long) elapsed_usec);
            fflush(runtime_file);
        }
        ;
        ;
        assert(futhark_free_i32_2d(ctx, read_value_2) == 0);
        assert(futhark_free_f32_3d(ctx, read_value_3) == 0);
        assert(futhark_free_f32_3d(ctx, read_value_4) == 0);
        assert(futhark_free_f32_3d(ctx, read_value_5) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_6) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_7) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_8) == 0);
        assert(futhark_free_i32_2d(ctx, read_value_9) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_10) == 0);
        assert(futhark_free_f32_1d(ctx, result_0) == 0);
    }
    time_runs = 1;
    // Proper run.
    for (int run = 0; run < num_runs; run++) {
        // Only profile last run.
        profile_run = run == num_runs - 1;
        
        int r;
        
        ;
        ;
        assert((read_value_2 = futhark_new_i32_2d(ctx, read_arr_2,
                                                  read_shape_2[0],
                                                  read_shape_2[1])) != NULL);
        assert((read_value_3 = futhark_new_f32_3d(ctx, read_arr_3,
                                                  read_shape_3[0],
                                                  read_shape_3[1],
                                                  read_shape_3[2])) != NULL);
        assert((read_value_4 = futhark_new_f32_3d(ctx, read_arr_4,
                                                  read_shape_4[0],
                                                  read_shape_4[1],
                                                  read_shape_4[2])) != NULL);
        assert((read_value_5 = futhark_new_f32_3d(ctx, read_arr_5,
                                                  read_shape_5[0],
                                                  read_shape_5[1],
                                                  read_shape_5[2])) != NULL);
        assert((read_value_6 = futhark_new_f32_2d(ctx, read_arr_6,
                                                  read_shape_6[0],
                                                  read_shape_6[1])) != NULL);
        assert((read_value_7 = futhark_new_f32_2d(ctx, read_arr_7,
                                                  read_shape_7[0],
                                                  read_shape_7[1])) != NULL);
        assert((read_value_8 = futhark_new_f32_2d(ctx, read_arr_8,
                                                  read_shape_8[0],
                                                  read_shape_8[1])) != NULL);
        assert((read_value_9 = futhark_new_i32_2d(ctx, read_arr_9,
                                                  read_shape_9[0],
                                                  read_shape_9[1])) != NULL);
        assert((read_value_10 = futhark_new_f32_2d(ctx, read_arr_10,
                                                   read_shape_10[0],
                                                   read_shape_10[1])) != NULL);
        if (futhark_context_sync(ctx) != 0)
            futhark_panic(1, "%s", futhark_context_get_error(ctx));
        ;
        // Only profile last run.
        if (profile_run)
            futhark_context_unpause_profiling(ctx);
        t_start = get_wall_time();
        r = futhark_entry_main(ctx, &result_0, read_value_0, read_value_1,
                               read_value_2, read_value_3, read_value_4,
                               read_value_5, read_value_6, read_value_7,
                               read_value_8, read_value_9, read_value_10);
        if (r != 0)
            futhark_panic(1, "%s", futhark_context_get_error(ctx));
        if (futhark_context_sync(ctx) != 0)
            futhark_panic(1, "%s", futhark_context_get_error(ctx));
        ;
        if (profile_run)
            futhark_context_pause_profiling(ctx);
        t_end = get_wall_time();
        
        long elapsed_usec = t_end - t_start;
        
        if (time_runs && runtime_file != NULL) {
            fprintf(runtime_file, "%lld\n", (long long) elapsed_usec);
            fflush(runtime_file);
        }
        ;
        ;
        assert(futhark_free_i32_2d(ctx, read_value_2) == 0);
        assert(futhark_free_f32_3d(ctx, read_value_3) == 0);
        assert(futhark_free_f32_3d(ctx, read_value_4) == 0);
        assert(futhark_free_f32_3d(ctx, read_value_5) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_6) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_7) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_8) == 0);
        assert(futhark_free_i32_2d(ctx, read_value_9) == 0);
        assert(futhark_free_f32_2d(ctx, read_value_10) == 0);
        if (run < num_runs - 1) {
            assert(futhark_free_f32_1d(ctx, result_0) == 0);
        }
    }
    ;
    ;
    free(read_arr_2);
    free(read_arr_3);
    free(read_arr_4);
    free(read_arr_5);
    free(read_arr_6);
    free(read_arr_7);
    free(read_arr_8);
    free(read_arr_9);
    free(read_arr_10);
    if (print_result) {
        // Print the final result.
        if (binary_output)
            set_binary_mode(stdout);
        {
            float *arr = calloc(futhark_shape_f32_1d(ctx, result_0)[0],
                                f32_info.size);
            
            assert(arr != NULL);
            assert(futhark_values_f32_1d(ctx, result_0, arr) == 0);
            write_array(stdout, binary_output, &f32_info, arr,
                        futhark_shape_f32_1d(ctx, result_0), 1);
            free(arr);
        }
        printf("\n");
    }
    assert(futhark_free_f32_1d(ctx, result_0) == 0);
}
typedef void entry_point_fun(struct futhark_context *);
struct entry_point_entry {
    const char *name;
    entry_point_fun *fun;
};
int main(int argc, char **argv)
{
    fut_progname = argv[0];
    
    struct futhark_context_config *cfg = futhark_context_config_new();
    
    assert(cfg != NULL);
    
    int parsed_options = parse_options(cfg, argc, argv);
    
    argc -= parsed_options;
    argv += parsed_options;
    if (argc != 0)
        futhark_panic(1, "Excess non-option: %s\n", argv[0]);
    
    struct futhark_context *ctx = futhark_context_new(cfg);
    
    assert(ctx != NULL);
    
    char *error = futhark_context_get_error(ctx);
    
    if (error != NULL)
        futhark_panic(1, "%s", error);
    
    struct entry_point_entry entry_points[] = {{.name ="main", .fun =
                                                futrts_cli_entry_main}};
    
    if (entry_point != NULL) {
        int num_entry_points = sizeof(entry_points) / sizeof(entry_points[0]);
        entry_point_fun *entry_point_fun = NULL;
        
        for (int i = 0; i < num_entry_points; i++) {
            if (strcmp(entry_points[i].name, entry_point) == 0) {
                entry_point_fun = entry_points[i].fun;
                break;
            }
        }
        if (entry_point_fun == NULL) {
            fprintf(stderr,
                    "No entry point '%s'.  Select another with --entry-point.  Options are:\n",
                    entry_point);
            for (int i = 0; i < num_entry_points; i++)
                fprintf(stderr, "%s\n", entry_points[i].name);
            return 1;
        }
        if (isatty(fileno(stdin))) {
            fprintf(stderr, "Reading input from TTY.\n");
            fprintf(stderr,
                    "Send EOF (CTRL-d) after typing all input values.\n");
        }
        entry_point_fun(ctx);
        if (runtime_file != NULL)
            fclose(runtime_file);
        
        char *report = futhark_context_report(ctx);
        
        fputs(report, stderr);
        free(report);
    }
    futhark_context_free(ctx);
    futhark_context_config_free(cfg);
    return 0;
}

#ifdef _MSC_VER
#define inline __inline
#endif
#include <string.h>
#include <string.h>
#include <errno.h>
#include <assert.h>
#include <ctype.h>



// Start of lock.h.

// A very simple cross-platform implementation of locks.  Uses
// pthreads on Unix and some Windows thing there.  Futhark's
// host-level code is not multithreaded, but user code may be, so we
// need some mechanism for ensuring atomic access to API functions.
// This is that mechanism.  It is not exposed to user code at all, so
// we do not have to worry about name collisions.

#ifdef _WIN32

typedef HANDLE lock_t;

static void create_lock(lock_t *lock) {
  *lock = CreateMutex(NULL,  // Default security attributes.
                      FALSE, // Initially unlocked.
                      NULL); // Unnamed.
}

static void lock_lock(lock_t *lock) {
  assert(WaitForSingleObject(*lock, INFINITE) == WAIT_OBJECT_0);
}

static void lock_unlock(lock_t *lock) {
  assert(ReleaseMutex(*lock));
}

static void free_lock(lock_t *lock) {
  CloseHandle(*lock);
}

#else
// Assuming POSIX

#include <pthread.h>

typedef pthread_mutex_t lock_t;

static void create_lock(lock_t *lock) {
  int r = pthread_mutex_init(lock, NULL);
  assert(r == 0);
}

static void lock_lock(lock_t *lock) {
  int r = pthread_mutex_lock(lock);
  assert(r == 0);
}

static void lock_unlock(lock_t *lock) {
  int r = pthread_mutex_unlock(lock);
  assert(r == 0);
}

static void free_lock(lock_t *lock) {
  // Nothing to do for pthreads.
  (void)lock;
}

#endif

// End of lock.h.

#define FUTHARK_F64_ENABLED

// Start of scalar.h.

// Implementation of the primitive scalar operations.  Very
// repetitive.  This code is inserted directly into both CUDA and
// OpenCL programs, as well as the CPU code, so it has some #ifdefs to
// work everywhere.  Some operations are defined as macros because
// this allows us to use them as constant expressions in things like
// array sizes and static initialisers.

// Some of the #ifdefs are because OpenCL uses type-generic functions
// for some operations (e.g. sqrt), while C and CUDA sensibly use
// distinct functions for different precisions (e.g. sqrtf() and
// sqrt()).  This is quite annoying.  Due to C's unfortunate casting
// rules, it is also really easy to accidentally implement
// floating-point functions in the wrong precision, so be careful.

// Double-precision definitions are only included if the preprocessor
// macro FUTHARK_F64_ENABLED is set.

static inline uint8_t add8(uint8_t x, uint8_t y) {
  return x + y;
}

static inline uint16_t add16(uint16_t x, uint16_t y) {
  return x + y;
}

static inline uint32_t add32(uint32_t x, uint32_t y) {
  return x + y;
}

static inline uint64_t add64(uint64_t x, uint64_t y) {
  return x + y;
}

static inline uint8_t sub8(uint8_t x, uint8_t y) {
  return x - y;
}

static inline uint16_t sub16(uint16_t x, uint16_t y) {
  return x - y;
}

static inline uint32_t sub32(uint32_t x, uint32_t y) {
  return x - y;
}

static inline uint64_t sub64(uint64_t x, uint64_t y) {
  return x - y;
}

static inline uint8_t mul8(uint8_t x, uint8_t y) {
  return x * y;
}

static inline uint16_t mul16(uint16_t x, uint16_t y) {
  return x * y;
}

static inline uint32_t mul32(uint32_t x, uint32_t y) {
  return x * y;
}

static inline uint64_t mul64(uint64_t x, uint64_t y) {
  return x * y;
}

static inline uint8_t udiv8(uint8_t x, uint8_t y) {
  return x / y;
}

static inline uint16_t udiv16(uint16_t x, uint16_t y) {
  return x / y;
}

static inline uint32_t udiv32(uint32_t x, uint32_t y) {
  return x / y;
}

static inline uint64_t udiv64(uint64_t x, uint64_t y) {
  return x / y;
}

static inline uint8_t udiv_up8(uint8_t x, uint8_t y) {
  return (x + y - 1) / y;
}

static inline uint16_t udiv_up16(uint16_t x, uint16_t y) {
  return (x + y - 1) / y;
}

static inline uint32_t udiv_up32(uint32_t x, uint32_t y) {
  return (x + y - 1) / y;
}

static inline uint64_t udiv_up64(uint64_t x, uint64_t y) {
  return (x + y - 1) / y;
}

static inline uint8_t umod8(uint8_t x, uint8_t y) {
  return x % y;
}

static inline uint16_t umod16(uint16_t x, uint16_t y) {
  return x % y;
}

static inline uint32_t umod32(uint32_t x, uint32_t y) {
  return x % y;
}

static inline uint64_t umod64(uint64_t x, uint64_t y) {
  return x % y;
}

static inline uint8_t udiv_safe8(uint8_t x, uint8_t y) {
  return y == 0 ? 0 : x / y;
}

static inline uint16_t udiv_safe16(uint16_t x, uint16_t y) {
  return y == 0 ? 0 : x / y;
}

static inline uint32_t udiv_safe32(uint32_t x, uint32_t y) {
  return y == 0 ? 0 : x / y;
}

static inline uint64_t udiv_safe64(uint64_t x, uint64_t y) {
  return y == 0 ? 0 : x / y;
}

static inline uint8_t udiv_up_safe8(uint8_t x, uint8_t y) {
  return y == 0 ? 0 : (x + y - 1) / y;
}

static inline uint16_t udiv_up_safe16(uint16_t x, uint16_t y) {
  return y == 0 ? 0 : (x + y - 1) / y;
}

static inline uint32_t udiv_up_safe32(uint32_t x, uint32_t y) {
  return y == 0 ? 0 : (x + y - 1) / y;
}

static inline uint64_t udiv_up_safe64(uint64_t x, uint64_t y) {
  return y == 0 ? 0 : (x + y - 1) / y;
}

static inline uint8_t umod_safe8(uint8_t x, uint8_t y) {
  return y == 0 ? 0 : x % y;
}

static inline uint16_t umod_safe16(uint16_t x, uint16_t y) {
  return y == 0 ? 0 : x % y;
}

static inline uint32_t umod_safe32(uint32_t x, uint32_t y) {
  return y == 0 ? 0 : x % y;
}

static inline uint64_t umod_safe64(uint64_t x, uint64_t y) {
  return y == 0 ? 0 : x % y;
}

static inline int8_t sdiv8(int8_t x, int8_t y) {
  int8_t q = x / y;
  int8_t r = x % y;

  return q - ((r != 0 && r < 0 != y < 0) ? 1 : 0);
}

static inline int16_t sdiv16(int16_t x, int16_t y) {
  int16_t q = x / y;
  int16_t r = x % y;

  return q - ((r != 0 && r < 0 != y < 0) ? 1 : 0);
}

static inline int32_t sdiv32(int32_t x, int32_t y) {
  int32_t q = x / y;
  int32_t r = x % y;

  return q - ((r != 0 && r < 0 != y < 0) ? 1 : 0);
}

static inline int64_t sdiv64(int64_t x, int64_t y) {
  int64_t q = x / y;
  int64_t r = x % y;

  return q - ((r != 0 && r < 0 != y < 0) ? 1 : 0);
}

static inline int8_t sdiv_up8(int8_t x, int8_t y) {
  return sdiv8(x + y - 1, y);
}

static inline int16_t sdiv_up16(int16_t x, int16_t y) {
  return sdiv16(x + y - 1, y);
}

static inline int32_t sdiv_up32(int32_t x, int32_t y) {
  return sdiv32(x + y - 1, y);
}

static inline int64_t sdiv_up64(int64_t x, int64_t y) {
  return sdiv64(x + y - 1, y);
}

static inline int8_t smod8(int8_t x, int8_t y) {
  int8_t r = x % y;

  return r + (r == 0 || (x > 0 && y > 0) || (x < 0 && y < 0) ? 0 : y);
}

static inline int16_t smod16(int16_t x, int16_t y) {
  int16_t r = x % y;

  return r + (r == 0 || (x > 0 && y > 0) || (x < 0 && y < 0) ? 0 : y);
}

static inline int32_t smod32(int32_t x, int32_t y) {
  int32_t r = x % y;

  return r + (r == 0 || (x > 0 && y > 0) || (x < 0 && y < 0) ? 0 : y);
}

static inline int64_t smod64(int64_t x, int64_t y) {
  int64_t r = x % y;

  return r + (r == 0 || (x > 0 && y > 0) || (x < 0 && y < 0) ? 0 : y);
}

static inline int8_t sdiv_safe8(int8_t x, int8_t y) {
  return y == 0 ? 0 : sdiv8(x, y);
}

static inline int16_t sdiv_safe16(int16_t x, int16_t y) {
  return y == 0 ? 0 : sdiv16(x, y);
}

static inline int32_t sdiv_safe32(int32_t x, int32_t y) {
  return y == 0 ? 0 : sdiv32(x, y);
}

static inline int64_t sdiv_safe64(int64_t x, int64_t y) {
  return y == 0 ? 0 : sdiv64(x, y);
}

static inline int8_t sdiv_up_safe8(int8_t x, int8_t y) {
  return sdiv_safe8(x + y - 1, y);
}

static inline int16_t sdiv_up_safe16(int16_t x, int16_t y) {
  return sdiv_safe16(x + y - 1, y);
}

static inline int32_t sdiv_up_safe32(int32_t x, int32_t y) {
  return sdiv_safe32(x + y - 1, y);
}

static inline int64_t sdiv_up_safe64(int64_t x, int64_t y) {
  return sdiv_safe64(x + y - 1, y);
}

static inline int8_t smod_safe8(int8_t x, int8_t y) {
  return y == 0 ? 0 : smod8(x, y);
}

static inline int16_t smod_safe16(int16_t x, int16_t y) {
  return y == 0 ? 0 : smod16(x, y);
}

static inline int32_t smod_safe32(int32_t x, int32_t y) {
  return y == 0 ? 0 : smod32(x, y);
}

static inline int64_t smod_safe64(int64_t x, int64_t y) {
  return y == 0 ? 0 : smod64(x, y);
}

static inline int8_t squot8(int8_t x, int8_t y) {
  return x / y;
}

static inline int16_t squot16(int16_t x, int16_t y) {
  return x / y;
}

static inline int32_t squot32(int32_t x, int32_t y) {
  return x / y;
}

static inline int64_t squot64(int64_t x, int64_t y) {
  return x / y;
}

static inline int8_t srem8(int8_t x, int8_t y) {
  return x % y;
}

static inline int16_t srem16(int16_t x, int16_t y) {
  return x % y;
}

static inline int32_t srem32(int32_t x, int32_t y) {
  return x % y;
}

static inline int64_t srem64(int64_t x, int64_t y) {
  return x % y;
}

static inline int8_t squot_safe8(int8_t x, int8_t y) {
  return y == 0 ? 0 : x / y;
}

static inline int16_t squot_safe16(int16_t x, int16_t y) {
  return y == 0 ? 0 : x / y;
}

static inline int32_t squot_safe32(int32_t x, int32_t y) {
  return y == 0 ? 0 : x / y;
}

static inline int64_t squot_safe64(int64_t x, int64_t y) {
  return y == 0 ? 0 : x / y;
}

static inline int8_t srem_safe8(int8_t x, int8_t y) {
  return y == 0 ? 0 : x % y;
}

static inline int16_t srem_safe16(int16_t x, int16_t y) {
  return y == 0 ? 0 : x % y;
}

static inline int32_t srem_safe32(int32_t x, int32_t y) {
  return y == 0 ? 0 : x % y;
}

static inline int64_t srem_safe64(int64_t x, int64_t y) {
  return y == 0 ? 0 : x % y;
}

static inline int8_t smin8(int8_t x, int8_t y) {
  return x < y ? x : y;
}

static inline int16_t smin16(int16_t x, int16_t y) {
  return x < y ? x : y;
}

static inline int32_t smin32(int32_t x, int32_t y) {
  return x < y ? x : y;
}

static inline int64_t smin64(int64_t x, int64_t y) {
  return x < y ? x : y;
}

static inline uint8_t umin8(uint8_t x, uint8_t y) {
  return x < y ? x : y;
}

static inline uint16_t umin16(uint16_t x, uint16_t y) {
  return x < y ? x : y;
}

static inline uint32_t umin32(uint32_t x, uint32_t y) {
  return x < y ? x : y;
}

static inline uint64_t umin64(uint64_t x, uint64_t y) {
  return x < y ? x : y;
}

static inline int8_t smax8(int8_t x, int8_t y) {
  return x < y ? y : x;
}

static inline int16_t smax16(int16_t x, int16_t y) {
  return x < y ? y : x;
}

static inline int32_t smax32(int32_t x, int32_t y) {
  return x < y ? y : x;
}

static inline int64_t smax64(int64_t x, int64_t y) {
  return x < y ? y : x;
}

static inline uint8_t umax8(uint8_t x, uint8_t y) {
  return x < y ? y : x;
}

static inline uint16_t umax16(uint16_t x, uint16_t y) {
  return x < y ? y : x;
}

static inline uint32_t umax32(uint32_t x, uint32_t y) {
  return x < y ? y : x;
}

static inline uint64_t umax64(uint64_t x, uint64_t y) {
  return x < y ? y : x;
}

static inline uint8_t shl8(uint8_t x, uint8_t y) {
  return (uint8_t)(x << y);
}

static inline uint16_t shl16(uint16_t x, uint16_t y) {
  return (uint16_t)(x << y);
}

static inline uint32_t shl32(uint32_t x, uint32_t y) {
  return x << y;
}

static inline uint64_t shl64(uint64_t x, uint64_t y) {
  return x << y;
}

static inline uint8_t lshr8(uint8_t x, uint8_t y) {
  return x >> y;
}

static inline uint16_t lshr16(uint16_t x, uint16_t y) {
  return x >> y;
}

static inline uint32_t lshr32(uint32_t x, uint32_t y) {
  return x >> y;
}

static inline uint64_t lshr64(uint64_t x, uint64_t y) {
  return x >> y;
}

static inline int8_t ashr8(int8_t x, int8_t y) {
  return x >> y;
}

static inline int16_t ashr16(int16_t x, int16_t y) {
  return x >> y;
}

static inline int32_t ashr32(int32_t x, int32_t y) {
  return x >> y;
}

static inline int64_t ashr64(int64_t x, int64_t y) {
  return x >> y;
}

static inline uint8_t and8(uint8_t x, uint8_t y) {
  return x & y;
}

static inline uint16_t and16(uint16_t x, uint16_t y) {
  return x & y;
}

static inline uint32_t and32(uint32_t x, uint32_t y) {
  return x & y;
}

static inline uint64_t and64(uint64_t x, uint64_t y) {
  return x & y;
}

static inline uint8_t or8(uint8_t x, uint8_t y) {
  return x | y;
}

static inline uint16_t or16(uint16_t x, uint16_t y) {
  return x | y;
}

static inline uint32_t or32(uint32_t x, uint32_t y) {
  return x | y;
}

static inline uint64_t or64(uint64_t x, uint64_t y) {
  return x | y;
}

static inline uint8_t xor8(uint8_t x, uint8_t y) {
  return x ^ y;
}

static inline uint16_t xor16(uint16_t x, uint16_t y) {
  return x ^ y;
}

static inline uint32_t xor32(uint32_t x, uint32_t y) {
  return x ^ y;
}

static inline uint64_t xor64(uint64_t x, uint64_t y) {
  return x ^ y;
}

static inline bool ult8(uint8_t x, uint8_t y) {
  return x < y;
}

static inline bool ult16(uint16_t x, uint16_t y) {
  return x < y;
}

static inline bool ult32(uint32_t x, uint32_t y) {
  return x < y;
}

static inline bool ult64(uint64_t x, uint64_t y) {
  return x < y;
}

static inline bool ule8(uint8_t x, uint8_t y) {
  return x <= y;
}

static inline bool ule16(uint16_t x, uint16_t y) {
  return x <= y;
}

static inline bool ule32(uint32_t x, uint32_t y) {
  return x <= y;
}

static inline bool ule64(uint64_t x, uint64_t y) {
  return x <= y;
}

static inline bool slt8(int8_t x, int8_t y) {
  return x < y;
}

static inline bool slt16(int16_t x, int16_t y) {
  return x < y;
}

static inline bool slt32(int32_t x, int32_t y) {
  return x < y;
}

static inline bool slt64(int64_t x, int64_t y) {
  return x < y;
}

static inline bool sle8(int8_t x, int8_t y) {
  return x <= y;
}

static inline bool sle16(int16_t x, int16_t y) {
  return x <= y;
}

static inline bool sle32(int32_t x, int32_t y) {
  return x <= y;
}

static inline bool sle64(int64_t x, int64_t y) {
  return x <= y;
}

static inline uint8_t pow8(uint8_t x, uint8_t y) {
  uint8_t res = 1, rem = y;

  while (rem != 0) {
    if (rem & 1)
      res *= x;
    rem >>= 1;
    x *= x;
  }
  return res;
}

static inline uint16_t pow16(uint16_t x, uint16_t y) {
  uint16_t res = 1, rem = y;

  while (rem != 0) {
    if (rem & 1)
      res *= x;
    rem >>= 1;
    x *= x;
  }
  return res;
}

static inline uint32_t pow32(uint32_t x, uint32_t y) {
  uint32_t res = 1, rem = y;

  while (rem != 0) {
    if (rem & 1)
      res *= x;
    rem >>= 1;
    x *= x;
  }
  return res;
}

static inline uint64_t pow64(uint64_t x, uint64_t y) {
  uint64_t res = 1, rem = y;

  while (rem != 0) {
    if (rem & 1)
      res *= x;
    rem >>= 1;
    x *= x;
  }
  return res;
}

static inline bool itob_i8_bool(int8_t x) {
  return x;
}

static inline bool itob_i16_bool(int16_t x) {
  return x;
}

static inline bool itob_i32_bool(int32_t x) {
  return x;
}

static inline bool itob_i64_bool(int64_t x) {
  return x;
}

static inline int8_t btoi_bool_i8(bool x) {
  return x;
}

static inline int16_t btoi_bool_i16(bool x) {
  return x;
}

static inline int32_t btoi_bool_i32(bool x) {
  return x;
}

static inline int64_t btoi_bool_i64(bool x) {
  return x;
}

#define sext_i8_i8(x) ((int8_t) (int8_t) (x))
#define sext_i8_i16(x) ((int16_t) (int8_t) (x))
#define sext_i8_i32(x) ((int32_t) (int8_t) (x))
#define sext_i8_i64(x) ((int64_t) (int8_t) (x))
#define sext_i16_i8(x) ((int8_t) (int16_t) (x))
#define sext_i16_i16(x) ((int16_t) (int16_t) (x))
#define sext_i16_i32(x) ((int32_t) (int16_t) (x))
#define sext_i16_i64(x) ((int64_t) (int16_t) (x))
#define sext_i32_i8(x) ((int8_t) (int32_t) (x))
#define sext_i32_i16(x) ((int16_t) (int32_t) (x))
#define sext_i32_i32(x) ((int32_t) (int32_t) (x))
#define sext_i32_i64(x) ((int64_t) (int32_t) (x))
#define sext_i64_i8(x) ((int8_t) (int64_t) (x))
#define sext_i64_i16(x) ((int16_t) (int64_t) (x))
#define sext_i64_i32(x) ((int32_t) (int64_t) (x))
#define sext_i64_i64(x) ((int64_t) (int64_t) (x))
#define zext_i8_i8(x) ((int8_t) (uint8_t) (x))
#define zext_i8_i16(x) ((int16_t) (uint8_t) (x))
#define zext_i8_i32(x) ((int32_t) (uint8_t) (x))
#define zext_i8_i64(x) ((int64_t) (uint8_t) (x))
#define zext_i16_i8(x) ((int8_t) (uint16_t) (x))
#define zext_i16_i16(x) ((int16_t) (uint16_t) (x))
#define zext_i16_i32(x) ((int32_t) (uint16_t) (x))
#define zext_i16_i64(x) ((int64_t) (uint16_t) (x))
#define zext_i32_i8(x) ((int8_t) (uint32_t) (x))
#define zext_i32_i16(x) ((int16_t) (uint32_t) (x))
#define zext_i32_i32(x) ((int32_t) (uint32_t) (x))
#define zext_i32_i64(x) ((int64_t) (uint32_t) (x))
#define zext_i64_i8(x) ((int8_t) (uint64_t) (x))
#define zext_i64_i16(x) ((int16_t) (uint64_t) (x))
#define zext_i64_i32(x) ((int32_t) (uint64_t) (x))
#define zext_i64_i64(x) ((int64_t) (uint64_t) (x))

static int8_t abs8(int8_t x) {
  return (int8_t)abs(x);
}

static int16_t abs16(int16_t x) {
  return (int16_t)abs(x);
}

static int32_t abs32(int32_t x) {
  return abs(x);
}

static int64_t abs64(int64_t x) {
#if defined(__OPENCL_VERSION__)
  return abs(x);
#else
  return llabs(x);
#endif
}

#if defined(__OPENCL_VERSION__)
static int32_t futrts_popc8(int8_t x) {
  return popcount(x);
}

static int32_t futrts_popc16(int16_t x) {
  return popcount(x);
}

static int32_t futrts_popc32(int32_t x) {
  return popcount(x);
}

static int32_t futrts_popc64(int64_t x) {
  return popcount(x);
}
#elif defined(__CUDA_ARCH__)

static int32_t futrts_popc8(int8_t x) {
  return __popc(zext_i8_i32(x));
}

static int32_t futrts_popc16(int16_t x) {
  return __popc(zext_i16_i32(x));
}

static int32_t futrts_popc32(int32_t x) {
  return __popc(x);
}

static int32_t futrts_popc64(int64_t x) {
  return __popcll(x);
}

#else // Not OpenCL or CUDA, but plain C.

static int32_t futrts_popc8(uint8_t x) {
  int c = 0;
  for (; x; ++c) { x &= x - 1; }
  return c;
}

static int32_t futrts_popc16(uint16_t x) {
  int c = 0;
  for (; x; ++c) { x &= x - 1; }
  return c;
}

static int32_t futrts_popc32(uint32_t x) {
  int c = 0;
  for (; x; ++c) { x &= x - 1; }
  return c;
}

static int32_t futrts_popc64(uint64_t x) {
  int c = 0;
  for (; x; ++c) { x &= x - 1; }
  return c;
}
#endif

#if defined(__OPENCL_VERSION__)
static uint8_t futrts_mul_hi8(uint8_t a, uint8_t b) {
  return mul_hi(a, b);
}

static uint16_t futrts_mul_hi16(uint16_t a, uint16_t b) {
  return mul_hi(a, b);
}

static uint32_t futrts_mul_hi32(uint32_t a, uint32_t b) {
  return mul_hi(a, b);
}

static uint64_t futrts_mul_hi64(uint64_t a, uint64_t b) {
  return mul_hi(a, b);
}

#elif defined(__CUDA_ARCH__)

static uint8_t futrts_mul_hi8(uint8_t a, uint8_t b) {
  uint16_t aa = a;
  uint16_t bb = b;

  return aa * bb >> 8;
}

static uint16_t futrts_mul_hi16(uint16_t a, uint16_t b) {
  uint32_t aa = a;
  uint32_t bb = b;

  return aa * bb >> 16;
}

static uint32_t futrts_mul_hi32(uint32_t a, uint32_t b) {
  return mulhi(a, b);
}

static uint64_t futrts_mul_hi64(uint64_t a, uint64_t b) {
  return mul64hi(a, b);
}

#else // Not OpenCL or CUDA, but plain C.

static uint8_t futrts_mul_hi8(uint8_t a, uint8_t b) {
  uint16_t aa = a;
  uint16_t bb = b;

  return aa * bb >> 8;
}

static uint16_t futrts_mul_hi16(uint16_t a, uint16_t b) {
  uint32_t aa = a;
  uint32_t bb = b;

  return aa * bb >> 16;
}

static uint32_t futrts_mul_hi32(uint32_t a, uint32_t b) {
  uint64_t aa = a;
  uint64_t bb = b;

  return aa * bb >> 32;
}

static uint64_t futrts_mul_hi64(uint64_t a, uint64_t b) {
  __uint128_t aa = a;
  __uint128_t bb = b;

  return aa * bb >> 64;
}
#endif

#if defined(__OPENCL_VERSION__)
static uint8_t futrts_mad_hi8(uint8_t a, uint8_t b, uint8_t c) {
  return mad_hi(a, b, c);
}

static uint16_t futrts_mad_hi16(uint16_t a, uint16_t b, uint16_t c) {
  return mad_hi(a, b, c);
}

static uint32_t futrts_mad_hi32(uint32_t a, uint32_t b, uint32_t c) {
  return mad_hi(a, b, c);
}

static uint64_t futrts_mad_hi64(uint64_t a, uint64_t b, uint64_t c) {
  return mad_hi(a, b, c);
}

#else // Not OpenCL

static uint8_t futrts_mad_hi8(uint8_t a, uint8_t b, uint8_t c) {
  return futrts_mul_hi8(a, b) + c;
}

static uint16_t futrts_mad_hi16(uint16_t a, uint16_t b, uint16_t c) {
  return futrts_mul_hi16(a, b) + c;
}

static uint32_t futrts_mad_hi32(uint32_t a, uint32_t b, uint32_t c) {
  return futrts_mul_hi32(a, b) + c;
}

static uint64_t futrts_mad_hi64(uint64_t a, uint64_t b, uint64_t c) {
  return futrts_mul_hi64(a, b) + c;
}
#endif

#if defined(__OPENCL_VERSION__)
static int32_t futrts_clzz8(int8_t x) {
  return clz(x);
}

static int32_t futrts_clzz16(int16_t x) {
  return clz(x);
}

static int32_t futrts_clzz32(int32_t x) {
  return clz(x);
}

static int32_t futrts_clzz64(int64_t x) {
  return clz(x);
}

#elif defined(__CUDA_ARCH__)

static int32_t futrts_clzz8(int8_t x) {
  return __clz(zext_i8_i32(x)) - 24;
}

static int32_t futrts_clzz16(int16_t x) {
  return __clz(zext_i16_i32(x)) - 16;
}

static int32_t futrts_clzz32(int32_t x) {
  return __clz(x);
}

static int32_t futrts_clzz64(int64_t x) {
  return __clzll(x);
}

#else // Not OpenCL or CUDA, but plain C.

static int32_t futrts_clzz8(int8_t x) {
  return x == 0 ? 8 : __builtin_clz((uint32_t)zext_i8_i32(x)) - 24;
}

static int32_t futrts_clzz16(int16_t x) {
  return x == 0 ? 16 : __builtin_clz((uint32_t)zext_i16_i32(x)) - 16;
}

static int32_t futrts_clzz32(int32_t x) {
  return x == 0 ? 32 : __builtin_clz((uint32_t)x);
}

static int32_t futrts_clzz64(int64_t x) {
  return x == 0 ? 64 : __builtin_clzll((uint64_t)x);
}
#endif

#if defined(__OPENCL_VERSION__)
static int32_t futrts_ctzz8(int8_t x) {
  int i = 0;
  for (; i < 8 && (x & 1) == 0; i++, x >>= 1)
    ;
  return i;
}

static int32_t futrts_ctzz16(int16_t x) {
  int i = 0;
  for (; i < 16 && (x & 1) == 0; i++, x >>= 1)
    ;
  return i;
}

static int32_t futrts_ctzz32(int32_t x) {
  int i = 0;
  for (; i < 32 && (x & 1) == 0; i++, x >>= 1)
    ;
  return i;
}

static int32_t futrts_ctzz64(int64_t x) {
  int i = 0;
  for (; i < 64 && (x & 1) == 0; i++, x >>= 1)
    ;
  return i;
}

#elif defined(__CUDA_ARCH__)

static int32_t futrts_ctzz8(int8_t x) {
  int y = __ffs(x);
  return y == 0 ? 8 : y - 1;
}

static int32_t futrts_ctzz16(int16_t x) {
  int y = __ffs(x);
  return y == 0 ? 16 : y - 1;
}

static int32_t futrts_ctzz32(int32_t x) {
  int y = __ffs(x);
  return y == 0 ? 32 : y - 1;
}

static int32_t futrts_ctzz64(int64_t x) {
  int y = __ffsll(x);
  return y == 0 ? 64 : y - 1;
}

#else // Not OpenCL or CUDA, but plain C.

static int32_t futrts_ctzz8(int8_t x) {
  return x == 0 ? 8 : __builtin_ctz((uint32_t)x);
}

static int32_t futrts_ctzz16(int16_t x) {
  return x == 0 ? 16 : __builtin_ctz((uint32_t)x);
}

static int32_t futrts_ctzz32(int32_t x) {
  return x == 0 ? 32 : __builtin_ctz((uint32_t)x);
}

static int32_t futrts_ctzz64(int64_t x) {
  return x == 0 ? 64 : __builtin_ctzll((uint64_t)x);
}
#endif

static inline float fdiv32(float x, float y) {
  return x / y;
}

static inline float fadd32(float x, float y) {
  return x + y;
}

static inline float fsub32(float x, float y) {
  return x - y;
}

static inline float fmul32(float x, float y) {
  return x * y;
}

static inline bool cmplt32(float x, float y) {
  return x < y;
}

static inline bool cmple32(float x, float y) {
  return x <= y;
}

static inline float sitofp_i8_f32(int8_t x) {
  return (float) x;
}

static inline float sitofp_i16_f32(int16_t x) {
  return (float) x;
}

static inline float sitofp_i32_f32(int32_t x) {
  return (float) x;
}

static inline float sitofp_i64_f32(int64_t x) {
  return (float) x;
}

static inline float uitofp_i8_f32(uint8_t x) {
  return (float) x;
}

static inline float uitofp_i16_f32(uint16_t x) {
  return (float) x;
}

static inline float uitofp_i32_f32(uint32_t x) {
  return (float) x;
}

static inline float uitofp_i64_f32(uint64_t x) {
  return (float) x;
}

#ifdef __OPENCL_VERSION__
static inline float fabs32(float x) {
  return fabs(x);
}

static inline float fmax32(float x, float y) {
  return fmax(x, y);
}

static inline float fmin32(float x, float y) {
  return fmin(x, y);
}

static inline float fpow32(float x, float y) {
  return pow(x, y);
}

#else // Not OpenCL, but CUDA or plain C.

static inline float fabs32(float x) {
  return fabsf(x);
}

static inline float fmax32(float x, float y) {
  return fmaxf(x, y);
}

static inline float fmin32(float x, float y) {
  return fminf(x, y);
}

static inline float fpow32(float x, float y) {
  return powf(x, y);
}
#endif

static inline bool futrts_isnan32(float x) {
  return isnan(x);
}

static inline bool futrts_isinf32(float x) {
  return isinf(x);
}

static inline int8_t fptosi_f32_i8(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (int8_t) x;
  }
}

static inline int16_t fptosi_f32_i16(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (int16_t) x;
  }
}

static inline int32_t fptosi_f32_i32(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (int32_t) x;
  }
}

static inline int64_t fptosi_f32_i64(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (int64_t) x;
  };
}

static inline uint8_t fptoui_f32_i8(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (uint8_t) (int8_t) x;
  }
}

static inline uint16_t fptoui_f32_i16(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (uint16_t) (int16_t) x;
  }
}

static inline uint32_t fptoui_f32_i32(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (uint32_t) (int32_t) x;
  }
}

static inline uint64_t fptoui_f32_i64(float x) {
  if (futrts_isnan32(x) || futrts_isinf32(x)) {
    return 0;
  } else {
    return (uint64_t) (int64_t) x;
  }
}

static inline bool ftob_f32_bool(float x) {
  return x != 0;
}

static inline float btof_bool_f32(bool x) {
  return x ? 1 : 0;
}

#ifdef __OPENCL_VERSION__
static inline float futrts_log32(float x) {
  return log(x);
}

static inline float futrts_log2_32(float x) {
  return log2(x);
}

static inline float futrts_log10_32(float x) {
  return log10(x);
}

static inline float futrts_sqrt32(float x) {
  return sqrt(x);
}

static inline float futrts_exp32(float x) {
  return exp(x);
}

static inline float futrts_cos32(float x) {
  return cos(x);
}

static inline float futrts_sin32(float x) {
  return sin(x);
}

static inline float futrts_tan32(float x) {
  return tan(x);
}

static inline float futrts_acos32(float x) {
  return acos(x);
}

static inline float futrts_asin32(float x) {
  return asin(x);
}

static inline float futrts_atan32(float x) {
  return atan(x);
}

static inline float futrts_cosh32(float x) {
  return cosh(x);
}

static inline float futrts_sinh32(float x) {
  return sinh(x);
}

static inline float futrts_tanh32(float x) {
  return tanh(x);
}

static inline float futrts_acosh32(float x) {
  return acosh(x);
}

static inline float futrts_asinh32(float x) {
  return asinh(x);
}

static inline float futrts_atanh32(float x) {
  return atanh(x);
}

static inline float futrts_atan2_32(float x, float y) {
  return atan2(x, y);
}

static inline float futrts_hypot32(float x, float y) {
  return hypot(x, y);
}

static inline float futrts_gamma32(float x) {
  return tgamma(x);
}

static inline float futrts_lgamma32(float x) {
  return lgamma(x);
}

static inline float fmod32(float x, float y) {
  return fmod(x, y);
}

static inline float futrts_round32(float x) {
  return rint(x);
}

static inline float futrts_floor32(float x) {
  return floor(x);
}

static inline float futrts_ceil32(float x) {
  return ceil(x);
}

static inline float futrts_lerp32(float v0, float v1, float t) {
  return mix(v0, v1, t);
}

static inline float futrts_mad32(float a, float b, float c) {
  return mad(a, b, c);
}

static inline float futrts_fma32(float a, float b, float c) {
  return fma(a, b, c);
}

#else // Not OpenCL, but CUDA or plain C.

static inline float futrts_log32(float x) {
  return logf(x);
}

static inline float futrts_log2_32(float x) {
  return log2f(x);
}

static inline float futrts_log10_32(float x) {
  return log10f(x);
}

static inline float futrts_sqrt32(float x) {
  return sqrtf(x);
}

static inline float futrts_exp32(float x) {
  return expf(x);
}

static inline float futrts_cos32(float x) {
  return cosf(x);
}

static inline float futrts_sin32(float x) {
  return sinf(x);
}

static inline float futrts_tan32(float x) {
  return tanf(x);
}

static inline float futrts_acos32(float x) {
  return acosf(x);
}

static inline float futrts_asin32(float x) {
  return asinf(x);
}

static inline float futrts_atan32(float x) {
  return atanf(x);
}

static inline float futrts_cosh32(float x) {
  return coshf(x);
}

static inline float futrts_sinh32(float x) {
  return sinhf(x);
}

static inline float futrts_tanh32(float x) {
  return tanhf(x);
}

static inline float futrts_acosh32(float x) {
  return acoshf(x);
}

static inline float futrts_asinh32(float x) {
  return asinhf(x);
}

static inline float futrts_atanh32(float x) {
  return atanhf(x);
}

static inline float futrts_atan2_32(float x, float y) {
  return atan2f(x, y);
}

static inline float futrts_hypot32(float x, float y) {
  return hypotf(x, y);
}

static inline float futrts_gamma32(float x) {
  return tgammaf(x);
}

static inline float futrts_lgamma32(float x) {
  return lgammaf(x);
}

static inline float fmod32(float x, float y) {
  return fmodf(x, y);
}

static inline float futrts_round32(float x) {
  return rintf(x);
}

static inline float futrts_floor32(float x) {
  return floorf(x);
}

static inline float futrts_ceil32(float x) {
  return ceilf(x);
}

static inline float futrts_lerp32(float v0, float v1, float t) {
  return v0 + (v1 - v0) * t;
}

static inline float futrts_mad32(float a, float b, float c) {
  return a * b + c;
}

static inline float futrts_fma32(float a, float b, float c) {
  return fmaf(a, b, c);
}
#endif

static inline int32_t futrts_to_bits32(float x) {
  union {
    float f;
    int32_t t;
  } p;

  p.f = x;
  return p.t;
}

static inline float futrts_from_bits32(int32_t x) {
  union {
    int32_t f;
    float t;
  } p;

  p.f = x;
  return p.t;
}

static inline float fsignum32(float x) {
  return futrts_isnan32(x) ? x : (x > 0) - (x < 0);
}

#ifdef FUTHARK_F64_ENABLED

static inline double fdiv64(double x, double y) {
  return x / y;
}

static inline double fadd64(double x, double y) {
  return x + y;
}

static inline double fsub64(double x, double y) {
  return x - y;
}

static inline double fmul64(double x, double y) {
  return x * y;
}

static inline bool cmplt64(double x, double y) {
  return x < y;
}

static inline bool cmple64(double x, double y) {
  return x <= y;
}

static inline double sitofp_i8_f64(int8_t x) {
  return (double) x;
}

static inline double sitofp_i16_f64(int16_t x) {
  return (double) x;
}

static inline double sitofp_i32_f64(int32_t x) {
  return (double) x;
}

static inline double sitofp_i64_f64(int64_t x) {
  return (double) x;
}

static inline double uitofp_i8_f64(uint8_t x) {
  return (double) x;
}

static inline double uitofp_i16_f64(uint16_t x) {
  return (double) x;
}

static inline double uitofp_i32_f64(uint32_t x) {
  return (double) x;
}

static inline double uitofp_i64_f64(uint64_t x) {
  return (double) x;
}

static inline double fabs64(double x) {
  return fabs(x);
}

static inline double fmax64(double x, double y) {
  return fmax(x, y);
}

static inline double fmin64(double x, double y) {
  return fmin(x, y);
}

static inline double fpow64(double x, double y) {
  return pow(x, y);
}

static inline double futrts_log64(double x) {
  return log(x);
}

static inline double futrts_log2_64(double x) {
  return log2(x);
}

static inline double futrts_log10_64(double x) {
  return log10(x);
}

static inline double futrts_sqrt64(double x) {
  return sqrt(x);
}

static inline double futrts_exp64(double x) {
  return exp(x);
}

static inline double futrts_cos64(double x) {
  return cos(x);
}

static inline double futrts_sin64(double x) {
  return sin(x);
}

static inline double futrts_tan64(double x) {
  return tan(x);
}

static inline double futrts_acos64(double x) {
  return acos(x);
}

static inline double futrts_asin64(double x) {
  return asin(x);
}

static inline double futrts_atan64(double x) {
  return atan(x);
}

static inline double futrts_cosh64(double x) {
  return cosh(x);
}

static inline double futrts_sinh64(double x) {
  return sinh(x);
}

static inline double futrts_tanh64(double x) {
  return tanh(x);
}

static inline double futrts_acosh64(double x) {
  return acosh(x);
}

static inline double futrts_asinh64(double x) {
  return asinh(x);
}

static inline double futrts_atanh64(double x) {
  return atanh(x);
}

static inline double futrts_atan2_64(double x, double y) {
  return atan2(x, y);
}

static inline double futrts_hypot64(double x, double y) {
  return hypot(x, y);
}

static inline double futrts_gamma64(double x) {
  return tgamma(x);
}

static inline double futrts_lgamma64(double x) {
  return lgamma(x);
}

static inline double futrts_fma64(double a, double b, double c) {
  return fma(a, b, c);
}

static inline double futrts_round64(double x) {
  return rint(x);
}

static inline double futrts_ceil64(double x) {
  return ceil(x);
}

static inline double futrts_floor64(double x) {
  return floor(x);
}

static inline bool futrts_isnan64(double x) {
  return isnan(x);
}

static inline bool futrts_isinf64(double x) {
  return isinf(x);
}

static inline int8_t fptosi_f64_i8(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (int8_t) x;
  }
}

static inline int16_t fptosi_f64_i16(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (int16_t) x;
  }
}

static inline int32_t fptosi_f64_i32(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (int32_t) x;
  }
}

static inline int64_t fptosi_f64_i64(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (int64_t) x;
  }
}

static inline uint8_t fptoui_f64_i8(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (uint8_t) (int8_t) x;
  }
}

static inline uint16_t fptoui_f64_i16(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (uint16_t) (int16_t) x;
  }
}

static inline uint32_t fptoui_f64_i32(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (uint32_t) (int32_t) x;
  }
}

static inline uint64_t fptoui_f64_i64(double x) {
  if (futrts_isnan64(x) || futrts_isinf64(x)) {
    return 0;
  } else {
    return (uint64_t) (int64_t) x;
  }
}

static inline bool ftob_f64_bool(double x) {
  return x != 0;
}

static inline double btof_bool_f64(bool x) {
  return x ? 1 : 0;
}

static inline int64_t futrts_to_bits64(double x) {
  union {
    double f;
    int64_t t;
  } p;

  p.f = x;
  return p.t;
}

static inline double futrts_from_bits64(int64_t x) {
  union {
    int64_t f;
    double t;
  } p;

  p.f = x;
  return p.t;
}

static inline double fmod64(double x, double y) {
  return fmod(x, y);
}

static inline double fsignum64(double x) {
  return futrts_isnan64(x) ? x : (x > 0) - (x < 0);
}

static inline double futrts_lerp64(double v0, double v1, double t) {
#ifdef __OPENCL_VERSION__
  return mix(v0, v1, t);
#else
  return v0 + (v1 - v0) * t;
#endif
}

static inline double futrts_mad64(double a, double b, double c) {
#ifdef __OPENCL_VERSION__
  return mad(a, b, c);
#else
  return a * b + c;
#endif
}

static inline float fpconv_f32_f32(float x) {
  return (float) x;
}

static inline double fpconv_f32_f64(float x) {
  return (double) x;
}

static inline float fpconv_f64_f32(double x) {
  return (float) x;
}

static inline double fpconv_f64_f64(double x) {
  return (double) x;
}

#endif

// End of scalar.h.
// Start of scalar_f16.h.

// Half-precision is emulated if needed (e.g. in straight C) with the
// native type used if possible.  The emulation works by typedef'ing
// 'float' to 'f16', and then implementing all operations on single
// precision.  To cut down on duplication, we use the same code for
// those Futhark functions that require just operators or casts.  The
// in-memory representation for arrays will still be 16 bits even
// under emulation, so the compiler will have to be careful when
// generating reads or writes.

#if !defined(cl_khr_fp16) && !(defined(__CUDA_ARCH__) && __CUDA_ARCH__ >= 600)
#define EMULATE_F16
#endif

#if !defined(EMULATE_F16) && defined(__OPENCL_VERSION__)
#pragma OPENCL EXTENSION cl_khr_fp16 : enable
#endif

#ifdef EMULATE_F16

// Note that the half-precision storage format is still 16 bits - the
// compiler will have to be real careful!
typedef float f16;

#else

#ifdef __CUDA_ARCH__
#include <cuda_fp16.h>
#endif

typedef half f16;

#endif

// Some of these functions convert to single precision because half
// precision versions are not available.

static inline f16 fadd16(f16 x, f16 y) {
  return x + y;
}

static inline f16 fsub16(f16 x, f16 y) {
  return x - y;
}

static inline f16 fmul16(f16 x, f16 y) {
  return x * y;
}

static inline bool cmplt16(f16 x, f16 y) {
  return x < y;
}

static inline bool cmple16(f16 x, f16 y) {
  return x <= y;
}

static inline f16 sitofp_i8_f16(int8_t x) {
  return (f16) x;
}

static inline f16 sitofp_i16_f16(int16_t x) {
  return (f16) x;
}

static inline f16 sitofp_i32_f16(int32_t x) {
  return (f16) x;
}

static inline f16 sitofp_i64_f16(int64_t x) {
  return (f16) x;
}

static inline f16 uitofp_i8_f16(uint8_t x) {
  return (f16) x;
}

static inline f16 uitofp_i16_f16(uint16_t x) {
  return (f16) x;
}

static inline f16 uitofp_i32_f16(uint32_t x) {
  return (f16) x;
}

static inline f16 uitofp_i64_f16(uint64_t x) {
  return (f16) x;
}

static inline int8_t fptosi_f16_i8(f16 x) {
  return (int8_t) (float) x;
}

static inline int16_t fptosi_f16_i16(f16 x) {
  return (int16_t) x;
}

static inline int32_t fptosi_f16_i32(f16 x) {
  return (int32_t) x;
}

static inline int64_t fptosi_f16_i64(f16 x) {
  return (int64_t) x;
}

static inline uint8_t fptoui_f16_i8(f16 x) {
  return (uint8_t) (float) x;
}

static inline uint16_t fptoui_f16_i16(f16 x) {
  return (uint16_t) x;
}

static inline uint32_t fptoui_f16_i32(f16 x) {
  return (uint32_t) x;
}

static inline uint64_t fptoui_f16_i64(f16 x) {
  return (uint64_t) x;
}

static inline bool ftob_f16_bool(f16 x) {
  return x != (f16)0;
}

static inline f16 btof_bool_f16(bool x) {
  return x ? 1 : 0;
}

#ifndef EMULATE_F16

#ifdef __OPENCL_VERSION__
static inline f16 fabs16(f16 x) {
  return fabs(x);
}

static inline f16 fmax16(f16 x, f16 y) {
  return fmax(x, y);
}

static inline f16 fmin16(f16 x, f16 y) {
  return fmin(x, y);
}

static inline f16 fpow16(f16 x, f16 y) {
  return pow(x, y);
}

#else // Assuming CUDA.

static inline f16 fabs16(f16 x) {
  return fabsf(x);
}

static inline f16 fmax16(f16 x, f16 y) {
  return fmaxf(x, y);
}

static inline f16 fmin16(f16 x, f16 y) {
  return fminf(x, y);
}

static inline f16 fpow16(f16 x, f16 y) {
  return powf(x, y);
}
#endif

static inline bool futrts_isnan16(f16 x) {
  return isnan((float)x);
}

static inline bool futrts_isinf16(f16 x) {
  return isinf((float)x);
}

#ifdef __OPENCL_VERSION__
static inline f16 futrts_log16(f16 x) {
  return log(x);
}

static inline f16 futrts_log2_16(f16 x) {
  return log2(x);
}

static inline f16 futrts_log10_16(f16 x) {
  return log10(x);
}

static inline f16 futrts_sqrt16(f16 x) {
  return sqrt(x);
}

static inline f16 futrts_exp16(f16 x) {
  return exp(x);
}

static inline f16 futrts_cos16(f16 x) {
  return cos(x);
}

static inline f16 futrts_sin16(f16 x) {
  return sin(x);
}

static inline f16 futrts_tan16(f16 x) {
  return tan(x);
}

static inline f16 futrts_acos16(f16 x) {
  return acos(x);
}

static inline f16 futrts_asin16(f16 x) {
  return asin(x);
}

static inline f16 futrts_atan16(f16 x) {
  return atan(x);
}

static inline f16 futrts_cosh16(f16 x) {
  return cosh(x);
}

static inline f16 futrts_sinh16(f16 x) {
  return sinh(x);
}

static inline f16 futrts_tanh16(f16 x) {
  return tanh(x);
}

static inline f16 futrts_acosh16(f16 x) {
  return acosh(x);
}

static inline f16 futrts_asinh16(f16 x) {
  return asinh(x);
}

static inline f16 futrts_atanh16(f16 x) {
  return atanh(x);
}

static inline f16 futrts_atan2_16(f16 x, f16 y) {
  return atan2(x, y);
}

static inline f16 futrts_hypot16(f16 x, f16 y) {
  return hypot(x, y);
}

static inline f16 futrts_gamma16(f16 x) {
  return tgamma(x);
}

static inline f16 futrts_lgamma16(f16 x) {
  return lgamma(x);
}

static inline f16 fmod16(f16 x, f16 y) {
  return fmod(x, y);
}

static inline f16 futrts_round16(f16 x) {
  return rint(x);
}

static inline f16 futrts_floor16(f16 x) {
  return floor(x);
}

static inline f16 futrts_ceil16(f16 x) {
  return ceil(x);
}

static inline f16 futrts_lerp16(f16 v0, f16 v1, f16 t) {
  return mix(v0, v1, t);
}

static inline f16 futrts_mad16(f16 a, f16 b, f16 c) {
  return mad(a, b, c);
}

static inline f16 futrts_fma16(f16 a, f16 b, f16 c) {
  return fma(a, b, c);
}

#else // Assume CUDA.

static inline f16 futrts_log16(f16 x) {
  return hlog(x);
}

static inline f16 futrts_log2_16(f16 x) {
  return hlog2(x);
}

static inline f16 futrts_log10_16(f16 x) {
  return hlog10(x);
}

static inline f16 futrts_sqrt16(f16 x) {
  return hsqrt(x);
}

static inline f16 futrts_exp16(f16 x) {
  return hexp(x);
}

static inline f16 futrts_cos16(f16 x) {
  return hcos(x);
}

static inline f16 futrts_sin16(f16 x) {
  return hsin(x);
}

static inline f16 futrts_tan16(f16 x) {
  return tanf(x);
}

static inline f16 futrts_acos16(f16 x) {
  return acosf(x);
}

static inline f16 futrts_asin16(f16 x) {
  return asinf(x);
}

static inline f16 futrts_atan16(f16 x) {
  return atanf(x);
}

static inline f16 futrts_cosh16(f16 x) {
  return coshf(x);
}

static inline f16 futrts_sinh16(f16 x) {
  return sinhf(x);
}

static inline f16 futrts_tanh16(f16 x) {
  return tanhf(x);
}

static inline f16 futrts_acosh16(f16 x) {
  return acoshf(x);
}

static inline f16 futrts_asinh16(f16 x) {
  return asinhf(x);
}

static inline f16 futrts_atanh16(f16 x) {
  return atanhf(x);
}

static inline f16 futrts_atan2_16(f16 x, f16 y) {
  return atan2f(x, y);
}

static inline f16 futrts_hypot16(f16 x, f16 y) {
  return hypotf(x, y);
}

static inline f16 futrts_gamma16(f16 x) {
  return tgammaf(x);
}

static inline f16 futrts_lgamma16(f16 x) {
  return lgammaf(x);
}

static inline f16 fmod16(f16 x, f16 y) {
  return fmodf(x, y);
}

static inline f16 futrts_round16(f16 x) {
  return rintf(x);
}

static inline f16 futrts_floor16(f16 x) {
  return hfloor(x);
}

static inline f16 futrts_ceil16(f16 x) {
  return hceil(x);
}

static inline f16 futrts_lerp16(f16 v0, f16 v1, f16 t) {
  return v0 + (v1 - v0) * t;
}

static inline f16 futrts_mad16(f16 a, f16 b, f16 c) {
  return a * b + c;
}

static inline f16 futrts_fma16(f16 a, f16 b, f16 c) {
  return fmaf(a, b, c);
}

#endif

// The CUDA __half type cannot be put in unions for some reason, so we
// use bespoke conversion functions instead.
#ifdef __CUDA_ARCH__
static inline int16_t futrts_to_bits16(f16 x) {
  return __half_as_ushort(x);
}
static inline f16 futrts_from_bits16(int16_t x) {
  return __ushort_as_half(x);
}
#else
static inline int16_t futrts_to_bits16(f16 x) {
  union {
    f16 f;
    int16_t t;
  } p;

  p.f = x;
  return p.t;
}

static inline f16 futrts_from_bits16(int16_t x) {
  union {
    int16_t f;
    f16 t;
  } p;

  p.f = x;
  return p.t;
}
#endif

#else // No native f16 - emulate.

static inline f16 fabs16(f16 x) {
  return fabs32(x);
}

static inline f16 fmax16(f16 x, f16 y) {
  return fmax32(x, y);
}

static inline f16 fmin16(f16 x, f16 y) {
  return fmin32(x, y);
}

static inline f16 fpow16(f16 x, f16 y) {
  return fpow32(x, y);
}

static inline bool futrts_isnan16(f16 x) {
  return futrts_isnan32(x);
}

static inline bool futrts_isinf16(f16 x) {
  return futrts_isinf32(x);
}

static inline f16 futrts_log16(f16 x) {
  return futrts_log32(x);
}

static inline f16 futrts_log2_16(f16 x) {
  return futrts_log2_32(x);
}

static inline f16 futrts_log10_16(f16 x) {
  return futrts_log10_32(x);
}

static inline f16 futrts_sqrt16(f16 x) {
  return futrts_sqrt32(x);
}

static inline f16 futrts_exp16(f16 x) {
  return futrts_exp32(x);
}

static inline f16 futrts_cos16(f16 x) {
  return futrts_cos32(x);
}

static inline f16 futrts_sin16(f16 x) {
  return futrts_sin32(x);
}

static inline f16 futrts_tan16(f16 x) {
  return futrts_tan32(x);
}

static inline f16 futrts_acos16(f16 x) {
  return futrts_acos32(x);
}

static inline f16 futrts_asin16(f16 x) {
  return futrts_asin32(x);
}

static inline f16 futrts_atan16(f16 x) {
  return futrts_atan32(x);
}

static inline f16 futrts_cosh16(f16 x) {
  return futrts_cosh32(x);
}

static inline f16 futrts_sinh16(f16 x) {
  return futrts_sinh32(x);
}

static inline f16 futrts_tanh16(f16 x) {
  return futrts_tanh32(x);
}

static inline f16 futrts_acosh16(f16 x) {
  return futrts_acosh32(x);
}

static inline f16 futrts_asinh16(f16 x) {
  return futrts_asinh32(x);
}

static inline f16 futrts_atanh16(f16 x) {
  return futrts_atanh32(x);
}

static inline f16 futrts_atan2_16(f16 x, f16 y) {
  return futrts_atan2_32(x, y);
}

static inline f16 futrts_hypot16(f16 x, f16 y) {
  return futrts_hypot32(x, y);
}

static inline f16 futrts_gamma16(f16 x) {
  return futrts_gamma32(x);
}

static inline f16 futrts_lgamma16(f16 x) {
  return futrts_lgamma32(x);
}

static inline f16 fmod16(f16 x, f16 y) {
  return fmod32(x, y);
}

static inline f16 futrts_round16(f16 x) {
  return futrts_round32(x);
}

static inline f16 futrts_floor16(f16 x) {
  return futrts_floor32(x);
}

static inline f16 futrts_ceil16(f16 x) {
  return futrts_ceil32(x);
}

static inline f16 futrts_lerp16(f16 v0, f16 v1, f16 t) {
  return futrts_lerp32(v0, v1, t);
}

static inline f16 futrts_mad16(f16 a, f16 b, f16 c) {
  return futrts_mad32(a, b, c);
}

static inline f16 futrts_fma16(f16 a, f16 b, f16 c) {
  return futrts_fma32(a, b, c);
}

// Even when we are using an OpenCL that does not support cl_khr_fp16,
// it must still support vload_half for actually creating a
// half-precision number, which can then be efficiently converted to a
// float.  Similarly for vstore_half.
#ifdef __OPENCL_VERSION__

static inline int16_t futrts_to_bits16(f16 x) {
  int16_t y;
  // Violating strict aliasing here.
  vstore_half((float)x, 0, (half*)&y);
  return y;
}

static inline f16 futrts_from_bits16(int16_t x) {
  return (f16)vload_half(0, (half*)&x);
}

#else

static inline int16_t futrts_to_bits16(f16 x) {
  return (int16_t)float2halfbits(x);
}

static inline f16 futrts_from_bits16(int16_t x) {
  return halfbits2float((uint16_t)x);
}

static inline f16 fsignum16(f16 x) {
  return futrts_isnan16(x) ? x : (x > 0) - (x < 0);
}

#endif

#endif

static inline float fpconv_f16_f16(f16 x) {
  return x;
}

static inline float fpconv_f16_f32(f16 x) {
  return x;
}

static inline f16 fpconv_f32_f16(float x) {
  return x;
}

#ifdef FUTHARK_F64_ENABLED

static inline double fpconv_f16_f64(f16 x) {
  return (double) x;
}

static inline f16 fpconv_f64_f16(double x) {
  return (f16) x;
}

#endif


// End of scalar_f16.h.

static int init_constants(struct futhark_context *);
static int free_constants(struct futhark_context *);
struct memblock {
    int *references;
    unsigned char *mem;
    int64_t size;
    const char *desc;
};
struct futhark_context_config {
    int debugging;
    int in_use;
};
struct futhark_context_config *futhark_context_config_new(void)
{
    struct futhark_context_config *cfg =
                                  (struct futhark_context_config *) malloc(sizeof(struct futhark_context_config));
    
    if (cfg == NULL)
        return NULL;
    cfg->in_use = 0;
    cfg->debugging = 0;
    return cfg;
}
void futhark_context_config_free(struct futhark_context_config *cfg)
{
    assert(!cfg->in_use);
    free(cfg);
}
void futhark_context_config_set_debugging(struct futhark_context_config *cfg,
                                          int detail)
{
    cfg->debugging = detail;
}
void futhark_context_config_set_profiling(struct futhark_context_config *cfg,
                                          int flag)
{
    (void) cfg;
    (void) flag;
}
void futhark_context_config_set_logging(struct futhark_context_config *cfg,
                                        int detail)
{
    // Does nothing for this backend.
    (void) cfg;
    (void) detail;
}
struct futhark_context {
    struct futhark_context_config *cfg;
    int detail_memory;
    int debugging;
    int profiling;
    int logging;
    lock_t lock;
    char *error;
    FILE *log;
    int profiling_paused;
    int64_t peak_mem_usage_default;
    int64_t cur_mem_usage_default;
    struct {
        int dummy;
    } constants;
};
struct futhark_context *futhark_context_new(struct futhark_context_config *cfg)
{
    assert(!cfg->in_use);
    
    struct futhark_context *ctx =
                           (struct futhark_context *) malloc(sizeof(struct futhark_context));
    
    if (ctx == NULL)
        return NULL;
    ctx->cfg = cfg;
    ctx->cfg->in_use = 1;
    ctx->detail_memory = cfg->debugging;
    ctx->debugging = cfg->debugging;
    ctx->profiling = cfg->debugging;
    ctx->logging = cfg->debugging;
    ctx->error = NULL;
    ctx->log = stderr;
    create_lock(&ctx->lock);
    ctx->peak_mem_usage_default = 0;
    ctx->cur_mem_usage_default = 0;
    init_constants(ctx);
    return ctx;
}
void futhark_context_free(struct futhark_context *ctx)
{
    free_constants(ctx);
    free_lock(&ctx->lock);
    ctx->cfg->in_use = 0;
    free(ctx);
}
int futhark_context_sync(struct futhark_context *ctx)
{
    (void) ctx;
    return 0;
}
static const char *tuning_param_names[0];
static const char *tuning_param_vars[0];
static const char *tuning_param_classes[0];
int futhark_context_config_set_tuning_param(struct futhark_context_config *cfg,
                                            const char *param_name,
                                            size_t param_value)
{
    (void) cfg;
    (void) param_name;
    (void) param_value;
    return 1;
}
static int memblock_unref(struct futhark_context *ctx, struct memblock *block,
                          const char *desc)
{
    if (block->references != NULL) {
        *block->references -= 1;
        if (ctx->detail_memory)
            fprintf(ctx->log,
                    "Unreferencing block %s (allocated as %s) in %s: %d references remaining.\n",
                    desc, block->desc, "default space", *block->references);
        if (*block->references == 0) {
            ctx->cur_mem_usage_default -= block->size;
            free(block->mem);
            free(block->references);
            if (ctx->detail_memory)
                fprintf(ctx->log,
                        "%lld bytes freed (now allocated: %lld bytes)\n",
                        (long long) block->size,
                        (long long) ctx->cur_mem_usage_default);
        }
        block->references = NULL;
    }
    return 0;
}
static int memblock_alloc(struct futhark_context *ctx, struct memblock *block,
                          int64_t size, const char *desc)
{
    if (size < 0)
        futhark_panic(1,
                      "Negative allocation of %lld bytes attempted for %s in %s.\n",
                      (long long) size, desc, "default space",
                      ctx->cur_mem_usage_default);
    
    int ret = memblock_unref(ctx, block, desc);
    
    if (ret != FUTHARK_SUCCESS)
        return ret;
    if (ctx->detail_memory)
        fprintf(ctx->log,
                "Allocating %lld bytes for %s in %s (then allocated: %lld bytes)",
                (long long) size, desc, "default space",
                (long long) ctx->cur_mem_usage_default + size);
    if (ctx->cur_mem_usage_default > ctx->peak_mem_usage_default) {
        ctx->peak_mem_usage_default = ctx->cur_mem_usage_default;
        if (ctx->detail_memory)
            fprintf(ctx->log, " (new peak).\n");
    } else if (ctx->detail_memory)
        fprintf(ctx->log, ".\n");
    block->mem = (unsigned char *) malloc((size_t) size);
    if (ctx->error == NULL) {
        block->references = (int *) malloc(sizeof(int));
        *block->references = 1;
        block->size = size;
        block->desc = desc;
        ctx->cur_mem_usage_default += size;
        return FUTHARK_SUCCESS;
    } else {
        char *old_error = ctx->error;
        
        ctx->error =
            msgprintf("Failed to allocate memory in %s.\nAttempted allocation: %12lld bytes\nCurrently allocated:  %12lld bytes\n%s",
                      "default space", (long long) size,
                      (long long) ctx->cur_mem_usage_default, old_error);
        free(old_error);
        return FUTHARK_OUT_OF_MEMORY;
    }
}
static int memblock_set(struct futhark_context *ctx, struct memblock *lhs,
                        struct memblock *rhs, const char *lhs_desc)
{
    int ret = memblock_unref(ctx, lhs, lhs_desc);
    
    if (rhs->references != NULL)
        (*rhs->references)++;
    *lhs = *rhs;
    return ret;
}
int futhark_get_tuning_param_count(void)
{
    return sizeof(tuning_param_names) / sizeof(tuning_param_names[0]);
}
const char *futhark_get_tuning_param_name(int i)
{
    return tuning_param_names[i];
}
const char *futhark_get_tuning_param_class(int i)
{
    return tuning_param_classes[i];
}
char *futhark_context_report(struct futhark_context *ctx)
{
    if (futhark_context_sync(ctx) != 0)
        return NULL;
    
    struct str_builder builder;
    
    str_builder_init(&builder);
    if (ctx->detail_memory || ctx->profiling || ctx->logging) {
        { }
    }
    if (ctx->profiling) { }
    return builder.str;
}
char *futhark_context_get_error(struct futhark_context *ctx)
{
    char *error = ctx->error;
    
    ctx->error = NULL;
    return error;
}
void futhark_context_set_logging_file(struct futhark_context *ctx, FILE *f)
{
    ctx->log = f;
}
void futhark_context_pause_profiling(struct futhark_context *ctx)
{
    ctx->profiling_paused = 1;
}
void futhark_context_unpause_profiling(struct futhark_context *ctx)
{
    ctx->profiling_paused = 0;
}
int futhark_context_clear_caches(struct futhark_context *ctx)
{
    lock_lock(&ctx->lock);
    ctx->peak_mem_usage_default = 0;
    lock_unlock(&ctx->lock);
    return ctx->error != NULL;
}

static int futrts_entry_main(struct futhark_context *ctx,
                             struct memblock *mem_out_p_16473,
                             struct memblock dir_vs_mem_15982,
                             struct memblock md_cs_mem_15983,
                             struct memblock md_vols_mem_15984,
                             struct memblock md_drifts_mem_15985,
                             struct memblock md_sts_mem_15986,
                             struct memblock md_detvals_mem_15987,
                             struct memblock md_discts_mem_15988,
                             struct memblock bb_inds_mem_15989,
                             struct memblock bb_data_mem_15990, int64_t k_13569,
                             int64_t num_bits_13570, int64_t num_models_13571,
                             int64_t num_und_13572, int64_t num_dates_13573,
                             int64_t num_discts_13574,
                             int32_t contract_number_13575,
                             int32_t num_mc_it_13576);

static int init_constants(struct futhark_context *ctx)
{
    (void) ctx;
    
    int err = 0;
    
    
  cleanup:
    return err;
}
static int free_constants(struct futhark_context *ctx)
{
    (void) ctx;
    return 0;
}
struct futhark_i32_2d {
    struct memblock mem;
    int64_t shape[2];
};
struct futhark_i32_2d *futhark_new_i32_2d(struct futhark_context *ctx, const
                                          int32_t *data, int64_t dim0,
                                          int64_t dim1)
{
    struct futhark_i32_2d *bad = NULL;
    struct futhark_i32_2d *arr =
                          (struct futhark_i32_2d *) malloc(sizeof(struct futhark_i32_2d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * dim1 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    arr->shape[1] = dim1;
    if ((size_t) (dim0 * dim1) * 4 > 0)
        memmove(arr->mem.mem + 0, data + 0, (size_t) (dim0 * dim1) * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
struct futhark_i32_2d *futhark_new_raw_i32_2d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0,
                                              int64_t dim1)
{
    struct futhark_i32_2d *bad = NULL;
    struct futhark_i32_2d *arr =
                          (struct futhark_i32_2d *) malloc(sizeof(struct futhark_i32_2d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * dim1 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    arr->shape[1] = dim1;
    if ((size_t) (dim0 * dim1) * 4 > 0)
        memmove(arr->mem.mem + 0, data + offset, (size_t) (dim0 * dim1) * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
int futhark_free_i32_2d(struct futhark_context *ctx, struct futhark_i32_2d *arr)
{
    lock_lock(&ctx->lock);
    if (memblock_unref(ctx, &arr->mem, "arr->mem") != 0)
        return 1;
    lock_unlock(&ctx->lock);
    free(arr);
    return 0;
}
int futhark_values_i32_2d(struct futhark_context *ctx,
                          struct futhark_i32_2d *arr, int32_t *data)
{
    lock_lock(&ctx->lock);
    if ((size_t) (arr->shape[0] * arr->shape[1]) * 4 > 0)
        memmove(data + 0, arr->mem.mem + 0, (size_t) (arr->shape[0] *
                                                      arr->shape[1]) * 4);
    lock_unlock(&ctx->lock);
    return 0;
}
unsigned char *futhark_values_raw_i32_2d(struct futhark_context *ctx,
                                         struct futhark_i32_2d *arr)
{
    (void) ctx;
    return arr->mem.mem;
}
const int64_t *futhark_shape_i32_2d(struct futhark_context *ctx,
                                    struct futhark_i32_2d *arr)
{
    (void) ctx;
    return arr->shape;
}
struct futhark_f32_1d {
    struct memblock mem;
    int64_t shape[1];
};
struct futhark_f32_1d *futhark_new_f32_1d(struct futhark_context *ctx, const
                                          float *data, int64_t dim0)
{
    struct futhark_f32_1d *bad = NULL;
    struct futhark_f32_1d *arr =
                          (struct futhark_f32_1d *) malloc(sizeof(struct futhark_f32_1d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    if ((size_t) dim0 * 4 > 0)
        memmove(arr->mem.mem + 0, data + 0, (size_t) dim0 * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
struct futhark_f32_1d *futhark_new_raw_f32_1d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0)
{
    struct futhark_f32_1d *bad = NULL;
    struct futhark_f32_1d *arr =
                          (struct futhark_f32_1d *) malloc(sizeof(struct futhark_f32_1d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    if ((size_t) dim0 * 4 > 0)
        memmove(arr->mem.mem + 0, data + offset, (size_t) dim0 * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
int futhark_free_f32_1d(struct futhark_context *ctx, struct futhark_f32_1d *arr)
{
    lock_lock(&ctx->lock);
    if (memblock_unref(ctx, &arr->mem, "arr->mem") != 0)
        return 1;
    lock_unlock(&ctx->lock);
    free(arr);
    return 0;
}
int futhark_values_f32_1d(struct futhark_context *ctx,
                          struct futhark_f32_1d *arr, float *data)
{
    lock_lock(&ctx->lock);
    if ((size_t) arr->shape[0] * 4 > 0)
        memmove(data + 0, arr->mem.mem + 0, (size_t) arr->shape[0] * 4);
    lock_unlock(&ctx->lock);
    return 0;
}
unsigned char *futhark_values_raw_f32_1d(struct futhark_context *ctx,
                                         struct futhark_f32_1d *arr)
{
    (void) ctx;
    return arr->mem.mem;
}
const int64_t *futhark_shape_f32_1d(struct futhark_context *ctx,
                                    struct futhark_f32_1d *arr)
{
    (void) ctx;
    return arr->shape;
}
struct futhark_f32_2d {
    struct memblock mem;
    int64_t shape[2];
};
struct futhark_f32_2d *futhark_new_f32_2d(struct futhark_context *ctx, const
                                          float *data, int64_t dim0,
                                          int64_t dim1)
{
    struct futhark_f32_2d *bad = NULL;
    struct futhark_f32_2d *arr =
                          (struct futhark_f32_2d *) malloc(sizeof(struct futhark_f32_2d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * dim1 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    arr->shape[1] = dim1;
    if ((size_t) (dim0 * dim1) * 4 > 0)
        memmove(arr->mem.mem + 0, data + 0, (size_t) (dim0 * dim1) * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
struct futhark_f32_2d *futhark_new_raw_f32_2d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0,
                                              int64_t dim1)
{
    struct futhark_f32_2d *bad = NULL;
    struct futhark_f32_2d *arr =
                          (struct futhark_f32_2d *) malloc(sizeof(struct futhark_f32_2d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * dim1 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    arr->shape[1] = dim1;
    if ((size_t) (dim0 * dim1) * 4 > 0)
        memmove(arr->mem.mem + 0, data + offset, (size_t) (dim0 * dim1) * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
int futhark_free_f32_2d(struct futhark_context *ctx, struct futhark_f32_2d *arr)
{
    lock_lock(&ctx->lock);
    if (memblock_unref(ctx, &arr->mem, "arr->mem") != 0)
        return 1;
    lock_unlock(&ctx->lock);
    free(arr);
    return 0;
}
int futhark_values_f32_2d(struct futhark_context *ctx,
                          struct futhark_f32_2d *arr, float *data)
{
    lock_lock(&ctx->lock);
    if ((size_t) (arr->shape[0] * arr->shape[1]) * 4 > 0)
        memmove(data + 0, arr->mem.mem + 0, (size_t) (arr->shape[0] *
                                                      arr->shape[1]) * 4);
    lock_unlock(&ctx->lock);
    return 0;
}
unsigned char *futhark_values_raw_f32_2d(struct futhark_context *ctx,
                                         struct futhark_f32_2d *arr)
{
    (void) ctx;
    return arr->mem.mem;
}
const int64_t *futhark_shape_f32_2d(struct futhark_context *ctx,
                                    struct futhark_f32_2d *arr)
{
    (void) ctx;
    return arr->shape;
}
struct futhark_f32_3d {
    struct memblock mem;
    int64_t shape[3];
};
struct futhark_f32_3d *futhark_new_f32_3d(struct futhark_context *ctx, const
                                          float *data, int64_t dim0,
                                          int64_t dim1, int64_t dim2)
{
    struct futhark_f32_3d *bad = NULL;
    struct futhark_f32_3d *arr =
                          (struct futhark_f32_3d *) malloc(sizeof(struct futhark_f32_3d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * dim1 * dim2 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    arr->shape[1] = dim1;
    arr->shape[2] = dim2;
    if ((size_t) (dim0 * dim1 * dim2) * 4 > 0)
        memmove(arr->mem.mem + 0, data + 0, (size_t) (dim0 * dim1 * dim2) * 4);
    lock_unlock(&ctx->lock);
    return arr;
}
struct futhark_f32_3d *futhark_new_raw_f32_3d(struct futhark_context *ctx, const
                                              unsigned char *data,
                                              int64_t offset, int64_t dim0,
                                              int64_t dim1, int64_t dim2)
{
    struct futhark_f32_3d *bad = NULL;
    struct futhark_f32_3d *arr =
                          (struct futhark_f32_3d *) malloc(sizeof(struct futhark_f32_3d));
    
    if (arr == NULL)
        return bad;
    lock_lock(&ctx->lock);
    arr->mem.references = NULL;
    if (memblock_alloc(ctx, &arr->mem, dim0 * dim1 * dim2 * 4, "arr->mem"))
        return NULL;
    arr->shape[0] = dim0;
    arr->shape[1] = dim1;
    arr->shape[2] = dim2;
    if ((size_t) (dim0 * dim1 * dim2) * 4 > 0)
        memmove(arr->mem.mem + 0, data + offset, (size_t) (dim0 * dim1 * dim2) *
                4);
    lock_unlock(&ctx->lock);
    return arr;
}
int futhark_free_f32_3d(struct futhark_context *ctx, struct futhark_f32_3d *arr)
{
    lock_lock(&ctx->lock);
    if (memblock_unref(ctx, &arr->mem, "arr->mem") != 0)
        return 1;
    lock_unlock(&ctx->lock);
    free(arr);
    return 0;
}
int futhark_values_f32_3d(struct futhark_context *ctx,
                          struct futhark_f32_3d *arr, float *data)
{
    lock_lock(&ctx->lock);
    if ((size_t) (arr->shape[0] * arr->shape[1] * arr->shape[2]) * 4 > 0)
        memmove(data + 0, arr->mem.mem + 0, (size_t) (arr->shape[0] *
                                                      arr->shape[1] *
                                                      arr->shape[2]) * 4);
    lock_unlock(&ctx->lock);
    return 0;
}
unsigned char *futhark_values_raw_f32_3d(struct futhark_context *ctx,
                                         struct futhark_f32_3d *arr)
{
    (void) ctx;
    return arr->mem.mem;
}
const int64_t *futhark_shape_f32_3d(struct futhark_context *ctx,
                                    struct futhark_f32_3d *arr)
{
    (void) ctx;
    return arr->shape;
}

static int futrts_entry_main(struct futhark_context *ctx,
                             struct memblock *mem_out_p_16473,
                             struct memblock dir_vs_mem_15982,
                             struct memblock md_cs_mem_15983,
                             struct memblock md_vols_mem_15984,
                             struct memblock md_drifts_mem_15985,
                             struct memblock md_sts_mem_15986,
                             struct memblock md_detvals_mem_15987,
                             struct memblock md_discts_mem_15988,
                             struct memblock bb_inds_mem_15989,
                             struct memblock bb_data_mem_15990, int64_t k_13569,
                             int64_t num_bits_13570, int64_t num_models_13571,
                             int64_t num_und_13572, int64_t num_dates_13573,
                             int64_t num_discts_13574,
                             int32_t contract_number_13575,
                             int32_t num_mc_it_13576)
{
    (void) ctx;
    
    int err = 0;
    size_t mem_15994_cached_sizze_16474 = 0;
    unsigned char *mem_15994 = NULL;
    size_t mem_16007_cached_sizze_16475 = 0;
    unsigned char *mem_16007 = NULL;
    size_t mem_16022_cached_sizze_16476 = 0;
    unsigned char *mem_16022 = NULL;
    size_t mem_16037_cached_sizze_16477 = 0;
    unsigned char *mem_16037 = NULL;
    size_t mem_16052_cached_sizze_16478 = 0;
    unsigned char *mem_16052 = NULL;
    size_t mem_16076_cached_sizze_16479 = 0;
    unsigned char *mem_16076 = NULL;
    size_t mem_16092_cached_sizze_16480 = 0;
    unsigned char *mem_16092 = NULL;
    size_t mem_16105_cached_sizze_16481 = 0;
    unsigned char *mem_16105 = NULL;
    size_t mem_16162_cached_sizze_16482 = 0;
    unsigned char *mem_16162 = NULL;
    size_t mem_16180_cached_sizze_16483 = 0;
    unsigned char *mem_16180 = NULL;
    size_t mem_16200_cached_sizze_16484 = 0;
    unsigned char *mem_16200 = NULL;
    size_t mem_16339_cached_sizze_16485 = 0;
    unsigned char *mem_16339 = NULL;
    size_t mem_16348_cached_sizze_16486 = 0;
    unsigned char *mem_16348 = NULL;
    size_t mem_16390_cached_sizze_16487 = 0;
    unsigned char *mem_16390 = NULL;
    struct memblock mem_16405;
    
    mem_16405.references = NULL;
    
    struct memblock mem_param_tmp_16452;
    
    mem_param_tmp_16452.references = NULL;
    
    struct memblock mem_16370;
    
    mem_16370.references = NULL;
    
    struct memblock mem_param_tmp_16460;
    
    mem_param_tmp_16460.references = NULL;
    
    struct memblock mem_16237;
    
    mem_16237.references = NULL;
    
    struct memblock mem_param_16185;
    
    mem_param_16185.references = NULL;
    
    struct memblock ext_mem_16241;
    
    ext_mem_16241.references = NULL;
    
    struct memblock mem_param_16071;
    
    mem_param_16071.references = NULL;
    
    struct memblock ext_mem_16383;
    
    ext_mem_16383.references = NULL;
    
    struct memblock mem_16066;
    
    mem_16066.references = NULL;
    
    struct memblock mem_16063;
    
    mem_16063.references = NULL;
    
    struct memblock mem_out_16444;
    
    mem_out_16444.references = NULL;
    
    int64_t sobvctszz_15079 = mul64(num_und_13572, num_dates_13573);
    bool dim_match_15080 = sobvctszz_15079 == k_13569;
    bool empty_or_match_cert_15081;
    
    if (!dim_match_15080) {
        ctx->error =
            msgprintf("Error: %s%lld%s%lld%s%lld%s%lld%s\n\nBacktrace:\n%s",
                      "Value of (core language) shape (", (long long) k_13569,
                      ", ", (long long) num_bits_13570,
                      ") cannot match shape of type `[",
                      (long long) sobvctszz_15079, "][",
                      (long long) num_bits_13570, "]i32`.",
                      "-> #0  sample_programs/OptionPricing.fut:335:16-48\n   #1  sample_programs/OptionPricing.fut:321:1-346:37\n");
        err = FUTHARK_PROGRAM_ERROR;
        goto cleanup;
    }
    
    int64_t i32_res_15083 = sext_i32_i64(num_mc_it_13576);
    bool bounds_invalid_upwards_15441 = slt64(i32_res_15083, (int64_t) 0);
    bool valid_15442 = !bounds_invalid_upwards_15441;
    bool range_valid_c_15443;
    
    if (!valid_15442) {
        ctx->error = msgprintf("Error: %s%lld%s%lld%s%lld%s\n\nBacktrace:\n%s",
                               "Range ", (long long) (int64_t) 0, "..",
                               (long long) (int64_t) 1, "..<",
                               (long long) i32_res_15083, " is invalid.",
                               "-> #0  /prelude/array.fut:90:3-10\n   #1  sample_programs/OptionPricing.fut:338:44-67\n   #2  sample_programs/OptionPricing.fut:321:1-346:37\n");
        err = FUTHARK_PROGRAM_ERROR;
        goto cleanup;
    }
    
    int64_t i64_arg_15094 = shl64((int64_t) 1, num_bits_13570);
    float i64_res_15095 = sitofp_i64_f32(i64_arg_15094);
    float sob_fact_15096 = 1.0F / i64_res_15095;
    int64_t binop_x_15991 = sobvctszz_15079 * i32_res_15083;
    int64_t binop_y_15992 = (int64_t) 4 * binop_x_15991;
    int64_t bytes_15993 = smax64((int64_t) 0, binop_y_15992);
    
    if (mem_15994_cached_sizze_16474 < bytes_15993) {
        err = lexical_realloc(&ctx->error, &mem_15994,
                              &mem_15994_cached_sizze_16474, bytes_15993);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    
    int64_t binop_y_16005 = (int64_t) 4 * sobvctszz_15079;
    int64_t bytes_16006 = smax64((int64_t) 0, binop_y_16005);
    
    if (mem_16007_cached_sizze_16475 < bytes_16006) {
        err = lexical_realloc(&ctx->error, &mem_16007,
                              &mem_16007_cached_sizze_16475, bytes_16006);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (mem_16022_cached_sizze_16476 < bytes_16006) {
        err = lexical_realloc(&ctx->error, &mem_16022,
                              &mem_16022_cached_sizze_16476, bytes_16006);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (mem_16037_cached_sizze_16477 < bytes_16006) {
        err = lexical_realloc(&ctx->error, &mem_16037,
                              &mem_16037_cached_sizze_16477, bytes_16006);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (mem_16052_cached_sizze_16478 < bytes_16006) {
        err = lexical_realloc(&ctx->error, &mem_16052,
                              &mem_16052_cached_sizze_16478, bytes_16006);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    for (int32_t i_15872 = 0; i_15872 < num_mc_it_13576; i_15872++) {
        int64_t i_15814 = sext_i32_i64(i_15872);
        int32_t sobolIndI_arg_15097 = add32(1, i_15872);
        int32_t x_15099 = ashr32(sobolIndI_arg_15097, 1);
        int32_t grayCode_res_15100 = sobolIndI_arg_15097 ^ x_15099;
        
        for (int64_t i_15792 = 0; i_15792 < sobvctszz_15079; i_15792++) {
            int32_t defunc_2_reduce_res_15111;
            int32_t redout_15788 = 0;
            
            for (int64_t i_15789 = 0; i_15789 < num_bits_13570; i_15789++) {
                int32_t x_15104;
                
                x_15104 = ((int32_t *) dir_vs_mem_15982.mem)[i_15792 *
                                                             num_bits_13570 +
                                                             i_15789];
                
                int32_t i64_res_15106 = sext_i64_i32(i_15789);
                int32_t t_15107 = shl32(1, i64_res_15106);
                int32_t x_15108 = grayCode_res_15100 & t_15107;
                bool testBit_res_15109 = x_15108 == t_15107;
                int32_t defunc_1_f_res_15110;
                
                if (testBit_res_15109) {
                    defunc_1_f_res_15110 = x_15104;
                } else {
                    defunc_1_f_res_15110 = 0;
                }
                
                int32_t defunc_1_op_res_15114 = defunc_1_f_res_15110 ^
                        redout_15788;
                int32_t redout_tmp_16447 = defunc_1_op_res_15114;
                
                redout_15788 = redout_tmp_16447;
            }
            defunc_2_reduce_res_15111 = redout_15788;
            ((int32_t *) mem_16007)[i_15792] = defunc_2_reduce_res_15111;
        }
        for (int64_t i_15911 = 0; i_15911 < sobvctszz_15079; i_15911++) {
            if ((int64_t) 4 > 0)
                memmove(mem_16022 + i_15911 * (int64_t) 4, mem_16007 +
                        ((int64_t) 0 + (int64_t) 1 * i_15911) * (int64_t) 4,
                        (int64_t) 4);
        }
        for (int64_t i_15924 = 0; i_15924 < sobvctszz_15079; i_15924++) {
            int32_t x_15926;
            
            x_15926 = ((int32_t *) mem_16022)[i_15924];
            
            float i32_res_15927 = sitofp_i32_f32(x_15926);
            float defunc_0_f_res_15928 = sob_fact_15096 * i32_res_15927;
            
            ((float *) mem_16037)[i_15924] = defunc_0_f_res_15928;
        }
        if (sobvctszz_15079 * (int64_t) 4 > 0)
            memmove(mem_16052 + (int64_t) 0, mem_16037 + (int64_t) 0,
                    sobvctszz_15079 * (int64_t) 4);
        if (sobvctszz_15079 * (int64_t) 4 > 0)
            memmove(mem_15994 + sobvctszz_15079 * i_15814 * (int64_t) 4,
                    mem_16052 + (int64_t) 0, sobvctszz_15079 * (int64_t) 4);
    }
    
    int64_t binop_y_16061 = (int64_t) 4 * num_models_13571;
    int64_t bytes_16062 = smax64((int64_t) 0, binop_y_16061);
    
    if (memblock_alloc(ctx, &mem_16063, bytes_16062, "mem_16063")) {
        err = 1;
        goto cleanup;
    }
    for (int64_t i_16450 = 0; i_16450 < num_models_13571; i_16450++) {
        ((float *) mem_16063.mem)[i_16450] = 0.0F;
    }
    
    bool cond_15343 = contract_number_13575 == 1;
    int64_t binop_y_16064 = (int64_t) 4 * num_und_13572;
    int64_t bytes_16065 = smax64((int64_t) 0, binop_y_16064);
    
    if (memblock_alloc(ctx, &mem_16066, bytes_16065, "mem_16066")) {
        err = 1;
        goto cleanup;
    }
    for (int64_t i_16451 = 0; i_16451 < num_und_13572; i_16451++) {
        ((float *) mem_16066.mem)[i_16451] = 1.0F;
    }
    
    bool bounds_invalid_upwards_15204 = slt64(num_dates_13573, (int64_t) 1);
    bool valid_15206 = !bounds_invalid_upwards_15204;
    bool range_valid_c_15207;
    
    if (!valid_15206) {
        ctx->error = msgprintf("Error: %s%lld%s%lld%s\n\nBacktrace:\n%s",
                               "Range ", (long long) (int64_t) 1, "..<",
                               (long long) num_dates_13573, " is invalid.",
                               "-> #0  sample_programs/OptionPricing.fut:189:35-47\n   #1  sample_programs/OptionPricing.fut:218:17-66\n   #2  sample_programs/OptionPricing.fut:340:19-72\n   #3  sample_programs/OptionPricing.fut:321:1-346:37\n");
        err = FUTHARK_PROGRAM_ERROR;
        goto cleanup;
    }
    
    int64_t distance_15205 = sub64(num_dates_13573, (int64_t) 1);
    bool y_15194 = slt64((int64_t) 0, num_dates_13573);
    bool index_certs_15195;
    
    if (!y_15194) {
        ctx->error = msgprintf("Error: %s%lld%s%lld%s\n\nBacktrace:\n%s",
                               "Index [", (long long) (int64_t) 0,
                               "] out of bounds for array of shape [",
                               (long long) num_dates_13573, "].",
                               "-> #0  sample_programs/OptionPricing.fut:188:26-30\n   #1  sample_programs/OptionPricing.fut:218:17-66\n   #2  sample_programs/OptionPricing.fut:340:19-72\n   #3  sample_programs/OptionPricing.fut:321:1-346:37\n");
        err = FUTHARK_PROGRAM_ERROR;
        goto cleanup;
    }
    
    int32_t x_15197;
    
    x_15197 = ((int32_t *) bb_inds_mem_15989.mem)[(int64_t) 0];
    
    int32_t i_15198 = sub32(x_15197, 1);
    int64_t i_15199 = sext_i32_i64(i_15198);
    bool y_15201 = slt64(i_15199, num_dates_13573);
    bool x_15200 = sle64((int64_t) 0, i_15199);
    bool bounds_check_15202 = x_15200 && y_15201;
    bool index_certs_15203;
    
    if (!bounds_check_15202) {
        ctx->error = msgprintf("Error: %s%lld%s%lld%s\n\nBacktrace:\n%s",
                               "Index [", (long long) i_15199,
                               "] out of bounds for array of shape [",
                               (long long) num_dates_13573, "].",
                               "-> #0  sample_programs/OptionPricing.fut:188:3-208:9\n   #1  sample_programs/OptionPricing.fut:218:17-66\n   #2  sample_programs/OptionPricing.fut:340:19-72\n   #3  sample_programs/OptionPricing.fut:321:1-346:37\n");
        err = FUTHARK_PROGRAM_ERROR;
        goto cleanup;
    }
    
    float x_15196;
    
    x_15196 = ((float *) bb_data_mem_15990.mem)[(int64_t) 0];
    
    int64_t binop_y_16074 = (int64_t) 4 * sobvctszz_15079;
    int64_t bytes_16075 = smax64((int64_t) 0, binop_y_16074);
    
    if (mem_16076_cached_sizze_16479 < bytes_16075) {
        err = lexical_realloc(&ctx->error, &mem_16076,
                              &mem_16076_cached_sizze_16479, bytes_16075);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (mem_16092_cached_sizze_16480 < bytes_16075) {
        err = lexical_realloc(&ctx->error, &mem_16092,
                              &mem_16092_cached_sizze_16480, bytes_16075);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    
    int64_t binop_y_16103 = (int64_t) 4 * num_dates_13573;
    int64_t bytes_16104 = smax64((int64_t) 0, binop_y_16103);
    
    if (mem_16105_cached_sizze_16481 < bytes_16104) {
        err = lexical_realloc(&ctx->error, &mem_16105,
                              &mem_16105_cached_sizze_16481, bytes_16104);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    
    int64_t binop_x_16158 = num_models_13571 * num_dates_13573;
    int64_t binop_x_16159 = num_und_13572 * binop_x_16158;
    int64_t binop_y_16160 = (int64_t) 4 * binop_x_16159;
    int64_t bytes_16161 = smax64((int64_t) 0, binop_y_16160);
    
    if (mem_16162_cached_sizze_16482 < bytes_16161) {
        err = lexical_realloc(&ctx->error, &mem_16162,
                              &mem_16162_cached_sizze_16482, bytes_16161);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    
    int64_t binop_x_16177 = num_und_13572 * num_dates_13573;
    int64_t binop_y_16178 = (int64_t) 4 * binop_x_16177;
    int64_t bytes_16179 = smax64((int64_t) 0, binop_y_16178);
    
    if (mem_16180_cached_sizze_16483 < bytes_16179) {
        err = lexical_realloc(&ctx->error, &mem_16180,
                              &mem_16180_cached_sizze_16483, bytes_16179);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (mem_16200_cached_sizze_16484 < bytes_16065) {
        err = lexical_realloc(&ctx->error, &mem_16200,
                              &mem_16200_cached_sizze_16484, bytes_16065);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (mem_16339_cached_sizze_16485 < bytes_16062) {
        err = lexical_realloc(&ctx->error, &mem_16339,
                              &mem_16339_cached_sizze_16485, bytes_16062);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    if (memblock_set(ctx, &mem_param_16071, &mem_16063, "mem_16063") != 0)
        return 1;
    for (int32_t i_15873 = 0; i_15873 < num_mc_it_13576; i_15873++) {
        int64_t i_15867 = sext_i32_i64(i_15873);
        
        for (int64_t i_15822 = 0; i_15822 < sobvctszz_15079; i_15822++) {
            float x_15160;
            
            x_15160 = ((float *) mem_15994)[i_15867 * sobvctszz_15079 +
                                            i_15822];
            
            float dp_15161 = x_15160 - 0.5F;
            bool cond_15162 = dp_15161 < 0.0F;
            float x_15163 = 0.0F - dp_15161;
            bool cond_t_res_15164 = x_15163 <= 0.425F;
            bool x_15165 = cond_15162 && cond_t_res_15164;
            bool cond_15166 = 0.0F <= dp_15161;
            bool cond_f_res_t_res_15167 = dp_15161 <= 0.425F;
            bool x_15168 = cond_15166 && cond_f_res_t_res_15167;
            bool x_15169 = !x_15165;
            bool y_15170 = x_15168 && x_15169;
            bool cond_15171 = x_15165 || y_15170;
            float defunc_0_f_res_15172;
            
            if (cond_15171) {
                float y_15173 = dp_15161 * dp_15161;
                float polyAppr_arg_15174 = 0.180625F - y_15173;
                float x_15472 = 2509.0808F * polyAppr_arg_15174;
                float y_15473 = 33430.574F + x_15472;
                float x_15474 = polyAppr_arg_15174 * y_15473;
                float y_15475 = 67265.77F + x_15474;
                float x_15476 = polyAppr_arg_15174 * y_15475;
                float y_15477 = 45921.953F + x_15476;
                float x_15478 = polyAppr_arg_15174 * y_15477;
                float y_15479 = 13731.693F + x_15478;
                float x_15480 = polyAppr_arg_15174 * y_15479;
                float y_15481 = 1971.591F + x_15480;
                float x_15482 = polyAppr_arg_15174 * y_15481;
                float y_15483 = 133.14166F + x_15482;
                float x_15484 = polyAppr_arg_15174 * y_15483;
                float x_15485 = 3.387133F + x_15484;
                float x_15486 = 5226.495F * polyAppr_arg_15174;
                float y_15487 = 28729.086F + x_15486;
                float x_15488 = polyAppr_arg_15174 * y_15487;
                float y_15489 = 39307.895F + x_15488;
                float x_15490 = polyAppr_arg_15174 * y_15489;
                float y_15491 = 21213.795F + x_15490;
                float x_15492 = polyAppr_arg_15174 * y_15491;
                float y_15493 = 5394.196F + x_15492;
                float x_15494 = polyAppr_arg_15174 * y_15493;
                float y_15495 = 687.187F + x_15494;
                float x_15496 = polyAppr_arg_15174 * y_15495;
                float y_15497 = 42.31333F + x_15496;
                float x_15498 = polyAppr_arg_15174 * y_15497;
                float y_15499 = 1.0F + x_15498;
                float polyAppr_res_15500 = x_15485 / y_15499;
                float smallcase_res_15176 = dp_15161 * polyAppr_res_15500;
                
                defunc_0_f_res_15172 = smallcase_res_15176;
            } else {
                float pp_15177;
                
                if (cond_15162) {
                    float pp_t_res_15178 = 0.5F + dp_15161;
                    
                    pp_15177 = pp_t_res_15178;
                } else {
                    float pp_f_res_15179 = 0.5F - dp_15161;
                    
                    pp_15177 = pp_f_res_15179;
                }
                
                float log_res_15180;
                
                log_res_15180 = futrts_log32(pp_15177);
                
                float sqrt_arg_15181 = 0.0F - log_res_15180;
                float sqrt_res_15182;
                
                sqrt_res_15182 = futrts_sqrt32(sqrt_arg_15181);
                
                bool cond_15183 = sqrt_res_15182 <= 5.0F;
                float x_15184;
                
                if (cond_15183) {
                    float polyAppr_arg_15185 = sqrt_res_15182 - 1.6F;
                    float x_15518 = 7.74545e-4F * polyAppr_arg_15185;
                    float y_15519 = 2.2723844e-2F + x_15518;
                    float x_15520 = polyAppr_arg_15185 * y_15519;
                    float y_15521 = 0.24178073F + x_15520;
                    float x_15522 = polyAppr_arg_15185 * y_15521;
                    float y_15523 = 1.2704582F + x_15522;
                    float x_15524 = polyAppr_arg_15185 * y_15523;
                    float y_15525 = 3.6478484F + x_15524;
                    float x_15526 = polyAppr_arg_15185 * y_15525;
                    float y_15527 = 5.7694974F + x_15526;
                    float x_15528 = polyAppr_arg_15185 * y_15527;
                    float y_15529 = 4.6303377F + x_15528;
                    float x_15530 = polyAppr_arg_15185 * y_15529;
                    float x_15531 = 1.4234371F + x_15530;
                    float x_15532 = 1.05075e-9F * polyAppr_arg_15185;
                    float y_15533 = 5.475938e-4F + x_15532;
                    float x_15534 = polyAppr_arg_15185 * y_15533;
                    float y_15535 = 1.5198667e-2F + x_15534;
                    float x_15536 = polyAppr_arg_15185 * y_15535;
                    float y_15537 = 0.14810398F + x_15536;
                    float x_15538 = polyAppr_arg_15185 * y_15537;
                    float y_15539 = 0.68976736F + x_15538;
                    float x_15540 = polyAppr_arg_15185 * y_15539;
                    float y_15541 = 1.6763848F + x_15540;
                    float x_15542 = polyAppr_arg_15185 * y_15541;
                    float y_15543 = 2.0531917F + x_15542;
                    float x_15544 = polyAppr_arg_15185 * y_15543;
                    float y_15545 = 1.0F + x_15544;
                    float polyAppr_res_15546 = x_15531 / y_15545;
                    
                    x_15184 = polyAppr_res_15546;
                } else {
                    float polyAppr_arg_15187 = sqrt_res_15182 - 5.0F;
                    float x_15564 = 2.0103344e-7F * polyAppr_arg_15187;
                    float y_15565 = 2.7115555e-5F + x_15564;
                    float x_15566 = polyAppr_arg_15187 * y_15565;
                    float y_15567 = 1.2426609e-3F + x_15566;
                    float x_15568 = polyAppr_arg_15187 * y_15567;
                    float y_15569 = 2.653219e-2F + x_15568;
                    float x_15570 = polyAppr_arg_15187 * y_15569;
                    float y_15571 = 0.2965606F + x_15570;
                    float x_15572 = polyAppr_arg_15187 * y_15571;
                    float y_15573 = 1.7848265F + x_15572;
                    float x_15574 = polyAppr_arg_15187 * y_15573;
                    float y_15575 = 5.4637847F + x_15574;
                    float x_15576 = polyAppr_arg_15187 * y_15575;
                    float x_15577 = 6.6579046F + x_15576;
                    float x_15578 = 2.044263e-5F * polyAppr_arg_15187;
                    float y_15579 = 1.4215118e-7F + x_15578;
                    float x_15580 = polyAppr_arg_15187 * y_15579;
                    float y_15581 = 1.8463183e-5F + x_15580;
                    float x_15582 = polyAppr_arg_15187 * y_15581;
                    float y_15583 = 7.8686915e-4F + x_15582;
                    float x_15584 = polyAppr_arg_15187 * y_15583;
                    float y_15585 = 1.4875362e-2F + x_15584;
                    float x_15586 = polyAppr_arg_15187 * y_15585;
                    float y_15587 = 0.13692988F + x_15586;
                    float x_15588 = polyAppr_arg_15187 * y_15587;
                    float y_15589 = 0.5998322F + x_15588;
                    float x_15590 = polyAppr_arg_15187 * y_15589;
                    float y_15591 = 1.0F + x_15590;
                    float polyAppr_res_15592 = x_15577 / y_15591;
                    
                    x_15184 = polyAppr_res_15592;
                }
                
                float defunc_0_f_res_f_res_15189;
                
                if (cond_15162) {
                    float defunc_0_f_res_f_res_t_res_15190 = 0.0F - x_15184;
                    
                    defunc_0_f_res_f_res_15189 =
                        defunc_0_f_res_f_res_t_res_15190;
                } else {
                    defunc_0_f_res_f_res_15189 = x_15184;
                }
                defunc_0_f_res_15172 = defunc_0_f_res_f_res_15189;
            }
            ((float *) mem_16076)[i_15822] = defunc_0_f_res_15172;
        }
        for (int64_t i_15826 = 0; i_15826 < num_und_13572; i_15826++) {
            for (int64_t i_16456 = 0; i_16456 < num_dates_13573; i_16456++) {
                ((float *) mem_16105)[i_16456] = 0.0F;
            }
            
            float y_15215;
            
            y_15215 = ((float *) mem_16076)[i_15826];
            
            float lw_val_15216 = x_15196 * y_15215;
            
            ((float *) mem_16105)[i_15199] = lw_val_15216;
            if (num_dates_13573 * (int64_t) 4 > 0)
                memmove(mem_16092 + i_15826 * num_dates_13573 * (int64_t) 4,
                        mem_16105 + (int64_t) 0, num_dates_13573 * (int64_t) 4);
            for (int64_t i_15219 = 0; i_15219 < distance_15205; i_15219++) {
                int64_t index_primexp_15221 = add64((int64_t) 1, i_15219);
                int32_t x_15222;
                
                x_15222 = ((int32_t *) bb_inds_mem_15989.mem)[num_dates_13573 +
                                                              index_primexp_15221];
                
                int32_t j_15223 = sub32(x_15222, 1);
                int32_t x_15224;
                
                x_15224 = ((int32_t *) bb_inds_mem_15989.mem)[(int64_t) 2 *
                                                              num_dates_13573 +
                                                              index_primexp_15221];
                
                int32_t k_15225 = sub32(x_15224, 1);
                int32_t x_15226;
                
                x_15226 =
                    ((int32_t *) bb_inds_mem_15989.mem)[index_primexp_15221];
                
                int32_t l_15227 = sub32(x_15226, 1);
                int64_t k_15228 = sext_i32_i64(k_15225);
                float wk_15229;
                
                wk_15229 = ((float *) mem_16092)[i_15826 * num_dates_13573 +
                                                 k_15228];
                
                int64_t binop_x_15938 = num_und_13572 * index_primexp_15221;
                int64_t new_index_15939 = i_15826 + binop_x_15938;
                float zzi_15230;
                
                zzi_15230 = ((float *) mem_16076)[new_index_15939];
                
                float x_15231;
                
                x_15231 = ((float *) bb_data_mem_15990.mem)[(int64_t) 2 *
                                                            num_dates_13573 +
                                                            index_primexp_15221];
                
                float x_15232 = wk_15229 * x_15231;
                float x_15233;
                
                x_15233 =
                    ((float *) bb_data_mem_15990.mem)[index_primexp_15221];
                
                float y_15234 = zzi_15230 * x_15233;
                float tmp_15235 = x_15232 + y_15234;
                bool cond_15236 = j_15223 == -1;
                float lw_val_15237;
                
                if (cond_15236) {
                    lw_val_15237 = tmp_15235;
                } else {
                    float x_15238;
                    
                    x_15238 =
                        ((float *) bb_data_mem_15990.mem)[num_dates_13573 +
                                                          index_primexp_15221];
                    
                    int64_t j_15239 = sext_i32_i64(j_15223);
                    float y_15240;
                    
                    y_15240 = ((float *) mem_16092)[i_15826 * num_dates_13573 +
                                                    j_15239];
                    
                    float y_15241 = x_15238 * y_15240;
                    float lw_val_f_res_15242 = tmp_15235 + y_15241;
                    
                    lw_val_15237 = lw_val_f_res_15242;
                }
                
                int64_t l_15243 = sext_i32_i64(l_15227);
                
                ((float *) mem_16092)[i_15826 * num_dates_13573 + l_15243] =
                    lw_val_15237;
            }
            for (int64_t i_15246 = 0; i_15246 < distance_15205; i_15246++) {
                int64_t index_primexp_15248 = add64((int64_t) 1, i_15246);
                int64_t i_15249 = sub64(num_dates_13573, index_primexp_15248);
                float x_15250;
                
                x_15250 = ((float *) mem_16092)[i_15826 * num_dates_13573 +
                                                i_15249];
                
                int64_t i_15251 = sub64(i_15249, (int64_t) 1);
                float y_15252;
                
                y_15252 = ((float *) mem_16092)[i_15826 * num_dates_13573 +
                                                i_15251];
                
                float lw_val_15253 = x_15250 - y_15252;
                
                ((float *) mem_16092)[i_15826 * num_dates_13573 + i_15249] =
                    lw_val_15253;
            }
        }
        for (int64_t i_15854 = 0; i_15854 < num_models_13571; i_15854++) {
            if (memblock_set(ctx, &mem_param_16185, &mem_16066, "mem_16066") !=
                0)
                return 1;
            for (int64_t i_15841 = 0; i_15841 < num_dates_13573; i_15841++) {
                for (int64_t i_15836 = 0; i_15836 < num_und_13572; i_15836++) {
                    float x_15315;
                    
                    x_15315 = ((float *) md_vols_mem_15984.mem)[i_15854 *
                                                                (num_und_13572 *
                                                                 num_dates_13573) +
                                                                i_15841 *
                                                                num_und_13572 +
                                                                i_15836];
                    
                    float x_15318;
                    
                    x_15318 = ((float *) md_drifts_mem_15985.mem)[i_15854 *
                                                                  (num_und_13572 *
                                                                   num_dates_13573) +
                                                                  i_15841 *
                                                                  num_und_13572 +
                                                                  i_15836];
                    
                    int64_t take_arg_15297 = add64((int64_t) 1, i_15836);
                    float defunc_2_reduce_res_15304;
                    float redout_15832 = 0.0F;
                    
                    for (int64_t i_15833 = 0; i_15833 < take_arg_15297;
                         i_15833++) {
                        float x_15301;
                        
                        x_15301 = ((float *) mem_16092)[i_15833 *
                                                        num_dates_13573 +
                                                        i_15841];
                        
                        float x_15302;
                        
                        x_15302 = ((float *) md_cs_mem_15983.mem)[i_15854 *
                                                                  (num_und_13572 *
                                                                   num_und_13572) +
                                                                  i_15836 *
                                                                  num_und_13572 +
                                                                  i_15833];
                        
                        float defunc_1_f_res_15303 = x_15301 * x_15302;
                        float defunc_1_op_res_15307 = defunc_1_f_res_15303 +
                              redout_15832;
                        float redout_tmp_16464 = defunc_1_op_res_15307;
                        
                        redout_15832 = redout_tmp_16464;
                    }
                    defunc_2_reduce_res_15304 = redout_15832;
                    
                    float defunc_1_f_res_15316 = defunc_2_reduce_res_15304 *
                          x_15315;
                    float defunc_1_f_res_15320 = defunc_1_f_res_15316 + x_15318;
                    float defunc_0_f_res_15325;
                    
                    defunc_0_f_res_15325 = futrts_exp32(defunc_1_f_res_15320);
                    ((float *) mem_16200)[i_15836] = defunc_0_f_res_15325;
                }
                for (int64_t i_15830 = 0; i_15830 < num_und_13572; i_15830++) {
                    float x_15330;
                    
                    x_15330 = ((float *) mem_param_16185.mem)[i_15830];
                    
                    float x_15331;
                    
                    x_15331 = ((float *) mem_16200)[i_15830];
                    
                    float defunc_1_f_res_15332 = x_15330 * x_15331;
                    
                    ((float *) mem_16180)[i_15841 * num_und_13572 + i_15830] =
                        defunc_1_f_res_15332;
                }
                if (memblock_alloc(ctx, &mem_16237, bytes_16065, "mem_16237")) {
                    err = 1;
                    goto cleanup;
                }
                if (num_und_13572 * (int64_t) 4 > 0)
                    memmove(mem_16237.mem + (int64_t) 0, mem_16180 +
                            ((int64_t) 0 + i_15841 * num_und_13572) *
                            (int64_t) 4, num_und_13572 * (int64_t) 4);
                if (memblock_set(ctx, &mem_param_tmp_16460, &mem_16237,
                                 "mem_16237") != 0)
                    return 1;
                if (memblock_set(ctx, &mem_param_16185, &mem_param_tmp_16460,
                                 "mem_param_tmp_16460") != 0)
                    return 1;
            }
            if (memblock_set(ctx, &ext_mem_16241, &mem_param_16185,
                             "mem_param_16185") != 0)
                return 1;
            for (int64_t i_15850 = 0; i_15850 < num_dates_13573; i_15850++) {
                for (int64_t i_15846 = 0; i_15846 < num_und_13572; i_15846++) {
                    float x_15337;
                    
                    x_15337 = ((float *) md_sts_mem_15986.mem)[i_15854 *
                                                               num_und_13572 +
                                                               i_15846];
                    
                    float x_15338;
                    
                    x_15338 = ((float *) mem_16180)[i_15850 * num_und_13572 +
                                                    i_15846];
                    
                    float defunc_1_f_res_15339 = x_15337 * x_15338;
                    
                    ((float *) mem_16162)[i_15854 * sobvctszz_15079 + i_15850 *
                                          num_und_13572 + i_15846] =
                        defunc_1_f_res_15339;
                }
            }
        }
        for (int64_t i_15864 = 0; i_15864 < num_models_13571; i_15864++) {
            float defunc_2_f_res_15360;
            
            if (cond_15343) {
                float detval_15361;
                
                detval_15361 = ((float *) md_detvals_mem_15987.mem)[i_15864];
                
                float x_15362;
                
                x_15362 = ((float *) mem_16162)[i_15864 * sobvctszz_15079];
                
                float x_15363 = x_15362 - 4000.0F;
                float amount_15364 = detval_15361 * x_15363;
                bool cond_15365 = 0.0F < amount_15364;
                float amount0_15366;
                
                if (cond_15365) {
                    amount0_15366 = amount_15364;
                } else {
                    amount0_15366 = 0.0F;
                }
                
                float y_15635;
                
                y_15635 = ((float *) md_discts_mem_15988.mem)[i_15864 *
                                                              num_discts_13574];
                
                float trajInner_res_15636 = amount0_15366 * y_15635;
                
                defunc_2_f_res_15360 = trajInner_res_15636;
            } else {
                bool cond_15368 = contract_number_13575 == 2;
                float defunc_2_f_res_f_res_15369;
                
                if (cond_15368) {
                    float x_15641;
                    
                    x_15641 = ((float *) mem_16162)[i_15864 * sobvctszz_15079];
                    
                    float fminPayoff_res_15642 = x_15641 / 3758.05F;
                    float x_15645;
                    
                    x_15645 = ((float *) mem_16162)[i_15864 * sobvctszz_15079 +
                                                    (int64_t) 1];
                    
                    float fminPayoff_res_15646 = x_15645 / 11840.0F;
                    float x_15649;
                    
                    x_15649 = ((float *) mem_16162)[i_15864 * sobvctszz_15079 +
                                                    (int64_t) 2];
                    
                    float fminPayoff_res_15650 = x_15649 / 1200.0F;
                    bool cond_15651 = fminPayoff_res_15642 <
                         fminPayoff_res_15646;
                    float fminPayoff_res_15652;
                    
                    if (cond_15651) {
                        bool cond_15653 = fminPayoff_res_15642 <
                             fminPayoff_res_15650;
                        float fminPayoff_res_t_res_15654;
                        
                        if (cond_15653) {
                            fminPayoff_res_t_res_15654 = fminPayoff_res_15642;
                        } else {
                            fminPayoff_res_t_res_15654 = fminPayoff_res_15650;
                        }
                        fminPayoff_res_15652 = fminPayoff_res_t_res_15654;
                    } else {
                        bool cond_15655 = fminPayoff_res_15646 <
                             fminPayoff_res_15650;
                        float fminPayoff_res_f_res_15656;
                        
                        if (cond_15655) {
                            fminPayoff_res_f_res_15656 = fminPayoff_res_15646;
                        } else {
                            fminPayoff_res_f_res_15656 = fminPayoff_res_15650;
                        }
                        fminPayoff_res_15652 = fminPayoff_res_f_res_15656;
                    }
                    
                    bool cond_15371 = 1.0F <= fminPayoff_res_15652;
                    int32_t payoff2_res_15372;
                    float payoff2_res_15373;
                    
                    if (cond_15371) {
                        payoff2_res_15372 = 0;
                        payoff2_res_15373 = 1150.0F;
                    } else {
                        float x_15661;
                        
                        x_15661 = ((float *) mem_16162)[i_15864 *
                                                        sobvctszz_15079 +
                                                        num_und_13572];
                        
                        float fminPayoff_res_15662 = x_15661 / 3758.05F;
                        float x_15665;
                        
                        x_15665 = ((float *) mem_16162)[i_15864 *
                                                        sobvctszz_15079 +
                                                        num_und_13572 +
                                                        (int64_t) 1];
                        
                        float fminPayoff_res_15666 = x_15665 / 11840.0F;
                        float x_15669;
                        
                        x_15669 = ((float *) mem_16162)[i_15864 *
                                                        sobvctszz_15079 +
                                                        num_und_13572 +
                                                        (int64_t) 2];
                        
                        float fminPayoff_res_15670 = x_15669 / 1200.0F;
                        bool cond_15671 = fminPayoff_res_15662 <
                             fminPayoff_res_15666;
                        float fminPayoff_res_15672;
                        
                        if (cond_15671) {
                            bool cond_15673 = fminPayoff_res_15662 <
                                 fminPayoff_res_15670;
                            float fminPayoff_res_t_res_15674;
                            
                            if (cond_15673) {
                                fminPayoff_res_t_res_15674 =
                                    fminPayoff_res_15662;
                            } else {
                                fminPayoff_res_t_res_15674 =
                                    fminPayoff_res_15670;
                            }
                            fminPayoff_res_15672 = fminPayoff_res_t_res_15674;
                        } else {
                            bool cond_15675 = fminPayoff_res_15666 <
                                 fminPayoff_res_15670;
                            float fminPayoff_res_f_res_15676;
                            
                            if (cond_15675) {
                                fminPayoff_res_f_res_15676 =
                                    fminPayoff_res_15666;
                            } else {
                                fminPayoff_res_f_res_15676 =
                                    fminPayoff_res_15670;
                            }
                            fminPayoff_res_15672 = fminPayoff_res_f_res_15676;
                        }
                        
                        bool cond_15375 = 1.0F <= fminPayoff_res_15672;
                        int32_t payoff2_res_f_res_15376;
                        float payoff2_res_f_res_15377;
                        
                        if (cond_15375) {
                            payoff2_res_f_res_15376 = 1;
                            payoff2_res_f_res_15377 = 1300.0F;
                        } else {
                            float x_15681;
                            
                            x_15681 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 2 *
                                                            num_und_13572];
                            
                            float fminPayoff_res_15682 = x_15681 / 3758.05F;
                            float x_15685;
                            
                            x_15685 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 2 *
                                                            num_und_13572 +
                                                            (int64_t) 1];
                            
                            float fminPayoff_res_15686 = x_15685 / 11840.0F;
                            float x_15689;
                            
                            x_15689 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 2 *
                                                            num_und_13572 +
                                                            (int64_t) 2];
                            
                            float fminPayoff_res_15690 = x_15689 / 1200.0F;
                            bool cond_15691 = fminPayoff_res_15682 <
                                 fminPayoff_res_15686;
                            float fminPayoff_res_15692;
                            
                            if (cond_15691) {
                                bool cond_15693 = fminPayoff_res_15682 <
                                     fminPayoff_res_15690;
                                float fminPayoff_res_t_res_15694;
                                
                                if (cond_15693) {
                                    fminPayoff_res_t_res_15694 =
                                        fminPayoff_res_15682;
                                } else {
                                    fminPayoff_res_t_res_15694 =
                                        fminPayoff_res_15690;
                                }
                                fminPayoff_res_15692 =
                                    fminPayoff_res_t_res_15694;
                            } else {
                                bool cond_15695 = fminPayoff_res_15686 <
                                     fminPayoff_res_15690;
                                float fminPayoff_res_f_res_15696;
                                
                                if (cond_15695) {
                                    fminPayoff_res_f_res_15696 =
                                        fminPayoff_res_15686;
                                } else {
                                    fminPayoff_res_f_res_15696 =
                                        fminPayoff_res_15690;
                                }
                                fminPayoff_res_15692 =
                                    fminPayoff_res_f_res_15696;
                            }
                            
                            bool cond_15379 = 1.0F <= fminPayoff_res_15692;
                            int32_t payoff2_res_f_res_f_res_15380;
                            float payoff2_res_f_res_f_res_15381;
                            
                            if (cond_15379) {
                                payoff2_res_f_res_f_res_15380 = 2;
                                payoff2_res_f_res_f_res_15381 = 1450.0F;
                            } else {
                                float x_15701;
                                
                                x_15701 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                (int64_t) 3 *
                                                                num_und_13572];
                                
                                float fminPayoff_res_15702 = x_15701 / 3758.05F;
                                float x_15705;
                                
                                x_15705 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                (int64_t) 3 *
                                                                num_und_13572 +
                                                                (int64_t) 1];
                                
                                float fminPayoff_res_15706 = x_15705 / 11840.0F;
                                float x_15709;
                                
                                x_15709 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                (int64_t) 3 *
                                                                num_und_13572 +
                                                                (int64_t) 2];
                                
                                float fminPayoff_res_15710 = x_15709 / 1200.0F;
                                bool cond_15711 = fminPayoff_res_15702 <
                                     fminPayoff_res_15706;
                                float fminPayoff_res_15712;
                                
                                if (cond_15711) {
                                    bool cond_15713 = fminPayoff_res_15702 <
                                         fminPayoff_res_15710;
                                    float fminPayoff_res_t_res_15714;
                                    
                                    if (cond_15713) {
                                        fminPayoff_res_t_res_15714 =
                                            fminPayoff_res_15702;
                                    } else {
                                        fminPayoff_res_t_res_15714 =
                                            fminPayoff_res_15710;
                                    }
                                    fminPayoff_res_15712 =
                                        fminPayoff_res_t_res_15714;
                                } else {
                                    bool cond_15715 = fminPayoff_res_15706 <
                                         fminPayoff_res_15710;
                                    float fminPayoff_res_f_res_15716;
                                    
                                    if (cond_15715) {
                                        fminPayoff_res_f_res_15716 =
                                            fminPayoff_res_15706;
                                    } else {
                                        fminPayoff_res_f_res_15716 =
                                            fminPayoff_res_15710;
                                    }
                                    fminPayoff_res_15712 =
                                        fminPayoff_res_f_res_15716;
                                }
                                
                                bool cond_15383 = 1.0F <= fminPayoff_res_15712;
                                int32_t payoff2_res_f_res_f_res_f_res_15384;
                                
                                if (cond_15383) {
                                    payoff2_res_f_res_f_res_f_res_15384 = 3;
                                } else {
                                    payoff2_res_f_res_f_res_f_res_15384 = 4;
                                }
                                
                                float payoff2_res_f_res_f_res_f_res_15385;
                                
                                if (cond_15383) {
                                    payoff2_res_f_res_f_res_f_res_15385 =
                                        1600.0F;
                                } else {
                                    float x_15721;
                                    
                                    x_15721 = ((float *) mem_16162)[i_15864 *
                                                                    sobvctszz_15079 +
                                                                    (int64_t) 4 *
                                                                    num_und_13572];
                                    
                                    float fminPayoff_res_15722 = x_15721 /
                                          3758.05F;
                                    float x_15725;
                                    
                                    x_15725 = ((float *) mem_16162)[i_15864 *
                                                                    sobvctszz_15079 +
                                                                    (int64_t) 4 *
                                                                    num_und_13572 +
                                                                    (int64_t) 1];
                                    
                                    float fminPayoff_res_15726 = x_15725 /
                                          11840.0F;
                                    float x_15729;
                                    
                                    x_15729 = ((float *) mem_16162)[i_15864 *
                                                                    sobvctszz_15079 +
                                                                    (int64_t) 4 *
                                                                    num_und_13572 +
                                                                    (int64_t) 2];
                                    
                                    float fminPayoff_res_15730 = x_15729 /
                                          1200.0F;
                                    bool cond_15731 = fminPayoff_res_15722 <
                                         fminPayoff_res_15726;
                                    float fminPayoff_res_15732;
                                    
                                    if (cond_15731) {
                                        bool cond_15733 = fminPayoff_res_15722 <
                                             fminPayoff_res_15730;
                                        float fminPayoff_res_t_res_15734;
                                        
                                        if (cond_15733) {
                                            fminPayoff_res_t_res_15734 =
                                                fminPayoff_res_15722;
                                        } else {
                                            fminPayoff_res_t_res_15734 =
                                                fminPayoff_res_15730;
                                        }
                                        fminPayoff_res_15732 =
                                            fminPayoff_res_t_res_15734;
                                    } else {
                                        bool cond_15735 = fminPayoff_res_15726 <
                                             fminPayoff_res_15730;
                                        float fminPayoff_res_f_res_15736;
                                        
                                        if (cond_15735) {
                                            fminPayoff_res_f_res_15736 =
                                                fminPayoff_res_15726;
                                        } else {
                                            fminPayoff_res_f_res_15736 =
                                                fminPayoff_res_15730;
                                        }
                                        fminPayoff_res_15732 =
                                            fminPayoff_res_f_res_15736;
                                    }
                                    
                                    bool cond_15387 = 1.0F <=
                                         fminPayoff_res_15732;
                                    float value_15388;
                                    
                                    if (cond_15387) {
                                        value_15388 = 1750.0F;
                                    } else {
                                        bool cond_15389 = 0.75F <
                                             fminPayoff_res_15732;
                                        float value_f_res_15390;
                                        
                                        if (cond_15389) {
                                            value_f_res_15390 = 1000.0F;
                                        } else {
                                            float value_f_res_f_res_15391 =
                                                  1000.0F *
                                                  fminPayoff_res_15732;
                                            
                                            value_f_res_15390 =
                                                value_f_res_f_res_15391;
                                        }
                                        value_15388 = value_f_res_15390;
                                    }
                                    payoff2_res_f_res_f_res_f_res_15385 =
                                        value_15388;
                                }
                                payoff2_res_f_res_f_res_15380 =
                                    payoff2_res_f_res_f_res_f_res_15384;
                                payoff2_res_f_res_f_res_15381 =
                                    payoff2_res_f_res_f_res_f_res_15385;
                            }
                            payoff2_res_f_res_15376 =
                                payoff2_res_f_res_f_res_15380;
                            payoff2_res_f_res_15377 =
                                payoff2_res_f_res_f_res_15381;
                        }
                        payoff2_res_15372 = payoff2_res_f_res_15376;
                        payoff2_res_15373 = payoff2_res_f_res_15377;
                    }
                    
                    int64_t ind_15741 = sext_i32_i64(payoff2_res_15372);
                    float y_15742;
                    
                    y_15742 = ((float *) md_discts_mem_15988.mem)[i_15864 *
                                                                  num_discts_13574 +
                                                                  ind_15741];
                    
                    float trajInner_res_15743 = payoff2_res_15373 * y_15742;
                    
                    defunc_2_f_res_f_res_15369 = trajInner_res_15743;
                } else {
                    bool cond_15393 = contract_number_13575 == 3;
                    float defunc_2_f_res_f_res_f_res_15394;
                    
                    if (cond_15393) {
                        if (mem_16348_cached_sizze_16486 < (int64_t) 367) {
                            err = lexical_realloc(&ctx->error, &mem_16348,
                                                  &mem_16348_cached_sizze_16486,
                                                  (int64_t) 367);
                            if (err != FUTHARK_SUCCESS)
                                goto cleanup;
                        }
                        for (int32_t i_15874 = 0; i_15874 < 367; i_15874++) {
                            int64_t i_15858 = sext_i32_i64(i_15874);
                            float x_15398;
                            
                            x_15398 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            i_15858 *
                                                            num_und_13572];
                            
                            bool cond_15399 = x_15398 <= 2630.635F;
                            bool cond_15400;
                            
                            if (cond_15399) {
                                cond_15400 = 1;
                            } else {
                                float x_15401;
                                
                                x_15401 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                i_15858 *
                                                                num_und_13572 +
                                                                (int64_t) 1];
                                
                                bool cond_f_res_15402 = x_15401 <= 8288.0F;
                                
                                cond_15400 = cond_f_res_15402;
                            }
                            
                            bool defunc_0_f_res_15403;
                            
                            if (cond_15400) {
                                defunc_0_f_res_15403 = 1;
                            } else {
                                float x_15404;
                                
                                x_15404 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                i_15858 *
                                                                num_und_13572 +
                                                                (int64_t) 2];
                                
                                bool defunc_0_f_res_f_res_15405 = x_15404 <=
                                     840.0F;
                                
                                defunc_0_f_res_15403 =
                                    defunc_0_f_res_f_res_15405;
                            }
                            ((bool *) mem_16348)[i_15858] =
                                defunc_0_f_res_15403;
                        }
                        
                        bool defunc_2_reduce_res_15406;
                        bool redout_15860 = 0;
                        
                        for (int32_t i_15875 = 0; i_15875 < 367; i_15875++) {
                            int64_t i_15861 = sext_i32_i64(i_15875);
                            bool x_15410;
                            
                            x_15410 = ((bool *) mem_16348)[i_15861];
                            
                            bool defunc_1_op_res_15409 = x_15410 ||
                                 redout_15860;
                            bool redout_tmp_16470 = defunc_1_op_res_15409;
                            
                            redout_15860 = redout_tmp_16470;
                        }
                        defunc_2_reduce_res_15406 = redout_15860;
                        
                        float y_15749;
                        
                        y_15749 = ((float *) md_discts_mem_15988.mem)[i_15864 *
                                                                      num_discts_13574];
                        
                        float trajInner_res_15750 = 100.0F * y_15749;
                        bool goto40_15412;
                        
                        if (defunc_2_reduce_res_15406) {
                            float x_15413;
                            
                            x_15413 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 366 *
                                                            num_und_13572];
                            
                            bool cond_15414 = x_15413 < 3758.05F;
                            bool cond_15415;
                            
                            if (cond_15414) {
                                cond_15415 = 1;
                            } else {
                                float x_15416;
                                
                                x_15416 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                (int64_t) 366 *
                                                                num_und_13572 +
                                                                (int64_t) 1];
                                
                                bool cond_f_res_15417 = x_15416 < 11840.0F;
                                
                                cond_15415 = cond_f_res_15417;
                            }
                            
                            bool goto40_t_res_15418;
                            
                            if (cond_15415) {
                                goto40_t_res_15418 = 1;
                            } else {
                                float x_15419;
                                
                                x_15419 = ((float *) mem_16162)[i_15864 *
                                                                sobvctszz_15079 +
                                                                (int64_t) 366 *
                                                                num_und_13572 +
                                                                (int64_t) 2];
                                
                                bool goto40_t_res_f_res_15420 = x_15419 <
                                     1200.0F;
                                
                                goto40_t_res_15418 = goto40_t_res_f_res_15420;
                            }
                            goto40_15412 = goto40_t_res_15418;
                        } else {
                            goto40_15412 = 0;
                        }
                        
                        float amount_15421;
                        
                        if (goto40_15412) {
                            float x_15755;
                            
                            x_15755 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 366 *
                                                            num_und_13572];
                            
                            float fminPayoff_res_15756 = x_15755 / 3758.05F;
                            float x_15759;
                            
                            x_15759 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 366 *
                                                            num_und_13572 +
                                                            (int64_t) 1];
                            
                            float fminPayoff_res_15760 = x_15759 / 11840.0F;
                            float x_15763;
                            
                            x_15763 = ((float *) mem_16162)[i_15864 *
                                                            sobvctszz_15079 +
                                                            (int64_t) 366 *
                                                            num_und_13572 +
                                                            (int64_t) 2];
                            
                            float fminPayoff_res_15764 = x_15763 / 1200.0F;
                            bool cond_15765 = fminPayoff_res_15756 <
                                 fminPayoff_res_15760;
                            float fminPayoff_res_15766;
                            
                            if (cond_15765) {
                                bool cond_15767 = fminPayoff_res_15756 <
                                     fminPayoff_res_15764;
                                float fminPayoff_res_t_res_15768;
                                
                                if (cond_15767) {
                                    fminPayoff_res_t_res_15768 =
                                        fminPayoff_res_15756;
                                } else {
                                    fminPayoff_res_t_res_15768 =
                                        fminPayoff_res_15764;
                                }
                                fminPayoff_res_15766 =
                                    fminPayoff_res_t_res_15768;
                            } else {
                                bool cond_15769 = fminPayoff_res_15760 <
                                     fminPayoff_res_15764;
                                float fminPayoff_res_f_res_15770;
                                
                                if (cond_15769) {
                                    fminPayoff_res_f_res_15770 =
                                        fminPayoff_res_15760;
                                } else {
                                    fminPayoff_res_f_res_15770 =
                                        fminPayoff_res_15764;
                                }
                                fminPayoff_res_15766 =
                                    fminPayoff_res_f_res_15770;
                            }
                            
                            float amount_t_res_15423 = 1000.0F *
                                  fminPayoff_res_15766;
                            
                            amount_15421 = amount_t_res_15423;
                        } else {
                            amount_15421 = 1000.0F;
                        }
                        
                        float y_15776;
                        
                        y_15776 = ((float *) md_discts_mem_15988.mem)[i_15864 *
                                                                      num_discts_13574 +
                                                                      (int64_t) 1];
                        
                        float trajInner_res_15777 = amount_15421 * y_15776;
                        float payoff3_res_15425 = trajInner_res_15750 +
                              trajInner_res_15777;
                        
                        defunc_2_f_res_f_res_f_res_15394 = payoff3_res_15425;
                    } else {
                        defunc_2_f_res_f_res_f_res_15394 = 0.0F;
                    }
                    defunc_2_f_res_f_res_15369 =
                        defunc_2_f_res_f_res_f_res_15394;
                }
                defunc_2_f_res_15360 = defunc_2_f_res_f_res_15369;
            }
            ((float *) mem_16339)[i_15864] = defunc_2_f_res_15360;
        }
        if (memblock_alloc(ctx, &mem_16370, bytes_16062, "mem_16370")) {
            err = 1;
            goto cleanup;
        }
        for (int64_t i_15818 = 0; i_15818 < num_models_13571; i_15818++) {
            float x_15432;
            
            x_15432 = ((float *) mem_param_16071.mem)[i_15818];
            
            float x_15433;
            
            x_15433 = ((float *) mem_16339)[i_15818];
            
            float defunc_1_f_res_15434 = x_15432 + x_15433;
            
            ((float *) mem_16370.mem)[i_15818] = defunc_1_f_res_15434;
        }
        if (memblock_set(ctx, &mem_param_tmp_16452, &mem_16370, "mem_16370") !=
            0)
            return 1;
        if (memblock_set(ctx, &mem_param_16071, &mem_param_tmp_16452,
                         "mem_param_tmp_16452") != 0)
            return 1;
    }
    if (memblock_set(ctx, &ext_mem_16383, &mem_param_16071,
                     "mem_param_16071") != 0)
        return 1;
    if (memblock_unref(ctx, &mem_16063, "mem_16063") != 0)
        return 1;
    if (memblock_unref(ctx, &mem_16066, "mem_16066") != 0)
        return 1;
    
    float i32_res_15436 = sitofp_i32_f32(num_mc_it_13576);
    
    if (mem_16390_cached_sizze_16487 < bytes_16062) {
        err = lexical_realloc(&ctx->error, &mem_16390,
                              &mem_16390_cached_sizze_16487, bytes_16062);
        if (err != FUTHARK_SUCCESS)
            goto cleanup;
    }
    for (int64_t i_15870 = 0; i_15870 < num_models_13571; i_15870++) {
        float x_15438;
        
        x_15438 = ((float *) ext_mem_16383.mem)[i_15870];
        
        float defunc_0_f_res_15439 = x_15438 / i32_res_15436;
        
        ((float *) mem_16390)[i_15870] = defunc_0_f_res_15439;
    }
    if (memblock_unref(ctx, &ext_mem_16383, "ext_mem_16383") != 0)
        return 1;
    if (memblock_alloc(ctx, &mem_16405, bytes_16062, "mem_16405")) {
        err = 1;
        goto cleanup;
    }
    if (num_models_13571 * (int64_t) 4 > 0)
        memmove(mem_16405.mem + (int64_t) 0, mem_16390 + (int64_t) 0,
                num_models_13571 * (int64_t) 4);
    if (memblock_set(ctx, &mem_out_16444, &mem_16405, "mem_16405") != 0)
        return 1;
    (*mem_out_p_16473).references = NULL;
    if (memblock_set(ctx, &*mem_out_p_16473, &mem_out_16444, "mem_out_16444") !=
        0)
        return 1;
    
  cleanup:
    {
        free(mem_15994);
        free(mem_16007);
        free(mem_16022);
        free(mem_16037);
        free(mem_16052);
        free(mem_16076);
        free(mem_16092);
        free(mem_16105);
        free(mem_16162);
        free(mem_16180);
        free(mem_16200);
        free(mem_16339);
        free(mem_16348);
        free(mem_16390);
        if (memblock_unref(ctx, &mem_16405, "mem_16405") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_param_tmp_16452, "mem_param_tmp_16452") !=
            0)
            return 1;
        if (memblock_unref(ctx, &mem_16370, "mem_16370") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_param_tmp_16460, "mem_param_tmp_16460") !=
            0)
            return 1;
        if (memblock_unref(ctx, &mem_16237, "mem_16237") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_param_16185, "mem_param_16185") != 0)
            return 1;
        if (memblock_unref(ctx, &ext_mem_16241, "ext_mem_16241") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_param_16071, "mem_param_16071") != 0)
            return 1;
        if (memblock_unref(ctx, &ext_mem_16383, "ext_mem_16383") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_16066, "mem_16066") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_16063, "mem_16063") != 0)
            return 1;
        if (memblock_unref(ctx, &mem_out_16444, "mem_out_16444") != 0)
            return 1;
    }
    return err;
}

int futhark_entry_main(struct futhark_context *ctx,
                       struct futhark_f32_1d **out0, const int32_t in0, const
                       int32_t in1, const struct futhark_i32_2d *in2, const
                       struct futhark_f32_3d *in3, const
                       struct futhark_f32_3d *in4, const
                       struct futhark_f32_3d *in5, const
                       struct futhark_f32_2d *in6, const
                       struct futhark_f32_2d *in7, const
                       struct futhark_f32_2d *in8, const
                       struct futhark_i32_2d *in9, const
                       struct futhark_f32_2d *in10)
{
    int64_t k_13569;
    int64_t num_bits_13570;
    int64_t num_models_13571;
    int64_t num_und_13572;
    int64_t num_dates_13573;
    int64_t num_discts_13574;
    int32_t contract_number_13575;
    int32_t num_mc_it_13576;
    int ret = 0;
    
    lock_lock(&ctx->lock);
    
    struct memblock mem_out_16444;
    
    mem_out_16444.references = NULL;
    
    struct memblock bb_data_mem_15990;
    
    bb_data_mem_15990.references = NULL;
    
    struct memblock bb_inds_mem_15989;
    
    bb_inds_mem_15989.references = NULL;
    
    struct memblock md_discts_mem_15988;
    
    md_discts_mem_15988.references = NULL;
    
    struct memblock md_detvals_mem_15987;
    
    md_detvals_mem_15987.references = NULL;
    
    struct memblock md_sts_mem_15986;
    
    md_sts_mem_15986.references = NULL;
    
    struct memblock md_drifts_mem_15985;
    
    md_drifts_mem_15985.references = NULL;
    
    struct memblock md_vols_mem_15984;
    
    md_vols_mem_15984.references = NULL;
    
    struct memblock md_cs_mem_15983;
    
    md_cs_mem_15983.references = NULL;
    
    struct memblock dir_vs_mem_15982;
    
    dir_vs_mem_15982.references = NULL;
    contract_number_13575 = in0;
    num_mc_it_13576 = in1;
    dir_vs_mem_15982 = in2->mem;
    k_13569 = in2->shape[0];
    num_bits_13570 = in2->shape[1];
    md_cs_mem_15983 = in3->mem;
    num_models_13571 = in3->shape[0];
    num_und_13572 = in3->shape[1];
    num_und_13572 = in3->shape[2];
    md_vols_mem_15984 = in4->mem;
    num_models_13571 = in4->shape[0];
    num_dates_13573 = in4->shape[1];
    num_und_13572 = in4->shape[2];
    md_drifts_mem_15985 = in5->mem;
    num_models_13571 = in5->shape[0];
    num_dates_13573 = in5->shape[1];
    num_und_13572 = in5->shape[2];
    md_sts_mem_15986 = in6->mem;
    num_models_13571 = in6->shape[0];
    num_und_13572 = in6->shape[1];
    md_detvals_mem_15987 = in7->mem;
    num_models_13571 = in7->shape[0];
    md_discts_mem_15988 = in8->mem;
    num_models_13571 = in8->shape[0];
    num_discts_13574 = in8->shape[1];
    bb_inds_mem_15989 = in9->mem;
    num_dates_13573 = in9->shape[1];
    bb_data_mem_15990 = in10->mem;
    num_dates_13573 = in10->shape[1];
    if (!((k_13569 == in2->shape[0] && num_bits_13570 == in2->shape[1]) &&
          ((num_models_13571 == in3->shape[0] && (num_und_13572 ==
                                                  in3->shape[1] &&
                                                  num_und_13572 ==
                                                  in3->shape[2])) &&
           ((num_models_13571 == in4->shape[0] && (num_dates_13573 ==
                                                   in4->shape[1] &&
                                                   num_und_13572 ==
                                                   in4->shape[2])) &&
            ((num_models_13571 == in5->shape[0] && (num_dates_13573 ==
                                                    in5->shape[1] &&
                                                    num_und_13572 ==
                                                    in5->shape[2])) &&
             ((num_models_13571 == in6->shape[0] && num_und_13572 ==
               in6->shape[1]) && ((num_models_13571 == in7->shape[0] &&
                                   (int64_t) 1 == in7->shape[1]) &&
                                  ((num_models_13571 == in8->shape[0] &&
                                    num_discts_13574 == in8->shape[1]) &&
                                   (((int64_t) 3 == in9->shape[0] &&
                                     num_dates_13573 == in9->shape[1]) &&
                                    ((int64_t) 3 == in10->shape[0] &&
                                     num_dates_13573 ==
                                     in10->shape[1])))))))))) {
        ret = 1;
        if (!ctx->error)
            ctx->error =
                msgprintf("Error: entry point arguments have invalid sizes.\n");
    }
    if (ret == 0) {
        ret = futrts_entry_main(ctx, &mem_out_16444, dir_vs_mem_15982,
                                md_cs_mem_15983, md_vols_mem_15984,
                                md_drifts_mem_15985, md_sts_mem_15986,
                                md_detvals_mem_15987, md_discts_mem_15988,
                                bb_inds_mem_15989, bb_data_mem_15990, k_13569,
                                num_bits_13570, num_models_13571, num_und_13572,
                                num_dates_13573, num_discts_13574,
                                contract_number_13575, num_mc_it_13576);
        if (ret == 0) {
            assert((*out0 =
                    (struct futhark_f32_1d *) malloc(sizeof(struct futhark_f32_1d))) !=
                NULL);
            (*out0)->mem = mem_out_16444;
            (*out0)->shape[0] = num_models_13571;
        }
    }
    lock_unlock(&ctx->lock);
    return ret;
}
  
