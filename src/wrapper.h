#include <stddef.h>
#include <stdint.h>

#define PARAM_T_STR 0b111
#define PARAM_T_U8 0b110
#define PARAM_T_I8 0b101
#define PARAM_T_I16 0b100
#define PARAM_T_I32 0b011
#define PARAM_T_I64 0b010
#define PARAM_T_F32 0b001
#define PARAM_T_F64 0b000

#define SCODE_ERROR_PARSE -2
#define SCODE_ERROR_DUMP -3
#define SCODE_ERROR_BUFFER -4
#define SCODE_ERROR_CRC -5
#define SCODE_ERROR_EMPTY -6

typedef struct {
  union {
    uint8_t u8;
    int8_t i8;
    int16_t i16;
    int32_t i32;
    int64_t i64;
    float f32;
    double f64;
    char *str;
  };
  uint8_t param;
} param_t;

typedef struct {
  param_t *params;
  uint8_t category;
  uint8_t number;
} code_t;

typedef struct {
  size_t end;
  size_t pos;
  size_t cap;
  char *buf;
} code_stream_t;

param_t init_param_u8(char param, uint8_t val);
param_t init_param_i8(char param, int8_t val);
param_t init_param_i16(char param, int16_t val);
param_t init_param_i32(char param, int32_t val);
param_t init_param_i64(char param, int64_t val);
param_t init_param_f32(char param, float val);
param_t init_param_f64(char param, double val);
param_t init_param_str(char param, const char *val);

uint8_t param_cast_u8(const param_t *self);
int8_t param_cast_i8(const param_t *self);
int16_t param_cast_i16(const param_t *self);
int32_t param_cast_i32(const param_t *self);
int64_t param_cast_i64(const param_t *self);
float param_cast_f32(const param_t *self);
double param_cast_f64(const param_t *self);

uint8_t param_type(const param_t *self);
char param_letter(const param_t *self);
void free_param(param_t *self);

int param_parse_binary(param_t *self, const char *buf, size_t len);
int param_parse_human(param_t *self, const char *buf, size_t len);
int param_dump_binary(const param_t *self, char *buf, size_t len);
int param_dump_human(const param_t *self, char *buf, size_t len);

code_t init_code(char letter, uint8_t number, size_t num_params);
void free_code(code_t *self);
int code_parse(code_t *self, const char *buf, size_t len);
int code_dump_binary(const code_t *self, char *buf, size_t len);
int code_dump_human(const code_t *self, char *buf, size_t len);
char code_letter(const code_t *self);
int code_is_binary(const code_t *self);

void free_code_stream(code_stream_t *self);
code_stream_t init_code_stream(size_t capacity);
void code_stream_update(code_stream_t *self, const char *buf, size_t len);
int code_stream_pop(code_stream_t *self, code_t *code);
