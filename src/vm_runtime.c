#include <stdint.h>
#include <stddef.h>

#include "vm_abi.h"

typedef struct {
    uint8_t opcode, width, reg, base, index, scale, flags, unused;
    int64_t value, target;
} VmOp;

typedef struct {
    uint8_t opcode, width, dst, src, base, index, scale, flags;
    int64_t value, target;
} VmRegOp;

typedef struct {
    uint64_t key;
    uint8_t architecture, variant;
    uint16_t blocks;
    uint32_t table;
} VmCodec;

typedef struct {
    uint8_t header[8], words[3], rounds[6];
} VmFormat;

typedef struct {
    uint64_t gpr[16];
    uint64_t flags, pc, ops, count, native_target, entry_rsp, host_sp;
    const VmCodec *codec;
    uint64_t stack_len;
    union {
        uint64_t stack[32];
        uint64_t temporaries[32];
    };
    uint64_t entry_saved[6];
} VmContext;

_Static_assert(sizeof(VmOp) == VM_OP_LEN, "VmOp layout");
_Static_assert(offsetof(VmOp, value) == 8 && offsetof(VmOp, target) == 16, "VmOp operands");
_Static_assert(sizeof(VmRegOp) == VM_OP_LEN, "VmRegOp layout");
_Static_assert(offsetof(VmRegOp, value) == 8 && offsetof(VmRegOp, target) == 16, "VmRegOp operands");
_Static_assert(sizeof(VmCodec) == VM_CODEC_LEN, "VmCodec layout");
_Static_assert(offsetof(VmCodec, architecture) == VM_CODEC_ARCH, "VmCodec architecture");
_Static_assert(offsetof(VmCodec, variant) == VM_CODEC_VARIANT, "VmCodec variant");
_Static_assert(offsetof(VmCodec, blocks) == VM_CODEC_BLOCKS, "VmCodec blocks");
_Static_assert(offsetof(VmCodec, table) == VM_CODEC_TABLE, "VmCodec table");
_Static_assert(sizeof(VmContext) == VM_CONTEXT_SIZE, "VmContext layout");
_Static_assert(VM_FRAME_SHIFT % 16 == 0 && VM_HOST_STACK % 16 == 0, "VM stack alignment");
_Static_assert(VM_CONTEXT_OFFSET >= 8, "context overlaps guest return address");
_Static_assert(VM_CONTEXT_OFFSET + VM_CONTEXT_SIZE <= VM_FRAME_SHIFT - 128,
               "context overlaps entry register saves");
#define CHECK(field, offset) _Static_assert(offsetof(VmContext, field) == offset, #field " offset")
CHECK(flags, VM_FLAGS);
CHECK(pc, VM_PC);
CHECK(ops, VM_OPS);
CHECK(count, VM_COUNT);
CHECK(native_target, VM_NATIVE_TARGET);
CHECK(entry_rsp, VM_ENTRY_RSP);
CHECK(host_sp, VM_HOST_SP);
CHECK(codec, VM_CODEC);
CHECK(stack_len, VM_STACK_LEN);
CHECK(stack, VM_STACK);
CHECK(temporaries, VM_STACK);
CHECK(entry_saved, VM_ENTRY_SAVED);

extern void vm_native_enter(void) __attribute__((noreturn));
extern void vm_finish(void) __attribute__((noreturn));
extern void vm_tail(void) __attribute__((noreturn));
extern void vm_abort(void) __attribute__((noreturn));

static inline uint64_t mask_for(unsigned width)
{
    return width == 8 ? UINT64_MAX : (UINT64_C(1) << (width * 8)) - 1;
}

static inline uint64_t reg_read(const VmContext *ctx, unsigned reg, unsigned width, unsigned high)
{
    uint64_t value = ctx->gpr[reg];
    if (high) value >>= 8;
    return value & mask_for(width);
}

static inline void reg_write(VmContext *ctx, unsigned reg, unsigned width, unsigned high, uint64_t value)
{
    if (width == 8) {
        ctx->gpr[reg] = value;
    } else if (width == 4) {
        ctx->gpr[reg] = (uint32_t)value;
    } else {
        unsigned shift = high ? 8 : 0;
        uint64_t mask = mask_for(width) << shift;
        ctx->gpr[reg] = (ctx->gpr[reg] & ~mask) | ((value << shift) & mask);
    }
}

static inline uint64_t address(const VmContext *ctx, const void *record,
                               unsigned base, unsigned index, unsigned scale, int64_t displacement)
{
    if (base == 254) return (uint64_t)(uintptr_t)record + (uint64_t)displacement;
    uint64_t value = (uint64_t)displacement;
    if (base < 16) value += ctx->gpr[base];
    if (index < 16) value += ctx->gpr[index] * scale;
    return value;
}

static inline int valid_address(unsigned base, unsigned index, unsigned scale)
{
    return (base < 16 || base == 254 || base == 255) &&
           (index < 16 || index == 255) && (base != 254 || index == 255) &&
           (scale == 1 || scale == 2 || scale == 4 || scale == 8);
}

static inline int valid_width(unsigned width)
{
    return width == 1 || width == 2 || width == 4 || width == 8;
}

static inline int valid_register(unsigned reg, unsigned width, unsigned flags)
{
    return reg < 16 && (!(flags & 1) || (reg < 4 && width == 1));
}

typedef uint16_t u16 __attribute__((aligned(1), may_alias));
typedef uint32_t u32 __attribute__((aligned(1), may_alias));
typedef uint64_t u64 __attribute__((aligned(1), may_alias));

static inline uint64_t memory_read(uint64_t address, unsigned width)
{
    switch (width) {
    case 1: return *(volatile uint8_t *)address;
    case 2: return *(volatile u16 *)address;
    case 4: return *(volatile u32 *)address;
    default: return *(volatile u64 *)address;
    }
}

static inline void memory_write(uint64_t address, unsigned width, uint64_t value)
{
    switch (width) {
    case 1: *(volatile uint8_t *)address = (uint8_t)value; break;
    case 2: *(volatile u16 *)address = (uint16_t)value; break;
    case 4: *(volatile u32 *)address = (uint32_t)value; break;
    default: *(volatile u64 *)address = value; break;
    }
}

static inline void push(VmContext *ctx, uint64_t value)
{
    if (ctx->stack_len == 32) vm_abort();
    ctx->stack[ctx->stack_len++] = value;
}

static inline uint64_t pop(VmContext *ctx)
{
    if (ctx->stack_len == 0) vm_abort();
    return ctx->stack[--ctx->stack_len];
}

static inline uint64_t sign_extend(uint64_t value, unsigned width)
{
    unsigned bits = width * 8;
    uint64_t sign = UINT64_C(1) << (bits - 1);
    return (value ^ sign) - sign;
}

static inline void set_flags(VmContext *ctx, uint64_t a, uint64_t b, uint64_t result,
                             unsigned width, unsigned op, unsigned mode)
{
    if (mode & VM_PRESERVE_FLAGS) return;
    uint64_t mask = mask_for(width);
    uint64_t sign = UINT64_C(1) << (width * 8 - 1);
    uint64_t value = result & mask;
    uint64_t carry = mode & VM_USE_CF ? ctx->flags & 1 : 0;
    uint64_t flags = ctx->flags & ~(UINT64_C(1) | 4 | 16 | 64 | 128 | 2048);
    if (value == 0) flags |= 64;
    if (value & sign) flags |= 128;
    if (!__builtin_parity((unsigned char)value)) flags |= 4;
    if (op == VM_ADD) {
        if (value < (a & mask) || (carry && (b & mask) == mask)) flags |= 1;
        if ((~(a ^ b) & (a ^ value) & sign) != 0) flags |= 2048;
        if (((a ^ b ^ value) & 16) != 0) flags |= 16;
    } else if (op == VM_SUB || op == VM_CMP) {
        if ((a & mask) < (b & mask) || (carry && (a & mask) == (b & mask))) flags |= 1;
        if (((a ^ b) & (a ^ value) & sign) != 0) flags |= 2048;
        if (((a ^ b ^ value) & 16) != 0) flags |= 16;
    }
    if (mode & VM_PRESERVE_CF) flags = (flags & ~UINT64_C(1)) | (ctx->flags & 1);
    ctx->flags = flags;
}

static inline uint64_t shift_or_rotate(VmContext *ctx, uint64_t source, unsigned width,
                                       unsigned mode, unsigned count)
{
    unsigned bits = width * 8;
    uint64_t mask = mask_for(width);
    uint64_t sign = UINT64_C(1) << (bits - 1);
    uint64_t value = source & mask;
    uint64_t carry, result;
    if (mode == VM_ROTATE_LEFT || mode == VM_ROTATE_RIGHT) {
        if (mode == VM_ROTATE_LEFT) {
            result = ((value << count) | (value >> (bits - count))) & mask;
            carry = result & 1;
        } else {
            result = ((value >> count) | (value << (bits - count))) & mask;
            carry = (result & sign) != 0;
        }
        uint64_t flags = ctx->flags & ~UINT64_C(1);
        if (count == 1) {
            flags &= ~UINT64_C(2048);
            if (mode == VM_ROTATE_LEFT ? ((result & sign) != 0) != (carry != 0) :
                ((result & sign) != 0) != ((result & (sign >> 1)) != 0)) flags |= 2048;
        }
        if (carry) flags |= 1;
        ctx->flags = flags;
        return result;
    }
    if (mode == VM_SHIFT_LEFT) {
        carry = (value >> (bits - count)) & 1;
        result = (value << count) & mask;
    } else {
        carry = (value >> (count - 1)) & 1;
        result = value >> count;
        if (mode == VM_SHIFT_ARITH && (value & sign))
            result |= mask ^ (mask >> count);
    }
    uint64_t flags = ctx->flags & ~(UINT64_C(1) | 4 | 64 | 128);
    if (count == 1) flags &= ~UINT64_C(2048);
    if (carry) flags |= 1;
    if (!__builtin_parity((unsigned char)result)) flags |= 4;
    if (result == 0) flags |= 64;
    if (result & sign) flags |= 128;
    if (count == 1 &&
        ((mode == VM_SHIFT_LEFT && ((result & sign) != 0) != (carry != 0)) ||
         (mode == VM_SHIFT_RIGHT && (value & sign)))) flags |= 2048;
    ctx->flags = flags;
    return result;
}

static inline int valid_alu_mode(unsigned op, unsigned mode)
{
    if (op == VM_ADD || op == VM_SUB)
        return mode == 0 || mode == VM_PRESERVE_CF || mode == VM_USE_CF;
    if (op == VM_BXOR)
        return mode == 0 || mode == VM_PRESERVE_FLAGS;
    return mode == 0;
}

static inline int condition(uint64_t flags, unsigned code)
{
    int cf = (flags & 1) != 0, pf = (flags & 4) != 0;
    int zf = (flags & 64) != 0, sf = (flags & 128) != 0;
    int of = (flags & 2048) != 0;
    switch (code) {
    case 0: return of;
    case 1: return !of;
    case 2: return cf;
    case 3: return !cf;
    case 4: return zf;
    case 5: return !zf;
    case 6: return cf || zf;
    case 7: return !cf && !zf;
    case 8: return sf;
    case 9: return !sf;
    case 10: return pf;
    case 11: return !pf;
    case 12: return sf != of;
    case 13: return sf == of;
    case 14: return zf || sf != of;
    default: return !zf && sf == of;
    }
}

static inline uint64_t vm_seed(uint64_t key, uint64_t number)
{
    uint64_t value = key ^ number ^ UINT64_C(0x6a09e667f3bcc909);
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static inline uint64_t branch_pc(const VmContext *ctx, int64_t token)
{
    if (token < 0 || (uint64_t)token >= ctx->codec->blocks) vm_abort();
    const uint8_t *table = (const uint8_t *)(uintptr_t)ctx->ops + ctx->codec->table;
    uint32_t encoded;
    __builtin_memcpy(&encoded, table + (uint64_t)token * 4, 4);
    uint32_t pc = encoded ^ (uint32_t)vm_seed(ctx->codec->key ^ UINT64_C(0x1f83d9abfb41bd6b),
                                              (uint64_t)token);
    if (pc >= ctx->count) vm_abort();
    return pc;
}

static inline void vm_permutation(uint8_t *order, unsigned len, uint64_t seed)
{
    uint64_t state = seed ^ UINT64_C(0xd1b54a32d192ed03);
    for (unsigned i = 0; i < len; ++i) order[i] = (uint8_t)i;
    for (unsigned i = len - 1; i > 0; --i) {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        unsigned j = (unsigned)((state * UINT64_C(0x2545f4914f6cdd1d)) % (i + 1));
        uint8_t tmp = order[i];
        order[i] = order[j];
        order[j] = tmp;
    }
}

static inline void vm_format(VmFormat *format, uint64_t key)
{
    vm_permutation(format->header, 8, key ^ UINT64_C(0x3c6ef372fe94f82b));
    vm_permutation(format->words, 3, key ^ UINT64_C(0xa54ff53a5f1d36f1));
    for (unsigned i = 0; i < 6; ++i)
        format->rounds[i] = (uint8_t)vm_seed(key ^ UINT64_C(0xbb67ae8584caa73b), i) & 15;
}

static inline uint8_t vm_round(uint8_t right, uint8_t key)
{
    return (uint8_t)(((5 * right + key) ^ ((right << 1) | (right >> 3))) & 15);
}

static inline uint8_t vm_opcode(uint8_t value, const VmFormat *format)
{
    uint8_t left = value >> 4, right = value & 15;
    for (int i = 5; i >= 0; --i) {
        uint8_t next = left;
        left = right ^ vm_round(left, format->rounds[i]);
        right = next;
    }
    return (left << 4) | right;
}

// PC masks keep RX records encoded across native calls and nonlocal returns.
static inline void decode_record(void *decoded, const void *wire, const VmCodec *codec,
                                 const VmFormat *format, uint64_t pc)
{
    uint8_t unmasked[VM_OP_LEN];
    for (unsigned word = 0; word < VM_OP_LEN / 8; ++word) {
        uint64_t value;
        __builtin_memcpy(&value, (const uint8_t *)wire + word * 8, 8);
        value ^= vm_seed(codec->key ^ (word * UINT64_C(0x9e3779b97f4a7c15)), pc);
        __builtin_memcpy(unmasked + word * 8, &value, 8);
    }
    uint8_t *out = decoded;
    const uint8_t *header = unmasked + format->words[0] * 8;
    for (unsigned byte = 0; byte < 8; ++byte)
        out[byte] = header[format->header[byte]];
    __builtin_memcpy(out + 8, unmasked + format->words[1] * 8, 8);
    __builtin_memcpy(out + 16, unmasked + format->words[2] * 8, 8);
    out[0] = vm_opcode(out[0], format);
    unsigned code = out[0];
    if (!((codec->architecture == VM_ARCH_STACK && code >= VM_PUSH_REG && code <= VM_SHIFT) ||
          (codec->architecture == VM_ARCH_REGISTER && code >= VM_R_READ_REG && code <= VM_R_SHIFT) ||
          (code >= VM_F_MOV_RR && code <= VM_F_TEST))) vm_abort();
}

static inline void execute_fused(VmContext *ctx, const void *decoded, const void *wire)
{
    const uint8_t *record = decoded;
    unsigned op = record[0], width = record[1], dst = record[2], src = record[3];
    unsigned base = record[4], index = record[5], scale = record[6], flags = record[7];
    int64_t value;
    __builtin_memcpy(&value, record + 8, 8);
    if (!valid_width(width) || flags > 3) vm_abort();
    if (op == VM_F_STORE) {
        if (!valid_register(src, width, flags >> 1) || !valid_address(base, index, scale)) vm_abort();
        memory_write(address(ctx, wire, base, index, scale, value), width,
                     reg_read(ctx, src, width, flags >> 1));
        return;
    }
    if (!valid_register(dst, width, flags)) vm_abort();
    if (op == VM_F_LOAD) {
        if (!valid_address(base, index, scale)) vm_abort();
        reg_write(ctx, dst, width, flags, memory_read(address(ctx, wire, base, index, scale, value), width));
        return;
    }
    if (op == VM_F_MOV_IR) {
        reg_write(ctx, dst, width, flags, (uint64_t)value);
        return;
    }
    if (src != 255 && !valid_register(src, width, flags >> 1)) vm_abort();
    if (op == VM_F_MOV_RR) {
        if (src == 255) vm_abort();
        reg_write(ctx, dst, width, flags, reg_read(ctx, src, width, flags >> 1));
        return;
    }
    uint64_t a = reg_read(ctx, dst, width, flags & 1);
    uint64_t b = src == 255 ? (uint64_t)value : reg_read(ctx, src, width, flags >> 1);
    uint64_t result;
    if (op == VM_F_ADD) result = a + b;
    else if (op == VM_F_SUB || op == VM_F_CMP) result = a - b;
    else if (op == VM_F_XOR) result = a ^ b;
    else if (op == VM_F_AND || op == VM_F_TEST) result = a & b;
    else if (op == VM_F_OR) result = a | b;
    else vm_abort();
    set_flags(ctx, a, b, result, width, op - VM_F_ADD + VM_ADD, 0);
    if (op != VM_F_CMP && op != VM_F_TEST)
        reg_write(ctx, dst, width, flags & 1, result & mask_for(width));
}

static inline void execute_register_alu(VmContext *ctx, const VmRegOp *ins, unsigned op)
{
    uint64_t a = ctx->temporaries[ins->dst] & mask_for(ins->width);
    uint64_t b = ctx->temporaries[ins->src] & mask_for(ins->width);
    uint64_t carry = ins->flags & VM_USE_CF ? ctx->flags & 1 : 0;
    uint64_t result;
    if (op == VM_R_ADD) result = a + b + carry;
    else if (op == VM_R_SUB) result = a - b - carry;
    else if (op == VM_R_CMP) result = a - b;
    else if (op == VM_R_XOR) result = a ^ b;
    else if (op == VM_R_AND || op == VM_R_TEST) result = a & b;
    else result = a | b;
    set_flags(ctx, a, b, result, ins->width, op - VM_R_ADD + VM_ADD, ins->flags);
    if (op != VM_R_CMP && op != VM_R_TEST) ctx->temporaries[ins->dst] = result & mask_for(ins->width);
}

static inline void execute_stack_alu(VmContext *ctx, const VmOp *ins, unsigned op)
{
    uint64_t b = pop(ctx) & mask_for(ins->width);
    uint64_t a = pop(ctx) & mask_for(ins->width);
    uint64_t carry = ins->flags & VM_USE_CF ? ctx->flags & 1 : 0;
    uint64_t result;
    if (op == VM_ADD) result = a + b + carry;
    else if (op == VM_SUB) result = a - b - carry;
    else if (op == VM_CMP) result = a - b;
    else if (op == VM_BXOR) result = a ^ b;
    else if (op == VM_BAND || op == VM_TEST) result = a & b;
    else result = a | b;
    set_flags(ctx, a, b, result, ins->width, op, ins->flags);
    if (op != VM_CMP && op != VM_TEST) push(ctx, result & mask_for(ins->width));
}

__attribute__((section(".vmruntime"), noreturn))
void vm_run(VmContext *ctx)
{
    if (ctx->count == 0 || ctx->count > 65535 || ctx->codec->blocks == 0 ||
        ctx->codec->blocks > ctx->count || ctx->codec->table != ctx->count * VM_OP_LEN)
        vm_abort();
    VmFormat format;
    vm_format(&format, ctx->codec->key);
    if (ctx->codec->architecture == VM_ARCH_REGISTER) {
        const VmRegOp *ops = (const VmRegOp *)ctx->ops;
        for (;;) {
            if (ctx->pc >= ctx->count) vm_abort();
            uint64_t pc = ctx->pc++;
            const VmRegOp *wire = &ops[pc];
            VmRegOp decoded;
            decode_record(&decoded, wire, ctx->codec, &format, pc);
            const VmRegOp *ins = &decoded;
            unsigned op = ins->opcode;
            if (op >= VM_F_MOV_RR && op <= VM_F_TEST) { execute_fused(ctx, ins, wire); continue; }
            if (ins->dst >= 32 || ins->src >= 32) vm_abort();
            if (op <= VM_R_TEST && !valid_width(ins->width)) vm_abort();
            if (op >= VM_R_ADD && op <= VM_R_TEST &&
                !valid_alu_mode(op - VM_R_ADD + VM_ADD, ins->flags)) vm_abort();
            if ((op == VM_R_READ_REG && !valid_register(ins->src, ins->width, ins->flags)) ||
                (op == VM_R_WRITE_REG && !valid_register(ins->dst, ins->width, ins->flags)))
                vm_abort();
            if ((op == VM_R_LOAD || op == VM_R_STORE || op == VM_R_ADDR) &&
                !valid_address(ins->base, ins->index, ins->scale)) vm_abort();
            if ((op == VM_R_JMP || op == VM_R_JCC) && (uint64_t)ins->target >= ctx->codec->blocks) vm_abort();
            if (op == VM_R_JCC && ins->flags > 15) vm_abort();
            if (op == VM_R_CC &&
                (ins->width != 0 || ins->src != 0 || ins->base != 255 || ins->index != 255 ||
                 ins->scale != 1 || ins->flags > 15 || ins->value != 0 || ins->target != 0)) vm_abort();
            if (op == VM_R_CMOV_REG &&
                (!valid_width(ins->width) || ins->width == 1 || ins->dst >= 16 ||
                 ins->base != 255 || ins->index != 255 || ins->scale != 1 ||
                 ins->flags > 15 || ins->value != 0 || ins->target != 0)) vm_abort();
            if (op == VM_R_BSWAP &&
                ((ins->width != 4 && ins->width != 8) || ins->src != 0 ||
                 ins->base != 255 || ins->index != 255 || ins->scale != 1 ||
                 ins->flags != 0 || ins->value != 0 || ins->target != 0)) vm_abort();
            if (op == VM_R_SHIFT &&
                (!valid_width(ins->width) || ins->src != 0 ||
                 ins->base != 255 || ins->index != 255 || ins->scale != 1 ||
                 ins->flags > VM_ROTATE_RIGHT || ins->value <= 0 ||
                 ins->value >= ins->width * 8 || ins->target != 0)) vm_abort();
            uint64_t a;
#if VM_VARIANT == 1
            if (op >= VM_R_ADD && op <= VM_R_TEST) {
                execute_register_alu(ctx, ins, op);
                continue;
            }
#endif
            switch (op) {
            case VM_R_READ_REG:
                a = reg_read(ctx, ins->src, ins->width, ins->flags & 1);
                ctx->temporaries[ins->dst] = ins->flags & 2 ? sign_extend(a, ins->width) : a;
                break;
            case VM_R_IMM:
                ctx->temporaries[ins->dst] = (uint64_t)ins->value;
                break;
            case VM_R_CC:
                ctx->temporaries[ins->dst] = condition(ctx->flags, ins->flags);
                break;
            case VM_R_LOAD:
                a = memory_read(address(ctx, wire, ins->base, ins->index, ins->scale, ins->value), ins->width);
                ctx->temporaries[ins->dst] = ins->flags & 2 ? sign_extend(a, ins->width) : a;
                break;
            case VM_R_WRITE_REG:
                reg_write(ctx, ins->dst, ins->width, ins->flags & 1, ctx->temporaries[ins->src]);
                break;
            case VM_R_CMOV_REG:
                if (condition(ctx->flags, ins->flags))
                    reg_write(ctx, ins->dst, ins->width, 0, ctx->temporaries[ins->src]);
                else if (ins->width == 4)
                    reg_write(ctx, ins->dst, 4, 0, reg_read(ctx, ins->dst, 4, 0));
                break;
            case VM_R_BSWAP:
                a = ctx->temporaries[ins->dst];
                ctx->temporaries[ins->dst] = ins->width == 4 ?
                    __builtin_bswap32((uint32_t)a) : __builtin_bswap64(a);
                break;
            case VM_R_SHIFT:
                ctx->temporaries[ins->dst] = shift_or_rotate(ctx, ctx->temporaries[ins->dst],
                                                              ins->width, ins->flags, (unsigned)ins->value);
                break;
            case VM_R_STORE:
                memory_write(address(ctx, wire, ins->base, ins->index, ins->scale, ins->value), ins->width,
                             ctx->temporaries[ins->src]);
                break;
            case VM_R_ADDR:
                ctx->temporaries[ins->dst] = address(ctx, wire, ins->base, ins->index, ins->scale, ins->value);
                break;
#if VM_VARIANT == 0
            case VM_R_ADD: case VM_R_SUB: case VM_R_XOR: case VM_R_AND: case VM_R_OR: case VM_R_CMP: case VM_R_TEST:
                execute_register_alu(ctx, ins, op);
                break;
#endif
            case VM_R_JMP:
                ctx->pc = branch_pc(ctx, ins->target);
                break;
            case VM_R_JCC:
                if (condition(ctx->flags, ins->flags)) ctx->pc = branch_pc(ctx, ins->target);
                break;
            case VM_R_NATIVE:
                ctx->native_target = (uint64_t)(uintptr_t)wire + (uint64_t)ins->target;
                vm_native_enter();
            case VM_R_RET:
                vm_finish();
            case VM_R_TAIL:
                ctx->native_target = (uint64_t)(uintptr_t)wire + (uint64_t)ins->target;
                vm_tail();
            default:
                vm_abort();
            }
        }
    }
    if (ctx->codec->architecture != VM_ARCH_STACK) vm_abort();
    const VmOp *ops = (const VmOp *)ctx->ops;
    for (;;) {
        if (ctx->pc >= ctx->count) vm_abort();
        uint64_t pc = ctx->pc++;
        const VmOp *wire = &ops[pc];
        VmOp decoded;
        decode_record(&decoded, wire, ctx->codec, &format, pc);
        const VmOp *ins = &decoded;
        unsigned op = ins->opcode;
        if (op >= VM_F_MOV_RR && op <= VM_F_TEST) {
            if (ctx->stack_len != 0) vm_abort();
            execute_fused(ctx, ins, wire);
            continue;
        }
        if (op <= VM_TEST && !valid_width(ins->width)) vm_abort();
        if (op >= VM_ADD && op <= VM_TEST && !valid_alu_mode(op, ins->flags)) vm_abort();
        if ((op == VM_PUSH_REG || op == VM_POP_REG) &&
            !valid_register(ins->reg, ins->width, ins->flags)) vm_abort();
        if ((op == VM_PUSH_MEM || op == VM_POP_MEM || op == VM_LEA) &&
            !valid_address(ins->base, ins->index, ins->scale)) vm_abort();
        if ((op == VM_JMP || op == VM_JCC) && (uint64_t)ins->target >= ctx->codec->blocks) vm_abort();
        if (op == VM_JCC && ins->flags > 15) vm_abort();
        if (op == VM_PUSH_CC &&
            (ins->width != 0 || ins->reg != 0 || ins->base != 255 || ins->index != 255 ||
             ins->scale != 1 || ins->flags > 15 || ins->unused != 0 ||
             ins->value != 0 || ins->target != 0)) vm_abort();
        if (op == VM_CMOV_REG &&
            (!valid_width(ins->width) || ins->width == 1 || ins->reg >= 16 ||
             ins->base != 255 || ins->index != 255 || ins->scale != 1 ||
             ins->flags > 15 || ins->unused != 0 ||
             ins->value != 0 || ins->target != 0)) vm_abort();
        if (op == VM_BSWAP &&
            ((ins->width != 4 && ins->width != 8) || ins->reg != 0 ||
             ins->base != 255 || ins->index != 255 || ins->scale != 1 ||
             ins->flags != 0 || ins->unused != 0 ||
             ins->value != 0 || ins->target != 0)) vm_abort();
        if (op == VM_SHIFT &&
            (!valid_width(ins->width) || ins->reg != 0 ||
             ins->base != 255 || ins->index != 255 || ins->scale != 1 ||
             ins->flags > VM_ROTATE_RIGHT || ins->unused != 0 ||
             ins->value <= 0 || ins->value >= ins->width * 8 || ins->target != 0)) vm_abort();
        uint64_t a;
#if VM_VARIANT == 1
        if (op >= VM_ADD && op <= VM_TEST) {
            execute_stack_alu(ctx, ins, op);
            continue;
        }
#endif
        switch (op) {
        case VM_PUSH_REG:
            a = reg_read(ctx, ins->reg, ins->width, ins->flags & 1);
            push(ctx, ins->flags & 2 ? sign_extend(a, ins->width) : a);
            break;
        case VM_PUSH_IMM:
            push(ctx, (uint64_t)ins->value);
            break;
        case VM_PUSH_CC:
            push(ctx, condition(ctx->flags, ins->flags));
            break;
        case VM_PUSH_MEM:
            a = memory_read(address(ctx, wire, ins->base, ins->index, ins->scale, ins->value), ins->width);
            push(ctx, ins->flags & 2 ? sign_extend(a, ins->width) : a);
            break;
        case VM_POP_REG:
            reg_write(ctx, ins->reg, ins->width, ins->flags & 1, pop(ctx));
            break;
        case VM_CMOV_REG:
            a = pop(ctx);
            if (condition(ctx->flags, ins->flags))
                reg_write(ctx, ins->reg, ins->width, 0, a);
            else if (ins->width == 4)
                reg_write(ctx, ins->reg, 4, 0, reg_read(ctx, ins->reg, 4, 0));
            break;
        case VM_BSWAP:
            a = pop(ctx);
            push(ctx, ins->width == 4 ?
                 __builtin_bswap32((uint32_t)a) : __builtin_bswap64(a));
            break;
        case VM_SHIFT:
            a = pop(ctx);
            push(ctx, shift_or_rotate(ctx, a, ins->width, ins->flags, (unsigned)ins->value));
            break;
        case VM_POP_MEM:
            memory_write(address(ctx, wire, ins->base, ins->index, ins->scale, ins->value), ins->width, pop(ctx));
            break;
        case VM_LEA:
            push(ctx, address(ctx, wire, ins->base, ins->index, ins->scale, ins->value));
            break;
#if VM_VARIANT == 0
        case VM_ADD: case VM_SUB: case VM_BXOR: case VM_BAND: case VM_BOR: case VM_CMP: case VM_TEST:
            execute_stack_alu(ctx, ins, op);
            break;
#endif
        case VM_JMP:
            ctx->pc = branch_pc(ctx, ins->target);
            break;
        case VM_JCC:
            if (condition(ctx->flags, ins->flags & 15)) ctx->pc = branch_pc(ctx, ins->target);
            break;
        case VM_NATIVE:
            if (ctx->stack_len != 0) vm_abort();
            ctx->native_target = (uint64_t)(uintptr_t)wire + (uint64_t)ins->target;
            vm_native_enter();
        case VM_RET:
            if (ctx->stack_len != 0) vm_abort();
            vm_finish();
        case VM_TAIL:
            if (ctx->stack_len != 0) vm_abort();
            ctx->native_target = (uint64_t)(uintptr_t)wire + (uint64_t)ins->target;
            vm_tail();
        default:
            vm_abort();
        }
    }
}
