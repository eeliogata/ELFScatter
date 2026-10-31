.intel_syntax noprefix
#include "vm_abi.h"
.section .vmruntime,"ax",@progbits
.global vm_enter
.global vm_native_enter
.global vm_native_leave
.global vm_finish
.global vm_tail
.global vm_abort
.global vm_context_ready
.global vm_native_restored
.global vm_finish_restored
.global vm_return
.global vm_tail_restored
.global vm_tail_jump
.global vm_run
.extern vm_run_0
.extern vm_run_1

vm_enter:
    pushfq
    push rax
    push rcx
    push rdx
    push rbx
    push rbp
    push rsi
    push rdi
    push r8
    push r9
    push r10
    push r12
    push r13
    push r14
    push r15
    mov r12, r11
    mov r13, rsp
    lea r14, [r13 - VM_FRAME_SHIFT + 128 + VM_CONTEXT_OFFSET]
    mov rax, [r12 + 24]
    lea r11, [r13 + 128 - VM_FRAME_SHIFT]
    sub r11, rax
    sub r11, 128
    lea rax, [r11 - VM_HOST_STACK]
    mov r10, r13
.Lprobe:
    sub r10, 4096
    mov byte ptr [r10], 0
    cmp r10, rax
    ja .Lprobe
    mov r15, r14
    mov rax, [r13 + 104]
    mov [r15 + 0], rax
    mov rax, [r13 + 96]
    mov [r15 + 8], rax
    mov rax, [r13 + 88]
    mov [r15 + 16], rax
    mov rax, [r13 + 80]
    mov [r15 + 24], rax
    mov [r15 + VM_ENTRY_SAVED + 0], rax
    lea rax, [r13 + 128 - VM_FRAME_SHIFT]
    mov [r15 + 32], rax
    mov rax, [r13 + 72]
    mov [r15 + 40], rax
    mov [r15 + VM_ENTRY_SAVED + 8], rax
    mov rax, [r13 + 64]
    mov [r15 + 48], rax
    mov rax, [r13 + 56]
    mov [r15 + 56], rax
    mov rax, [r13 + 48]
    mov [r15 + 64], rax
    mov rax, [r13 + 40]
    mov [r15 + 72], rax
    mov rax, [r13 + 32]
    mov [r15 + 80], rax
    mov rax, [r13 + 120]
    mov [r15 + 88], rax
    mov rax, [r13 + 24]
    mov [r15 + 96], rax
    mov [r15 + VM_ENTRY_SAVED + 16], rax
    mov rax, [r13 + 16]
    mov [r15 + 104], rax
    mov [r15 + VM_ENTRY_SAVED + 24], rax
    mov rax, [r13 + 8]
    mov [r15 + 112], rax
    mov [r15 + VM_ENTRY_SAVED + 32], rax
    mov rax, [r13 + 0]
    mov [r15 + 120], rax
    mov [r15 + VM_ENTRY_SAVED + 40], rax
    mov rax, [r13 + 112]
    mov [r15 + VM_FLAGS], rax
    lea rax, [r13 + 128]
    mov [r15 + VM_ENTRY_RSP], rax
    mov rdx, [rax]
    mov rcx, [r15 + 32]
    mov [rcx], rdx
    mov [r15 + VM_HOST_SP], r11
    mov rax, [r12]
    add rax, r12
    mov [r15 + VM_OPS], rax
    mov eax, [r12 + 8]
    mov [r15 + VM_PC], rax
    mov eax, [r12 + 12]
    mov [r15 + VM_COUNT], rax
    mov rax, [r12 + 16]
    add rax, r12
    mov [r15 + VM_CODEC], rax
    mov qword ptr [r15 + VM_STACK_LEN], 0
vm_context_ready:
    mov rsp, r11
    cld
    mov rdi, r15
    jmp vm_run

vm_native_enter:
    mov rsp, [r15 + VM_HOST_SP]
    push r15
    push qword ptr [r15 + VM_NATIVE_TARGET]
    push qword ptr [r15 + 32]
    mov rax, [r15 + 0]
    mov rcx, [r15 + 8]
    mov rdx, [r15 + 16]
    mov rbx, [r15 + 24]
    mov rbp, [r15 + 40]
    mov rsi, [r15 + 48]
    mov rdi, [r15 + 56]
    mov r8, [r15 + 64]
    mov r9, [r15 + 72]
    mov r10, [r15 + 80]
    mov r11, [r15 + 88]
    mov r12, [r15 + 96]
    mov r13, [r15 + 104]
    mov r14, [r15 + 112]
    push qword ptr [r15 + VM_FLAGS]
    popfq
    mov r15, [r15 + 120]
vm_native_restored:
    jmp qword ptr [rsp + 8]

vm_native_leave:
    mov [r15 + 0], rax
    mov [r15 + 8], rcx
    mov [r15 + 16], rdx
    mov [r15 + 24], rbx
    mov [r15 + 40], rbp
    mov [r15 + 48], rsi
    mov [r15 + 56], rdi
    mov [r15 + 64], r8
    mov [r15 + 72], r9
    mov [r15 + 80], r10
    mov [r15 + 88], r11
    mov [r15 + 96], r12
    mov [r15 + 104], r13
    mov [r15 + 112], r14
    mov rax, [rsp]
    mov [r15 + 120], rax
    mov rax, [rsp + 8]
    mov [r15 + VM_FLAGS], rax
    lea rax, [rsp + 144]
    mov [r15 + 32], rax
    mov qword ptr [r15 + VM_STACK_LEN], 0
    mov rsp, [r15 + VM_HOST_SP]
    cld
    mov rdi, r15
    jmp vm_run

vm_finish:
    mov rsp, [r15 + VM_HOST_SP]
    push qword ptr [r15 + VM_ENTRY_RSP]
    push r15
    push qword ptr [r15 + VM_FLAGS]
    popfq
    mov rax, [r15 + 0]
    mov rcx, [r15 + 8]
    mov rdx, [r15 + 16]
    mov rbx, [r15 + 24]
    mov rbp, [r15 + 40]
    mov rsi, [r15 + 48]
    mov rdi, [r15 + 56]
    mov r8, [r15 + 64]
    mov r9, [r15 + 72]
    mov r10, [r15 + 80]
    mov r11, [r15 + 88]
    mov r12, [r15 + 96]
    mov r13, [r15 + 104]
    mov r14, [r15 + 112]
    mov r15, [r15 + 120]
vm_finish_restored:
    mov rsp, [rsp + 8]
vm_return:
    ret

vm_tail:
    mov rsp, [r15 + VM_HOST_SP]
    push qword ptr [r15 + VM_ENTRY_RSP]
    push r15
    mov rax, [r15 + VM_ENTRY_RSP]
    mov rcx, [r15 + VM_NATIVE_TARGET]
    mov [rax - 8], rcx
    push qword ptr [r15 + VM_FLAGS]
    popfq
    mov rax, [r15 + 0]
    mov rcx, [r15 + 8]
    mov rdx, [r15 + 16]
    mov rbx, [r15 + 24]
    mov rbp, [r15 + 40]
    mov rsi, [r15 + 48]
    mov rdi, [r15 + 56]
    mov r8, [r15 + 64]
    mov r9, [r15 + 72]
    mov r10, [r15 + 80]
    mov r11, [r15 + 88]
    mov r12, [r15 + 96]
    mov r13, [r15 + 104]
    mov r14, [r15 + 112]
    mov r15, [r15 + 120]
vm_tail_restored:
    mov rsp, [rsp + 8]
vm_tail_jump:
    notrack jmp qword ptr [rsp - 8]

vm_abort:
    mov eax, 1
    mov edi, 2
    lea rsi, [rip + vm_error]
    mov edx, vm_error_end - vm_error
    syscall
    mov eax, 231
    mov edi, 126
    syscall
    ud2

vm_error:
    .ascii "elfscatter: VM runtime failure\n"
vm_error_end:
vm_run:
    mov rax, [rdi + VM_CODEC]
    movzx eax, byte ptr [rax + VM_CODEC_VARIANT]
    test eax, eax
    je vm_run_0
    cmp eax, 1
    je vm_run_1
    jmp vm_abort
.section .note.GNU-stack,"",@progbits
