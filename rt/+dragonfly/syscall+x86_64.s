.section .text.rt.syscall0
.global rt.syscall0
rt.syscall0:
	movq %rdi, %rax
	syscall
	ret

.section .text.rt.syscall1
.global rt.syscall1
rt.syscall1:
	movq %rdi, %rax
	movq %rsi, %rdi
	syscall
	ret

.section .text.rt.syscall2
.global rt.syscall2
rt.syscall2:
	movq %rdi, %rax
	movq %rsi, %rdi
	movq %rdx, %rsi
	syscall
	ret

.section .text.rt.syscall3
.global rt.syscall3
rt.syscall3:
	movq %rdi, %rax
	movq %rsi, %rdi
	movq %rdx, %rsi
	movq %rcx, %rdx
	syscall
	ret

.section .text.rt.syscall4
.global rt.syscall4
rt.syscall4:
	movq %rdi, %rax
	movq %r8, %r10
	movq %rsi, %rdi
	movq %rdx, %rsi
	movq %rcx, %rdx
	syscall
	ret

.section .text.rt.syscall5
.global rt.syscall5
rt.syscall5:
	movq %rdi, %rax
	movq %r8, %r10
	movq %rsi, %rdi
	movq %r9, %r8
	movq %rdx, %rsi
	movq %rcx, %rdx
	syscall
	ret

.section .text.rt.syscall6
.global rt.syscall6
rt.syscall6:
	movq %rdi, %rax
	movq %r8, %r10
	movq %rsi, %rdi
	movq %r9, %r8
	movq %rdx, %rsi
	movq 8(%rsp), %r9
	movq %rcx, %rdx
	syscall
	ret

.section .text.rt._mmap
.global rt._mmap
rt._mmap:
	// DragonFly BSD uses 7 arguments for mmap syscall
	//
 	//   rax: 197 (SYS_mmap)
	//   rdi: addr
	//   rsi: length
	//   rdx: prot
	//   r10: flags
	//   r8:  fd
	//   r9:  pad (0)
	//   on stack: offs

	// Move flags to r10
	movq %rcx, %r10

	// Put offs on stack
	sub $16, %rsp
	mov %r9, 8(%rsp)

	// Zero pad
	mov $0, %r9

	// SYS_mmap
	mov $197, %rax

	syscall

	add $16, %rsp
	ret

.section .text.rt._pipe2
.global rt._pipe2
rt._pipe2:
	// SYS_pipe2
	mov $538, %rax
	syscall
	jb pipe2err
	// %rdi is preserved by syscall
	movl	%eax,0(%rdi)
	movl	%edx,4(%rdi)
	movq	$0,%rax
	ret
pipe2err:
	movl $-1, 0(%rdi)
	movl $-1, 4(%rdi)
	ret

