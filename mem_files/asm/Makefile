ASM := $(wildcard *.asm)
BASE := $(ASM:.asm=)

assemble:
	riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 $< -o $*.o
	riscv64-unknown-elf-objcopy -O binary -j .text --pad-to=0x400 $*.o $*.hex
	xxd -g 1 -c 4 -p $*.hex | sed 's/../& /g' > $*.mem
