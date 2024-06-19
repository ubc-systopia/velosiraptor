

CFILES_LINUX=\
	linux-kernel/linux.c \
	linux-kernel/mm/memory.c \
	linux-kernel/mm/pgtable-generic.c \
	linux-kernel/arch/x86/mm/pgtable.c

INC_LINUX=\
	-Ilinux-kernel/include \
	-Ilinux-kernel/arch/x86/include \
	-Ilinux-kernel/arch/x86/include/uapi

CFILES_BARRELFISH=\
	barrelfish-kernel/barrelfish.c

INC_BARRELFISH=\
	-Ibarrelfish-kernel/include

INV_VELOSIRAPTOR=\
	-Ivelosiraptor
#
CFILES=bench.c $(CFILES_LINUX) $(CFILES_BARRELFISH)
INC=$(INC_LINUX) $(INC_BARRELFISH) $(INV_VELOSIRAPTOR)

bench: $(CFILES)
	gcc -O3 -o bench $(INC) $(CFILES)

clean:
	rm -rf bench

run: bench
	./bench