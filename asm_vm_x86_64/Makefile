main: main.rs libvm.a
	rustc -L. -O main.rs

vm.o: vm.s
	gcc -c vm.s
libvm.a: vm.o
	ar -r libvm.a vm.o

.PHONY: clean
clean:
	-rm *.o *.a main
