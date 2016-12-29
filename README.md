# Compiler project
* This is an implementation of a 'Java like' compiler using language C, bison and flex
* The file of subject is in the folder named subject

### Installation ### 
* `git clone git@github.com:suesunSS/compiler.git nameOfProject`
* `cd nameOfProject` 
* `cd src`
* `make tp`
 * `tp` is just name of the project, don't be interwined by it.
* Using `./tp [-c] [-e] [-o] [output.txt] programName.txt` to compile the program
 * The option `-c` is the trigger to execute the phase of context verification. If we add this option, the compilation process will avoid this phase
 * The option `-e` is the trigger to execute the phase of code generation. Same as `-c`
 * The option `-o` is used to define the name of the output of the code generation, here `code.txt` for example
* Using `./interp code.txt` to execute the program

### Test ### 
* In the `src/test` directory, there are some test samples for the context verification phase and code generation phase

### Versions of dependencies### 
* OS: ubuntu 14.04
* gcc: gcc (Ubuntu 4.8.4-2ubuntu1~14.04.3) 4.8.4
* bison: bison (GNU Bison) 3.0.2
* flex: flex 2.5.35

### PS ### 
* The comments of the code are in French. Will be fixed later.  