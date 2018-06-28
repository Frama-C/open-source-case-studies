// Some definition for compiling the annotated program

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

int stdin_finished = 0;

// read source from stdin, complete with 0
void Frama_C_make_unknown(char *dest, size_t n){
  size_t i = 0;

  size_t r = 1;
  while(r != 0){
    r = read(0,dest,n-i);
    i += r;
  };
  printf("i=%li\n",i);
  for ( ; i < n; i++)
    dest[i] = '\0';

}

int printf_va_1(char const *format, int param0, int param1){
  return printf(format,param0,param1);
}
int printf_va_2(char const *format, int param0){
  return printf(format,param0);
}
int printf_va_3(char const *format){
  return printf("%s",format);
}
int printf_va_4(char const *format, int param0){
  return printf(format,param0);
}
