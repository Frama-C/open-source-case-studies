// Based on MITRE's CWE-787, demonstrative example 4
// https://cwe.mitre.org/data/definitions/787.html

// Option "-eva-precision 1" reduces the number of "Unknown" alarms.
// Run with "-eva-precision 2" to obtain a "Red Alarm".

// Also, adding option "-eva-no-alloc-returns-null" allows focusing on this
// issue while ignoring the the fact that malloc() may fail (which would
// require an extra check).

#include <stdlib.h>
#include <string.h>

#define MAX_SIZE 16

char * copy_input(char *user_supplied_string) {
  int i, dst_index;
  char *dst_buf = (char*)malloc(4*sizeof(char) * MAX_SIZE);
  if ( MAX_SIZE <= strlen(user_supplied_string) ){
    exit(1);
  }
  dst_index = 0;
  for ( i = 0; i < strlen(user_supplied_string); i++ ){
    if( '&' == user_supplied_string[i] ){
      dst_buf[dst_index++] = '&';
      dst_buf[dst_index++] = 'a';
      dst_buf[dst_index++] = 'm';
      dst_buf[dst_index++] = 'p';
      dst_buf[dst_index++] = ';';
    }
    else if ('<' == user_supplied_string[i] ){
      dst_buf[dst_index++] = '&';
      dst_buf[dst_index++] = 'l';
      dst_buf[dst_index++] = 't';
    }
    else dst_buf[dst_index++] = user_supplied_string[i];
  }
  return dst_buf;
}

int main() {
  char *benevolent_string = "<a href='ab&c'>";
  copy_input(benevolent_string);
  char *malicious_string  = "&&&&&&&&&&&&&&&";
  copy_input(malicious_string);
  return 0;
}
