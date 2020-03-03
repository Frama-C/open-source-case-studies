// Based on MITRE's CWE-119, demonstrative example 1
// https://cwe.mitre.org/data/definitions/119.html

// Run with "-eva-precision 1" to obtain a "Red Alarm".

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <netdb.h>

// To use Frama-C's "Frama_C_interval" to generate a nondeterministic value
#include "__fc_builtin.h"

static void validate_addr_form(char *v) {
  // naive, simplistic validation
  if (strspn(v, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-0123456789.") < strlen(v)) {
    fprintf(stderr, "hostname contains invalid characters");
    exit(1);
  }
}

static int my_strcmp(const char *s1, const char *s2)
{
  size_t i;
  for (i = 0; s1[i] == s2[i]; i++) {
    if (s1[i] == 0) return 0;
  }
  return (((unsigned char *)s1)[i] - ((unsigned char *)s2)[i]);
}

// simplified version
static in_addr_t my_inet_addr(const char *cp) {
  if (my_strcmp(cp, "127.0.0.1") == 0) {
    return 0;
  } else {
    return Frama_C_nondet(1,UINT_MAX);
  }
}

// simplified version
static struct hostent *my_gethostbyaddr(const void *addr,
                                     socklen_t len, int type) {
  static struct hostent res;
  // actual lookup code omitted
  if ((in_addr_t*)addr == 0) {
    res.h_name = "www.example.com";
  } else {
    res.h_name = "hypermegagigaterasupercalifragilisticexpialidocious2.example.com";
  }
  return &res;
}

void host_lookup(char *user_supplied_addr){
  struct hostent *hp;
  in_addr_t *addr;
  char hostname[64];

  /* routine that ensures user_supplied_addr is in the right format for conversion */
  validate_addr_form(user_supplied_addr);
  addr = my_inet_addr(user_supplied_addr);
  hp = my_gethostbyaddr(addr, sizeof(struct in_addr), AF_INET);
  strcpy(hostname, hp->h_name);
}

int main() {
  char *very_large_but_valid_hostname = "127.0.0.1";
  host_lookup(very_large_but_valid_hostname);
  char *overly_large_hostname = "127.0.0.2";
  host_lookup(overly_large_hostname);
  return 0;
}
