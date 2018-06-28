/*
   ############################################################################

   SPOILER WARNING!

   This file contains the solutions for the Frama-C tutorial.

   DO NOT LOOK INSIDE UNTIL AFTER YOU HAVE TRIED FOR YOURSELF!

   ############################################################################
 */

#include <__fc_builtin.h>
#include <stdint.h>
#include <stdio.h>

#define MAX_CHILDREN_LEN 10
#define MAX_BUF_SIZE 100
#define MAX_PERSON_NUMBER 50

struct person {
  uint8_t age;
  uint8_t children_len;
  uint8_t children[MAX_CHILDREN_LEN];
};

struct person p[MAX_PERSON_NUMBER];

/*@
  predicate valid_person(integer i) =
    p[i].children_len < MAX_CHILDREN_LEN &&
    \forall integer k; 0 <= k < p[i].children_len ==> p[i].children[k] < i;

  predicate valid_p(integer p_nb) =
   \forall integer i; 0 <= i < p_nb ==> valid_person(i);
  @*/

/*@
  ensures \result == 0 ==> valid_person(p_id);
  assigns *offset, \result, p[p_id].age, p[p_id].children_len, p[p_id].children[ 0 .. MAX_CHILDREN_LEN ];
  @*/
int parse(uint8_t *buf, uint16_t *offset, uint16_t len, uint8_t p_id){

  if(! (sizeof(uint8_t) <= len - *offset) ) return -1;
  p[p_id].age = (uint8_t) buf[*offset];
  *offset += sizeof(uint8_t);

  if(! (sizeof(uint8_t) <= len - *offset)) return -1;
  p[p_id].children_len = (uint8_t) buf[*offset];
  *offset += sizeof(uint8_t);

  if(! (p[p_id].children_len < MAX_CHILDREN_LEN)) return -1;

  /*@
    loop invariant \forall integer k; 0 <= k < child_id ==> p[p_id].children[k] < p_id;
    loop assigns child_id, p[p_id].children[ 0 .. MAX_CHILDREN_LEN ], *offset;
    @*/
  for(uint8_t child_id = 0; child_id < p[p_id].children_len; child_id++){
    if(! (sizeof(uint8_t) <= len - *offset)) return -1;
    p[p_id].children[child_id] = (uint8_t) buf[*offset];

    if(! (p[p_id].children[child_id] < p_id) ) return -1;
    *offset += sizeof(uint8_t);
  };

  return 0;

};

/*@
  requires 0 <= p_id < MAX_PERSON_NUMBER;
  requires valid_person(p_id);
  assigns __fc_stdout->__fc_FILE_data;
  @*/
void print_diff_child_age(uint8_t p_id){

  printf("%i(%i) :", p_id,p[p_id].age);
  /*@
    loop assigns i, __fc_stdout->__fc_FILE_data;
    @*/
  for(uint8_t i = 0; i < p[p_id].children_len; i++){
    printf(" %i",p[p_id].age - p[p[p_id].children[i]].age);
  }

  printf("\n");

}

/*@
  axiomatic Sum {
  logic integer sum_age(integer p_nb) reads p[ 0 .. MAX_PERSON_NUMBER ];
  axiom sum_0: sum_age(0) == 0;
  axiom sum_n: \forall integer i; 0 < i ==> sum_age(i) == p[i-1].age + sum_age(i-1);
}
  @*/

/*@
  requires p_nb <= MAX_PERSON_NUMBER;
  ensures \result ==  sum_age(p_nb);
  @*/
uint64_t compute_sum_age(uint8_t p_nb){

  if(p_nb == 0){
    return 0.;
  } else {

    uint64_t sum = 0;

    /*@
      loop invariant sum <= 255 * p_id;
      loop invariant p_id <= p_nb;
      loop invariant sum_age(p_id) == sum;
      loop assigns sum, p_id;
      @*/
    for(uint8_t p_id = 0; p_id < p_nb; p_id++){
      sum += p[p_id].age;
    }

    printf("sum: %i\n", sum);

    return sum;
  }

}


uint64_t run(uint8_t *buf, uint16_t len){

  uint16_t offset = 0;

  uint8_t p_nb;
  /*@
    loop invariant \forall integer i; 0 <= i < p_nb ==> valid_person(i);
    @*/
  for(p_nb = 0; p_nb < MAX_PERSON_NUMBER; p_nb++){
    int r = parse(buf, &offset, len, p_nb);
    if(r) break;
  }

  /*@
    loop assigns p_id, __fc_stdout->__fc_FILE_data;
    @*/
  for(uint8_t p_id = 0; p_id < p_nb; p_id++){
    print_diff_child_age(p_id);
  }

  return compute_sum_age(p_nb);

}

int main(){

  uint8_t buf[MAX_BUF_SIZE];
  uint16_t len = MAX_BUF_SIZE;
  Frama_C_make_unknown((char*)buf,MAX_BUF_SIZE);

  run(buf,len);

  return 0;
};

void test1(){

  uint8_t test[] = { 3, 0, 5, 0, 28, 2, 0, 1 };
  uint16_t len = sizeof(test);

  uint64_t sum = run(test,len);
  /*@ assert p[2].children[1] == 1; @*/
  /*@ assert sum == (3 + 5 + 28); @*/
}

void test2(){

  uint8_t test[] = { 53, 0, 55, 0, 78, 2, 0, 1, 80, 2, 0, 1, 104, 1, 3, 0, 255 };
  uint16_t len = sizeof(test);

  uint64_t sum = run(test,len);
  /*@ assert p[2].children[1] == 1; @*/
  /*@ assert sum == (53 + 55 + 78 + 80 + 104); @*/
}
