/* */

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

int parse(uint8_t *buf, uint16_t *offset, uint16_t len, uint8_t p_id){

  if(! (sizeof(uint8_t) <= len - *offset) ) return -1;
  p[p_id].age = (uint8_t) buf[*offset];
  *offset += sizeof(uint8_t);

  if(! (sizeof(uint8_t) <= len - *offset)) return -1;
  p[p_id].children_len = (uint8_t) buf[*offset];
  *offset += sizeof(uint8_t);

  if(! (p[p_id].children_len < MAX_CHILDREN_LEN)) return -1;

  for(uint8_t child_id = 0; child_id < p[p_id].children_len; child_id++){
    if(! (sizeof(uint8_t) <= len - *offset)) return -1;
    p[p_id].children[child_id] = (uint8_t) buf[*offset];

    if(! (p[p_id].children[child_id] < p_id) ) return -1;
    *offset += sizeof(uint8_t);
  };

  return 0;

};

void print_diff_child_age(uint8_t p_id){

  printf("%i(%i) :", p_id,p[p_id].age);

  for(uint8_t i = 0; i < p[p_id].children_len; i++){
    printf(" %i",p[p_id].age - p[p[p_id].children[i]].age);
  }

  printf("\n");

}

uint64_t compute_sum_age(uint8_t p_nb){

  if(p_nb == 0){
    return 0.;
  } else {

    uint8_t sum = 0;

    for(uint8_t p_id = 0; p_id < p_nb; p_id++){
      sum += p[p_id].age;
    }

    printf("sum: %i\n", sum);

    return sum;
  }

}


uint64_t run(uint8_t *buf, uint16_t len){

  uint16_t offset;

  uint8_t p_nb;
  for(p_nb = 0; p_nb < MAX_PERSON_NUMBER; p_nb++){
    int r = parse(buf, &offset, len, p_nb);
    if(r) break;
  }

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
}
