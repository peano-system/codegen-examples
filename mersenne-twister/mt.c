#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include <stdbool.h>
#define n0_true() true
#define n0_false() false
#define sw_bool(b) (b)
#define case_true_bool default
#define case_false_bool case false

#define nat uint64_t
#define n0_O() ((nat)0)
#define n1_S(n) ((n)+1)
#define sw_nat(n) (n)
#define case_O_nat case 0
#define case_S_nat default
#define field0_S_nat(n) ((n)-1)

#define N uint32_t
#define n0_N0() 0
#define n2_land(n1,n2) ((n1)&(n2))
#define n2_lor(n1,n2) ((n1)|(n2))
#define n2_lxor(n1,n2) ((n1)^(n2))
#define n2_shiftl(n1,n2) ((n1)<<(n2))
#define n2_shiftr(n1,n2) ((n1)>>(n2))
#define n2_eqb_0(n1,n2) ((n1)==(n2))
#define n2_testbit(n1,n2) ((n1)&(1<<(n2)))
#define n1_of_nat(n) ((uint32_t)n)

#define positive uint32_t
#define n0_xH() 1
#define n1_xO(n) (2*(n))
#define n1_xI(n) (2*(n)+1)
#define n1_Npos(n) n

#define n2_addn(a,b) ((a)+(b))
#define n2_subn(a,b) ((a)-(b))
#define n2_muln(a,b) ((a)*(b))
#define n2_divn(a,b) ((a)/(b))
#define n2_modulo(a,b) ((a)%(b))
#define n1_succ(n) ((uint32_t)(n) + 1)
#define n1_nat_of_bin(n) ((uint32_t)(n))

#define n2_modulo_0(a,b) ((a)%(b))
#define n2_add_1(a,b) ((a)+(b))
#define n2_sub_0(a,b) ((a)-(b))
#define n2_mul_0(a,b) ((a)*(b))
#define n2_div_0(a,b) ((a)/(b))

#define n0_len() 624
#define n0_m() 397
#define n0_r() 31
#define n0_u() 11
#define n0_s() 7
#define n0_t() 15
#define n0_l() 18
#define n0_a() 2567483615
#define n0_b() 2636928640
#define n0_c() 4022730752

#define n0_upper_mask() 2147483648
#define n0_whole_mask() (n0_upper_mask() * 2 - 1)
#define n0_lower_mask() (n0_upper_mask() - 1)

struct list_n {
  N list[n0_len()];
  int index;
};

#define list_N struct list_n

#define n0_nil_N() {{},0}
list_N n2_cons_N(N value, list_N l) {
  l.list[l.index] = value;
  ++(l.index);
  return l;
}

N n2_head_N(N default_value, list_N l) {
  return l.list[l.index-1];
}

N n3_nth_N(N default_value, list_N l, nat index) {
  return l.list[index];
}

list_N n4_set_nth_N(N default_value, list_N l, nat index, N value) {
  l.list[index] = value;
  return l;
}

void swap(list_N l, nat n1, nat n2) {
  N temp = l.list[n1];
  l.list[n1] = l.list[n2];
  l.list[n2] = temp;
}

list_N n1_rev_N(list_N l) {
  for (nat i = 0; i < n0_len(); ++i) {
    swap(l, i, n0_len()-i-1);
  }
  return l;
}

struct rand_state {
  nat index;
  list_N state_vector;
};

#define random_state struct rand_state

random_state n2_Build_random_state(nat index, list_N list) {
  random_state r = {index,list};
  return r;
}

nat n1_index(random_state rand) {
  return rand.index;
}

list_N n1_state_vector(random_state rand) {
  return rand.state_vector;
}

struct prod_n_random_state {
  N n;
  random_state r;
};

#define prod_N_random_state struct prod_n_random_state

prod_N_random_state n2_pair_N_random_state(N n, random_state r) {
  prod_N_random_state x = {n,r};
  return x;
}

#define field0_pair_prod_N_random_state(p) (p).n
#define field1_pair_prod_N_random_state(p) (p).r

#include "mt_generated.c"

int main(void) {
  int seed = 20190820;
  random_state r = n1_initialize_random_state(seed);
  int i;
  for (i = 0; i < 2048; ++i) {
    prod_N_random_state p = n1_next_random_state(r);
    printf("%d:%u\n", i, field0_pair_prod_N_random_state(p));
    r = field1_pair_prod_N_random_state(p);
  }
  return 0;
}
