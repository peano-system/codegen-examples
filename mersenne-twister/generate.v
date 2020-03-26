From codegen Require Import codegen.
From mathcomp Require Import all_ssreflect.
Require Import BinNat.
Require mt.

Open Scope N_scope.

Definition len := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Definition m := 397. (* 'm' in  tgfsr3.pdf, p.4 *)
Definition r := 31.
Definition a := 2567483615.

Definition u := 11.
Definition s := 7.
Definition t := 15.
Definition l := 18.
Definition b := 2636928640.
Definition c := 4022730752.

Definition next_random_state := Eval hnf in mt.next_random_state len m r a.
Definition tempering := Eval hnf in mt.tempering u s t l b c.
Definition whole_mask := Eval compute in (2 ^ r) * 2 - 1.

Fixpoint generate_state_vector (rest : nat) (acc : seq N) : seq N :=
  match rest with
  | 0%nat => acc
  | 1%nat => acc
  | S rest' => generate_state_vector rest' ((N.land (1812433253 * (N.lxor (head 0 acc) (N.shiftr (head 0 acc) 30)) + N.of_nat(len - rest) + 1) whole_mask) :: acc)
  end.

Definition initialize_random_state (seed : N) : mt.random_state :=
  mt.Build_random_state 0 (rev (generate_state_vector len (N.land seed whole_mask :: nil))).

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Snippet "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen Inductive Type nat => "nat".
CodeGen Inductive Match nat => ""
| O => "case 0"
| S => "default" "nat_pred".
CodeGen Constant O => "(nat)0".
CodeGen Primitive S => "nat_succ".

CodeGen Snippet "
#include <stdint.h>
typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)
".

CodeGen Inductive Type positive => "uint32_t".
CodeGen Inductive Type N => "N".
CodeGen Inductive Match N => ""
| N0 => "case 0"
| Npos => "default" "".
CodeGen Constant N0 => "0".
CodeGen Constant xH => "1".
CodeGen Primitive xO => "n1_xO".
CodeGen Primitive xI => "n1_xI".
CodeGen Primitive Npos => "n1_pos".

CodeGen Snippet "
typedef uint32_t N;
#define n1_xO(n) (2*(n))
#define n1_xI(n) (2*(n)+1)
#define n1_pos(n) (n)
".

CodeGen Primitive N.land => "n2_land".
CodeGen Primitive N.lor => "n2_lor".
CodeGen Primitive N.lxor => "n2_lxor".
CodeGen Primitive N.shiftl => "n2_shiftl".
CodeGen Primitive N.shiftr => "n2_shiftr".
CodeGen Primitive N.testbit => "n2_testbit".
CodeGen Primitive N.succ => "n1_succ".

CodeGen Snippet "
#define n2_land(n1,n2) ((n1)&(n2))
#define n2_lor(n1,n2) ((n1)|(n2))
#define n2_lxor(n1,n2) ((n1)^(n2))
#define n2_shiftl(n1,n2) ((n1)<<(n2))
#define n2_shiftr(n1,n2) ((n1)>>(n2))
#define n2_testbit(n1,n2) ((n1)&(1<<(n2)))
#define n1_succ(n1) ((n1) + 1)
".

CodeGen Constant len => "624".
CodeGen Constant m => "397".
CodeGen Constant r => "31".
CodeGen Constant a => "2567483615".
CodeGen Constant whole_mask => "4294967295".

CodeGen Inductive Type (seq N) => "list_n".
CodeGen Primitive nil => "n0_nil_N".
CodeGen Primitive head => "n2_head_N".
CodeGen Primitive nth => "n3_nth_N".
CodeGen Primitive set_nth => "n4_set_nth_N".
CodeGen Primitive rev => "n1_rev_N".

CodeGen Snippet "
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
".

CodeGen Inductive Type mt.random_state => "rand_state".
CodeGen Primitive mt.Build_random_state => "n2_Build_random_state".
CodeGen Primitive mt.index => "n1_index".
CodeGen Primitive mt.state_vector => "n1_state_vector".
CodeGen Snippet "
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
".

CodeGen Inductive Type (N * mt.random_state) => "prod_n_random_state".
CodeGen Primitive pair => "n2_pair_N_random_state".
CodeGen Primitive fst => "field0_pair_prod_N_random_state".
CodeGen Primitive snd => "field1_pair_prod_N_random_state".
CodeGen Snippet "
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
".

CodeGen Function next_random_state.
CodeGen Function initialize_random_state.
CodeGen GenerateFile "mt_generated.c".
