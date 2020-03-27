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

CodeGen Terminate Monomorphization N.land.
CodeGen Terminate Monomorphization N.lor.
CodeGen Terminate Monomorphization N.lxor.
CodeGen Terminate Monomorphization N.shiftl.
CodeGen Terminate Monomorphization N.shiftr.
CodeGen Terminate Monomorphization N.succ.
CodeGen Terminate Monomorphization N.testbit.
CodeGen Monomorphization initialize_random_state.
CodeGen Monomorphization next_random_state.

CodeGen GenCFile "mt_generated.c"
        _generate_state_vector
        _initialize_random_state
        _next_random_state.
