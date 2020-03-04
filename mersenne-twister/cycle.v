From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require irreducible.
Require Import polyn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [fieldType of 'F_2].
Notation p := (n * w - r).
Hypothesis pm : prime (2 ^ p - 1).
Hypothesis mn : m < n.
Hypothesis m0 : 0 < m.
Hypothesis rw : r <= w.
Hypothesis r0 : 0 < r. (* TODO: move to Lemma *)
Hypothesis p3 : p >= 3.

Lemma n2 : 2 <= n.
Proof. by case: n mn m0 => //; case: m => []//[]// ?? + _; apply ltn_trans. Qed.

Lemma n0 : 0 < n.
Proof. by case: n n2. Qed.

Lemma w0 : 0 < w.
Proof. by case: w rw r0 => //; rewrite leqn0 => /eqP ->. Qed.

Lemma rw' : r < w.
Proof. Admitted. (* TODO *)

Lemma rnpw : r <= n.-1 * w.
Proof.
  case: n mn m0 => []//=[|*]; first by case m.
  rewrite mulSn.
  by apply/leq_trans/leq_addr.
Qed.

Lemma tecr : r = r.-1.+1.
Proof. by case: r r0. Qed.

Lemma tecwr : w - r = (w - r).-1.+1.
Proof. by rewrite prednK // /leq subnBA // add1n subn_eq0 rw'. Qed.

Lemma tecw : (w - r).-1.+1 + r.-1.+1 = w.
Proof. by rewrite !prednK // ?subnK // /leq subnBA // add1n subn_eq0 rw'. Qed.

Lemma tecnw : w + (n.-1 * w - r) = p.
Proof. by rewrite addnBA ?rnpw // -mulSn prednK ?n0. Qed.

Lemma tecpr : p + r = n * w.
Proof.
  rewrite subnK //.
  case: n mn => // ??.
  rewrite mulSn.
  by apply/leq_trans/leq_addr.
Qed.

Lemma tecp : p = p.-1.+1.
Proof. by case: p p3. Qed.

Hint Resolve n2 n0 w0 rw' rnpw : core.
Local Open Scope ring_scope.

Definition shiftr : 'M['F_2]_w :=
  \matrix_(i, j) (1 *+ (i == j.+1 :> nat)).

Definition A := \matrix_j (\row_i a`_i *+ (j == w.-1 :> nat)) + shiftr.

Definition S := castmx (etrans (addnC _ _) tecw, tecw)
                (block_mx 0 (castmx (tecr, tecr) 1%:M)
                          (castmx (tecwr, tecwr) 1%:M) 0) *m A.

Definition B :=
  castmx (etrans (addnC _ _) tecnw, tecnw)
  (block_mx (\matrix_(i, j) (1 *+ (i == j - m :> nat)%nat)) 1%:M
             S 0).

Definition pull_ord (o : 'I_p) := cast_ord tecpr (lshift r o).

Definition incomplete_array (x : 'M['F_2]_(n, w)) : 'rV_p :=
  \row_i (mxvec x) ord0 (pull_ord i).

Definition array_incomplete (y : 'rV['F_2]_p) : 'M_(n, w) :=
  vec_mx (castmx (erefl, tecpr) (row_mx y 0)).

Lemma array_incompleteK : cancel array_incomplete incomplete_array.
Proof.
move=> y; rewrite /incomplete_array /array_incomplete; apply/rowP => j.
by rewrite mxE vec_mxK castmxE /pull_ord cast_ordK row_mxEl cast_ord_id.
Qed.

Definition phi := char_poly B.
Lemma size_phi : (size phi).-1 = p.
Proof. by rewrite size_char_poly. Qed.

Lemma X2X : 'X ^ 2 %% phi != 'X %% phi.
Proof.
  rewrite -GRing.subr_eq0 -modp_opp -modp_add.
  apply/negP => /dvdp_leq H.
  have/H: 'X ^ 2 - 'X != 0 :> {poly 'F_2}.
   rewrite GRing.subr_eq0.
   apply/negP => /eqP/(f_equal (size : {poly 'F_2} -> nat)).
   by rewrite size_polyXn size_polyX.
  case: (size phi) size_phi => //= p0 => [|->].
   by move: p0 pm => <-; rewrite expn0 subn1.
  rewrite size_addl ?size_polyXn ?size_opp ?size_polyX //.
  by apply/negP; rewrite -leqNgt.
Qed.

Lemma pm' : prime (2 ^ (size phi).-1 - 1).
Proof. by rewrite size_phi. Qed.

Hint Resolve pm' : core.

Lemma irreducibleP : reflect (irreducible_poly phi)
                             ('X ^ (2 ^ (size phi).-1)%N %% phi == 'X %% phi).
apply/(iffP idP).
* move=> H1; apply/irreducible.irreducibleP => //.
  by rewrite X2X /=.
* by case/irreducible.irreducibleP/andP.
Qed.

(* Lemma cycleB_dvdP q : reflect (horner_mx (castmx (tecp, tecp) B) ('X ^+ q) == 1) *)
(*                               (2 ^ p - 1 %| q)%nat. *)
(* Proof. *)


Check B *m B.
Check powers_mx.
Variable q : nat.


End phi.
Definition w := 32.
Definition r := 1.
Definition n := 4.
Definition m := 1.

Lemma mn : m < n.
  done.
  Qed.
Lemma rw : r < w.
  done.
  Qed.

Compute incomplete_array mn rw 0.
Lemma sizea : size ([:: 1;0;0;1;1;0;0;1;0;0;0;0;1;0;0;0;1;0;1;1;0;0;0;0;1;1;0;1;1;1;1;1] : seq 'F_2)%R == w.
  done.
Qed.

Lemma nm : m < n.
  by [].
Defined.
Lemma pm'': prime (2 ^ (n * w - r) - 1).
Proof.
  Admitted.
Definition B := lin1_mx (@f _ _ _ _ (Tuple sizea) pm'' nm erefl erefl erefl).
Compute B.
Variable j : 'I_(size (phi n m r (Tuple sizea))).-1.
Check lin_mx.
Check lin1_mx.
Lemma BE : B (delta_mx 0%R j) = B (delta_mx 0%R j) .
rewrite /B /f.

rewrite /= /rVnpoly /comp rVpoly_delta.
rewrite /irreducible.mulX /irreducible.mulV.
rewrite /insubd.
      Check row_mx 0.
Check delta_mx

Compute B 0.
