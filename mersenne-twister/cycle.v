From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.
Require irreducible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mulBE.
Local Open Scope ring_scope.
Variable w r : nat.
Variable R : ringType.
Variable ul : 'M[R]_(r, w).
Variable dl : 'M[R]_(w, w).
Local Notation B := (castmx (erefl, addnC _ _) (block_mx ul 1%:M dl 0)).
Lemma mulBE_hidden (x : 'rV[R]_(r + w)) :
  x *m B = castmx (erefl, addnC _ _)
                  (row_mx (lsubmx x *m ul + rsubmx x *m dl) (lsubmx x)).
Proof.
apply/rowP => i; rewrite ?(castmxE, mxE).
apply/etrans; first by apply/eq_bigr => j _; rewrite castmxE block_mxEh mxE.
set T := cast_ord _ i; case: (splitP T) => j Tj.
+ rewrite ?(castmxE, mxE) big_split_ord /=.
  congr (_ + _); apply/eq_bigr => k _;
  rewrite ?(castmxE, mxE) !cast_ord_id.
  - case: (splitP (lshift w k)) => j0 wkj0.
    * congr (_ * ul _ _).
      apply/ord_inj.
      by rewrite -wkj0.
    * case: k wkj0 => k /= i0 krj0.
      suff: false by []; move: i0.
      by rewrite krj0 ltnNge leq_addr.
  - case: (splitP (rshift r k)) => j0 wkj0.
    * case: j0 wkj0 => j0 /= i0 rkj0.
      suff: false by []; move: i0.
      by rewrite -rkj0 ltnNge leq_addr.
    * congr (_ * dl _ _).
      apply/ord_inj; move/eqP: wkj0.
      by rewrite /= eqn_add2l eq_sym => /eqP.
+ rewrite ?(castmxE, mxE) [in RHS](matrix_sum_delta x) summxE big_ord1
          summxE !big_split_ord /= !cast_ord_id.
  congr (_ + _); apply/eq_bigr => k _.
  * by rewrite cast_ord_id col_mxEu !mxE !eqE /= eq_sym.
  * rewrite cast_ord_id col_mxEd !mxE !eqE /=.
    case jrk: (val j == r + k)%N => //.
    case: j jrk {Tj} => j + /= /eqP jrk.
    by rewrite jrk ltnNge leq_addr.
Qed.
End mulBE.
Section mulAE.
Local Open Scope ring_scope.
Variable w r : nat.
Variable dl : 'F_2.
Variable dr : 'rV['F_2]_r.
Local Notation A :=
  (castmx (addn1 _, etrans (addnC _ _) (addn1 _)) (block_mx 0 1%:M dl%:M dr)).

Lemma Aul (i1 : 'I_r) : A (widen_ord (leqnSn r) i1) ord0 = 0.
Proof.
  rewrite ?(castmxE, mxE).
  set T := cast_ord _ _.
  case: (splitP T) => k Tk.
  + set S := cast_ord _ _.
    by rewrite mxE; case: (splitP S) => l Sl; rewrite mxE.
  + case: k Tk => [][]//= ?.
    rewrite addn0 => i1r.
    suff: (r < r)%nat by rewrite ltnn.
    by rewrite -[X in (X < _)%nat]i1r.
Qed.

Lemma Adr (j : 'I_r) : A ord_max (lift ord0 j) = dr ord0 j.
Proof.
  rewrite ?(castmxE, mxE).
  set T := cast_ord _ _.
  case: (splitP T) => k /= Tk.
  + suff: (r < r)%nat by rewrite ltnn.
    by rewrite [X in (X < _)%nat]Tk.
  + rewrite mxE.
    set S := cast_ord _ _.
    case: (splitP S) => l /= Sl.
     by case: l Sl => [][].
    congr (dr _ _); apply/ord_inj; first by case: k Tk => [][].
    by move: Sl; rewrite /bump /= !add1n; case.
Qed.

Lemma Aur i0 j :
  A (widen_ord (leqnSn r) i0) (lift ord0 j) = if i0 == j then 1 else 0.
Proof.
  rewrite castmxE mxE.
  set T := cast_ord _ _.
  case: (splitP T) => k /= Tk; last first.
   case: k Tk => [][]//= ?; rewrite addn0 => Tk.
   suff: (r < r)%nat by rewrite ltnn.
   by rewrite -[X in (X < _)%nat]Tk.
  rewrite mxE.
  set S := cast_ord _ _.
  case: (splitP S) => l /= Sl.
   by case: l Sl => [][].
  rewrite /bump /= !add1n in Sl.
  rewrite mxE !eqE /= -Tk; case: Sl => ->.
  by case: ifP.
Qed.

Lemma mulAE_hidden (x : 'rV['F_2]_(r.+1)) :
  x *m A =
  row_mx 0 (\row_i x ord0 (widen_ord (leqnSn r) i)) + (row_mx dl%:M dr) *+ (x ord0 ord_max == 1%R).
Proof.
apply/rowP => i; rewrite ?(castmxE, mxE).
case x00: (x ord0 ord_max == 1); rewrite !mxE.
- case: (@splitP 1 r i) => j /= ij.
  * case: j ij => [][]//= ? i0.
    rewrite !mxE GRing.add0r eqE /= -GRing.mulr_natr GRing.mulr1.
    have->: i = ord0 by apply/ord_inj.
    rewrite big_ord_recr /= (eqP x00) GRing.mul1r castmxE mxE.
    set T := cast_ord _ _.
    case: (splitP T) => k Tk.
     suff: (r < r)%nat by rewrite ltnn.
     by move: Tk => /= Tk; rewrite [X in (X < _)%nat]Tk.
    set S := cast_ord _ _.
    rewrite !mxE; case: (splitP S) => l Sl; last by rewrite /= add1n in Sl.
    case: k l {Tk Sl} => [][]//?[][]//? /=.
    rewrite mxE eqE /= -GRing.mulr_natr GRing.mulr1 -[RHS]GRing.add0r.
    congr (_ + _).
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aul GRing.mulr0.
    rewrite /= big_const_ord.
    by elim: r => // r' IHr; rewrite iterS IHr GRing.addr0.
  * rewrite mxE big_ord_recr /=.
    have->: i = lift ord0 j by apply/ord_inj; rewrite ij.
    rewrite Adr (eqP x00) GRing.mul1r; congr (_ + _).
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aur.
    rewrite [in RHS](matrix_sum_delta x) summxE big_ord1 summxE
            /= [in RHS]big_ord_recr /= !mxE -[LHS]GRing.addr0.
    congr (_ + _).
    apply eq_bigr => i0 _;
     first by rewrite !mxE eqxx /= !eqE /= eq_sym; case: ifP.
    rewrite !eqE /=; case jr: (j == r :> nat)%nat; last by rewrite GRing.mulr0.
    move/eqP: jr => jr; suff: (r < r)%nat by rewrite ltnn.
    by rewrite -[X in (X < _)%nat]jr.
- have x00': (x ord0 ord_max == 0) by case: (x ord0 ord_max) x00 => [][|[]//].
  case: (@splitP 1 r i) => j /= ij.
  * case: j ij => [][]//= ? i0.
    have->: i = ord0 by apply/ord_inj.
    rewrite big_ord_recr /= (eqP x00') GRing.mul0r GRing.addr0.
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aul GRing.mulr0.
    rewrite /= mxE big_const_ord GRing.addr0.
    by elim: r => // r' IHr; rewrite iterS IHr GRing.addr0.
  * rewrite mxE big_ord_recr /=.
    have->: i = lift ord0 j by apply/ord_inj; rewrite ij.
    rewrite Adr (eqP x00') GRing.mul0r GRing.addr0.
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aur.
    rewrite [in RHS](matrix_sum_delta x) summxE big_ord1 summxE
            /= [in RHS]big_ord_recr /= !mxE GRing.addr0 -[LHS]GRing.addr0.
    congr (_ + _).
    apply eq_bigr => i0 _;
     first by rewrite !mxE eqxx /= !eqE /= eq_sym; case: ifP.
    rewrite !eqE /=; case jr: (j == r :> nat)%nat; last by rewrite GRing.mulr0.
    move/eqP: jr => jr; suff: (r < r)%nat by rewrite ltnn.
    by rewrite -[X in (X < _)%nat]jr.
Qed.
End mulAE.

Section Main.
Variables w n m r : nat.
Variable a : w.-tuple [fieldType of 'F_2].
Notation p := (n * w - r).
Hypothesis pm : prime (2 ^ p - 1).
Hypothesis mn : m.+1 < n.-2.
Hypothesis m0 : 0 < m.
Hypothesis r0 : 0 < r.
Hypothesis rw : r < w.
Hypothesis p3 : 3 <= p.

Lemma n2 : 2 < n.
Proof. by case: n mn m0 => []//[]//[]//. Qed.

Lemma n2' : 2 <= n.
Proof. by apply: ltnW n2. Qed.

Lemma mn' : m < n.
Proof.
  case: n mn => []//[]//[]// n'.
  rewrite /= ltnS => H.
  apply/(leq_trans H).
  by rewrite leqW // leqW //.
Qed.

Lemma n0 : 0 < n.
Proof. by case: n n2. Qed.

Lemma p0 : 0 < p.
Proof. by case: p p3. Qed.

Lemma w0 : 0 < w.
Proof. by case: w rw r0 => //; rewrite leqn0 => /eqP ->. Qed.

Lemma rw' : r <= w.
by apply/ltnW.
Qed.

Lemma rnpw : r <= n.-1 * w.
Proof.
  case: n mn' m0 => []//=[|*]; first by case m.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw'.
Qed.

Lemma rnmw : r <= (n - m) * w.
Proof.
case: n mn' => // n' ?.
by rewrite subSn // mulSn; apply/leq_trans/leq_addr/ltnW.
Qed.

Lemma rnppw : r <= n.-2 * w.
Proof.
  case: n n2 => []//[]//[]// n0 _.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw'.
Qed.

Lemma wnpwr : w <= n.-1 * w - r.
Proof.
  case: n n2 rnppw => []//[]//[]// n0 _ ?.
  by rewrite mulSn -addnBA // leq_addr.
Qed.

Lemma tecr : r = r.-1.+1.
Proof. by case: r r0. Qed.

Lemma tecwr : w - r = (w - r).-1.+1.
Proof. by rewrite prednK // /leq subnBA ?rw' // add1n subn_eq0 rw. Qed.

Lemma tecw : (w - r).-1.+1 + r.-1.+1 = w.
Proof.
by rewrite !prednK // ?subnK ?rw' // /leq subnBA ?rw' // add1n subn_eq0 rw.
Qed.

Lemma twist : r + (w - r) = w.
Proof. by rewrite subnKC // ltnW. Qed.

Lemma tecw' : w.-1.+1 = w.
Proof. by case: w w0. Qed.

Lemma tecw'' : 1 + w.-1 = w.
Proof. by case: w w0. Qed.

Lemma rnwp : r <= n * w.-1.
Proof.
  case: n mn' m0 => []//=[|*]; first by case m.
  move: rw => rw''.
  rewrite -tecw' ltnS in rw''.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw''.
Qed.

Lemma tecnw : w + (n.-1 * w - r) = p.
Proof. by rewrite addnBA ?rnpw // -mulSn prednK ?n0. Qed.

Lemma choose_m : m.-1 * w + w + ((n - m) * w - r) = p.
Proof.
by rewrite addnC addnA addnC addnCA -mulSn addnC addnBA
           ?rnmw // -mulnDl prednK // addnC subnK // ltnW ?mn'.
Qed.

Lemma choose_last : (n.-1 * w - r) + w = p.
Proof. by rewrite addnC tecnw. Qed.

Lemma tecpr : p + r = n * w.
Proof.
  rewrite subnK //.
  case: n mn' => // ??.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/ltnW.
Qed.

Lemma tecp : p = p.-1.+1.
Proof. by case: p p3. Qed.

Lemma tecn : n = n.-2.+2.
Proof. by case: n n2' => []//[]. Qed.

Lemma wrpwr : (w - r).-1 < w - r.
Proof.
  by rewrite /leq prednK ?subnn // ltnNge /leq subn0 subn_eq0 -ltnNge.
Qed.

Lemma wrw : (w - r) < w.
Proof.
  rewrite /leq -subSn; last by apply/ltnW.
  by rewrite subnAC subSn // subnn subn_eq0.
Qed.

Lemma wrp : (w - r) < p.
Proof.
  apply/(leq_trans wrw).
  by rewrite -choose_last leq_addl.
Qed.

Lemma wr0 : 0 < w - r.
Proof. by case: (w - r) wrpwr. Qed.

Lemma pwn : p %/ w < n.
Proof.
  rewrite divnMBl ?w0 //.
  case wr: (w %| r).
   case/dvdnP: wr => [][|p rpw].
    rewrite mul0n => rn0.
    by move: rn0 r0 => ->.
   move: rpw rw => ->.
   rewrite mulSn => /(leq_ltn_trans (leq_addr _ _)).
   by rewrite ltnn.
  rewrite subn1 divn_small // subn0.
  by case: n n0.
Qed.

Hint Resolve p0 n2' n0 w0 rw' rnwp rnpw rnmw wnpwr mn' wr0 : core.
Local Open Scope ring_scope.

Definition A :=
  castmx (tecw', tecw')
  (castmx (addn1 _, etrans (addnC _ w.-1) (addn1 _))
  (block_mx 0 1%:M (nth 0 a 0)%:M (\row_i nth 0 a i.+1))).

Definition S :=
  castmx (etrans (addnC _ _) tecw, tecw)
  (block_mx 0                             (castmx (tecr, tecr) 1%:M)
            (castmx (tecwr, tecwr) 1%:M)                          0) *m A.

Definition UL : 'M['F_2]_(n.-1 * w - r, w) :=
\matrix_(i, j) (1 *+ ((j == i - (m.-1 * w) :> nat) && (i >= (m.-1 * w)))%nat).

Definition B :=
  castmx (etrans (addnC _ _) tecnw, tecnw)
 (block_mx  UL 1%:M
            S  0).

Definition phi := char_poly (castmx (tecp, tecp) B).
Lemma size_phi : (size phi).-1 = p.
Proof. by rewrite size_char_poly prednK. Qed.

Lemma X2X : 'X ^ 2 %% phi != 'X %% phi.
Proof.
  rewrite -GRing.subr_eq0 -modp_opp -modp_add.
  apply/negP => /dvdp_leq H.
  have/H: 'X ^ 2 - 'X != 0 :> {poly 'F_2}.
   rewrite GRing.subr_eq0.
   apply/negP => /eqP/(f_equal (size : {poly 'F_2} -> nat)).
   by rewrite size_polyXn size_polyX.
  case: (size phi) size_phi => //= p0' => [|->].
   by move: p0' pm => <-; rewrite expn0 subn1.
  rewrite size_addl ?size_polyXn ?size_opp ?size_polyX //.
  by apply/negP; rewrite -leqNgt.
Qed.

Lemma pm' : prime (2 ^ (size phi).-1 - 1).
Proof. by rewrite size_phi. Qed.

Hint Resolve pm' : core.

Lemma irreducibleP : reflect (irreducible_poly phi)
                             ('X ^ (2 ^ (size phi).-1)%N %% phi == 'X %% phi).
Proof.
apply/(iffP idP).
* move=> H1; apply/irreducible.irreducibleP => //.
  by rewrite X2X /=.
* by case/irreducible.irreducibleP/andP.
Qed.

Lemma phi_mxminpoly :
  irreducible_poly phi ->
  phi = mxminpoly (castmx (tecp, tecp) B).
Proof.
 case => ? H0.
 move/H0: (mxminpoly_dvd_char (castmx (tecp, tecp) B)).
 rewrite size_mxminpoly eqSS -lt0n mxminpoly_nonconstant => /implyP /= ?.
 apply/esym/eqP.
 by rewrite -eqp_monic ?char_poly_monic ?mxminpoly_monic.
Qed.

Local Open Scope quotient_scope.

Lemma cycleB_dvdP :
  irreducible_poly phi ->
  forall q, (castmx (tecp, tecp) B ^+ (2 ^ q) == castmx (tecp, tecp) B)
        = (2 ^ (size phi).-1 - 1 %| 2 ^ q - 1)%nat.
Proof.
  move=> H q.
  apply/eqP; case: ifP => H0.
  * rewrite -(horner_mx_X (castmx _ _)) -GRing.rmorphX
            (divp_eq 'X^(2 ^ q) phi) GRing.rmorphD
            GRing.rmorphM /= Cayley_Hamilton GRing.mulr0 GRing.add0r.
    move/(irreducible.cycleF_dvdP pm' H q)/(_ (\pi 'X)) : H0.
    rewrite irreducible.expXpE -GRing.rmorphX => /eqP.
    rewrite exprnP -irreducible.XnE => /eqP ->.
    by rewrite modp_small // size_polyX size_char_poly prednK ltnW // ltnW.
  * move=> H1.
    suff: (2 ^ (size phi).-1 - 1 %| 2 ^ q - 1)%N by rewrite H0.
    rewrite -(horner_mx_X (castmx _ _)) -GRing.rmorphX /= in H1.
    move/(f_equal (mx_inv_horner (castmx (tecp, tecp) B))): H1.
    rewrite !horner_mxK -!phi_mxminpoly // => H1.
    by apply/(irreducible.cycleF_dvdP pm' H q)/irreducible.expandF/eqP.
Qed.

Lemma size_ord_enum q : size (ord_enum q) = q.
Proof. by rewrite -(size_map val) val_ord_enum size_iota. Qed.

Lemma nth_ord_enum i (q : nat) k : (i < q)%nat -> val (nth k (ord_enum q) i) = i.
Proof.
move=> iq.
by rewrite -(nth_map k (val k) val) ?val_ord_enum ?nth_iota // size_ord_enum.
Qed.

Lemma eq_big_cond (T : ringType) p q (pq : p = q) (F1 : 'I_p -> T)
  (F2 : 'I_q -> T) (F12 : forall i, F1 (cast_ord (esym pq) i) = F2 i) :
  \sum_(j < p) F1 j = \sum_(i < q) F2 i.
Proof.
case p0: (p > 0)%nat; last first.
 case: p p0 pq F1 F2 F12 => //= _.
 case: q => // *.
 by rewrite !big_ord0.
have dq: 'I_q.
 rewrite -pq.
 case: p p0 {F1 F12 pq} => // *.
 by apply ord0.
apply/etrans; last first.
 apply congr_big => [|//|i _]; last by rewrite -F12.
 apply: (_ : map (cast_ord pq) (index_enum (ordinal_finType p)) = _).
  apply/eq_from_nth.
  by rewrite size_map /index_enum !unlock /= -!(size_map val) !val_ord_enum !size_iota.
 rewrite size_map /index_enum !unlock /= size_ord_enum => i Hi.
 apply: (_ : nth dq [seq cast_ord pq i | i <- ord_enum p] i = nth dq (ord_enum q) i).
 apply/val_inj.
 rewrite (nth_map (cast_ord (esym pq) dq)); last by rewrite size_ord_enum.
 rewrite /= !nth_ord_enum //; last by rewrite -pq.
rewrite big_map; apply eq_bigr => i _.
by rewrite -F12; congr (F1 _); apply/val_inj.
Qed.

Lemma mulBE_hidden' (x : 'rV['F_2]_p) :
let x' := castmx (erefl, etrans (esym tecnw) (addnC _ _)) x in
x *m B = castmx (erefl, tecnw)
        (row_mx (lsubmx x' *m UL + rsubmx x' *m S) (lsubmx x')).
Proof.
move=> x'.
apply: (can_inj (castmxK (esym erefl) (esym tecnw))).
apply: (can_inj (castmxK erefl (addnC w (n.-1 * w - r)%N))).
rewrite !castmxK -mulBE_hidden castmx_comp /=; subst x'.
apply: (can_inj (castmxK (esym erefl) (esym (etrans (esym tecnw) (addnC w _))))).
rewrite castmxK; apply/rowP => k.
rewrite ?(mxE, castmxE).
apply/etrans; last first.
 apply eq_bigr => j _.
 by rewrite !castmxE !cast_ord_id !esymK.
apply: eq_big_cond => [|? i].
 by rewrite addnC tecnw.
congr (_ * _); first by congr (x 0 _); apply/val_inj.
rewrite castmxE //=.
by congr (block_mx _ _ _ _ _ _); apply/val_inj.
Qed.

Lemma mulSE (x : 'rV['F_2]_(n.-1 * w - r + w)) :
  let x' := castmx (erefl, esym tecw')
            (rsubmx x *m castmx (etrans (addnC _ _) tecw, tecw)
                         (block_mx 0 (castmx (tecr, tecr) 1%:M)
                                   (castmx (tecwr, tecwr) 1%:M) 0)) in
  rsubmx x *m S = castmx (erefl, tecw')
  (row_mx 0 (\row_i x' ord0 (widen_ord (leqnSn w.-1) i))
             + row_mx a`_0%:M (\row_i a`_i.+1) *+ (x' ord0 ord_max == 1)).
Proof.
  move=> x'; rewrite mulmxA -mulAE_hidden.
  apply/rowP => k; rewrite ?(mxE, castmxE).
  apply: eq_big_cond => [|? i]; first by rewrite prednK.
  rewrite ?(mxE, castmxE).
  congr (_ * _).
  apply/eq_bigr => j _.
  congr (rsubmx x _ _ * _); first by apply/val_inj.
  by rewrite !castmxE; congr (block_mx _ _ _ _ _ _); apply/val_inj.
  set I := cast_ord _ _; set I' := cast_ord (esym _) i.
  by have->: I = I' by apply/val_inj.
Qed.

Definition z (x : 'rV['F_2]_p) :=
  rsubmx (castmx (erefl _, etrans (esym tecnw) (addnC _ _)) x) *m
  castmx (etrans (addnC _ _) tecw, tecw)
 (block_mx 0 (castmx (tecr, tecr) 1%:M) (castmx (tecwr, tecwr) 1%:M) 0).

Definition y (x : 'rV['F_2]_p) :=
lsubmx (castmx (erefl _, etrans (esym tecnw) (addnC _ _)) x).

Lemma sum_f2_eq0 q (P : pred 'I_q) :
\big[GRing.add_comoid [ringType of 'F_2]/0]_(i0 | P i0) 0 = 0.
Proof.
rewrite big_const; set T := #|_|.
elim: T => // t IHt.
by rewrite iterS IHt /= GRing.addr0.
Qed.

Lemma ULE (x : 'rV['F_2]_p) :
  y x *m UL = rsubmx (lsubmx (castmx (erefl, esym choose_m) x)).
Proof.
apply/rowP => i.
rewrite ?(mxE, castmxE).
apply/etrans; first by apply/eq_bigr => j _; rewrite ?(mxE, castmxE).
have inwr: (i + m.-1 * w < n.-1 * w - r)%nat.
 apply: leq_trans.
  apply: (_ : (_ < w + m.-1 * w)%nat); first by rewrite ltn_add2r.
 have->: n.-1 = n.-2.+1 by case: n n2 => []//[].
 rewrite -mulSn [X in (_ <= X - _)%nat]mulSn addnC
         -[X in (X <= _)%nat]addn0 -addnBA //.
 apply leq_add.
  rewrite leq_mul2r; apply/orP; right; apply: (leq_trans _ mn).
  by case: m => []//= ?; apply ltnW.
 by rewrite /leq sub0n.
rewrite (bigD1 (Ordinal inwr)) // -[RHS]GRing.addr0.
congr (_ + _).
 rewrite /= addnK leq_addl !eqxx GRing.mulr1; congr (x _ _).
 by apply/ord_inj; rewrite /= addnC.
apply/etrans; first apply/eq_bigr => j /= P.
case mpwj : (m.-1 * w <= j)%nat.
 have->: (i == (j - m.-1 * w)%N :> nat) = false.
  apply/negP/negP; move: P; apply contra.
  rewrite !eqE /= => /eqP ->.
  by rewrite subnK //.
 by rewrite GRing.mulr0.
 by rewrite andbF GRing.mulr0.
by apply sum_f2_eq0.
Qed.

Definition twist_word (x y : 'rV['F_2]_w) :=
  castmx (erefl, etrans (addnC _ _) twist)
 (row_mx (rsubmx (castmx (erefl, esym twist) x))
         (lsubmx (castmx (erefl, esym twist) y))).

Definition z' (x : 'rV['F_2]_p) :=
  let l := rsubmx (castmx (erefl, esym choose_last) x) in
  twist_word l l.

Lemma zE (x : 'rV['F_2]_p) : z x = z' x.
Proof.
  rewrite /z'.
  set l := rsubmx (castmx (erefl, esym choose_last) x).
  apply/rowP => j.
  rewrite !(mxE, castmxE).
  apply/etrans; first by apply/eq_bigr => k _; rewrite !castmxE block_mxEh !mxE.
  set T := cast_ord _ _; set S := cast_ord _ _.
  case: (splitP T) => i Ti.
  - case: (splitP S) => k Sk; last first.
     suff: (w - r < w - r)%nat by rewrite ltnn.
     suff: (w - r + k < w - r)%nat; apply/leq_trans.
     + by rewrite ltnS leq_addr.
       rewrite /= in Ti, Sk; rewrite -Sk Ti.
     + case: i {Ti} => i /=; apply.
     + apply: wrpwr.
    apply/etrans; first by apply/eq_bigr => t _; rewrite !(castmxE, mxE).
    rewrite !(mxE, castmxE) !cast_ord_id !esymK.
    have rkw: (r + k < w)%nat.
     case: k {Sk} => k /= H.
     apply/leq_trans.
      apply: (_ : _  <  r + (w - r))%nat; by rewrite ltn_add2l.
     by rewrite addnBA // addnC addnK.
    rewrite (bigD1 (Ordinal rkw)) // -[RHS]GRing.addr0; congr (_ + _).
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     case: (splitP Q) => t Qt.
      suff: (r < r)%nat by rewrite ltnn.
      suff: (r + k < r)%nat by apply/leq_trans; rewrite ltnS leq_addr.
      rewrite /= in Qt; rewrite Qt.
      case: t {Qt} => t /=.
      by rewrite prednK //.
     rewrite castmxE mxE eqE /=.
     move/eqP: Qt; rewrite /= prednK // eqn_add2l => /eqP <-.
     rewrite -Sk -Ti eqxx GRing.mulr1.
     by congr (x _ _); apply/val_inj.
    apply/etrans; first apply/eq_bigr => q /= P.
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     case: (splitP Q) => t Qt.
      by rewrite mxE GRing.mulr0.
     rewrite /= in Qt, Sk.
     rewrite castmxE mxE eqE /= -Ti /= Sk.
     case tk: (t == k :> nat)%nat.
      case: q P Q' {Q} Qt => /= q qw.
      rewrite eqE /= (eqP tk) prednK // => qrk ? /eqP.
      by rewrite (negPf qrk).
     by rewrite GRing.mulr0.
    by apply sum_f2_eq0.
  - case: (splitP S) => k Sk.
     suff: (w - r < w - r)%nat by rewrite ltnn.
     suff: (w - r + i < w - r)%nat; apply/leq_trans.
     + by rewrite ltnS leq_addr.
     + rewrite /= prednK // in Ti; rewrite /= in Sk.
       rewrite -Ti Sk; case: k {Sk} => k; apply.
     + by rewrite leqnn.
    apply/etrans; first by apply/eq_bigr => t _; rewrite !(castmxE, mxE).
    rewrite !(mxE, castmxE) !cast_ord_id !esymK.
    have kw: (k < w)%nat.
     case: k {Sk} => k /= H; by apply/(leq_trans H).
    rewrite (bigD1 (Ordinal kw)) // -[RHS]GRing.addr0; congr (_ + _).
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     case: (splitP Q) => t Qt.
      rewrite castmxE mxE eqE /=.
      rewrite /= in Ti, Sk.
      rewrite Sk prednK // in Ti.
      move/eqP: Ti; rewrite eqn_add2l -Qt /= => ->.
      rewrite GRing.mulr1.
      by congr (x _ _); apply/val_inj.
     rewrite /= in Qt.
     suff: (r < r)%nat by rewrite ltnn.
     suff: (r + t < r)%nat by apply/leq_trans; rewrite ltnS leq_addr.
     rewrite prednK // in Qt.
     by rewrite -Qt.
    apply/etrans; first apply/eq_bigr => q /= P.
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     apply: (_ : _ = 0).
     case: (splitP Q) => t Qt.
      rewrite /= ?prednK // in Ti, Qt, Sk.
      rewrite castmxE mxE eqE /= -Qt.
      rewrite Ti in Sk; move/eqP: Sk; rewrite eqn_add2l => /eqP ->.
      case: q P Q' {Q Qt} => //= q ?.
      rewrite eqE /= => /negPf -> ?.
      by rewrite GRing.mulr0.
     by rewrite mxE GRing.mulr0.
    by apply sum_f2_eq0.
Qed.

Definition ra : 'rV_(1 + w.-1) := (row_mx a`_0%:M (\row_i a`_i.+1)).

Definition shiftr (x : 'rV['F_2]_w) : 'rV_(1 + w.-1) :=
row_mx 0 (\row_i castmx (erefl _, esym tecw') x ord0 (widen_ord (leqnSn w.-1) i)).

Definition computeB (x : 'rV['F_2]_p) :=
castmx (erefl _, tecnw)
(row_mx (rsubmx (lsubmx (castmx (erefl, esym choose_m) x)) + castmx (erefl _, tecw')
(shiftr (z' x) + ra *+ (castmx (erefl _, esym tecw') (z' x) ord0 ord_max == 1)))
        (y x)).

Lemma mulBE (x : 'rV['F_2]_p) : x *m B = computeB x.
Proof. by rewrite mulBE_hidden' mulSE ULE -/(z x) !zE. Qed.

Lemma mulBE0 (x : 'rV['F_2]_p) (k : 'I_(n.-1 * w - r)) :
  (x *m B) ord0 (cast_ord tecnw (rshift w k)) = y x ord0 k.
Proof.
  rewrite mulBE_hidden' mulSE ?(castmxE, mxE) /=.
  set T := cast_ord _ _.
  case: (splitP T) => j jT.
   suff: (j >= w)%nat.
    case: j {jT} => j H.
    by rewrite leqNgt /= H.
   by rewrite -jT /= leq_addr.
  rewrite ?(castmxE, mxE).
  congr (x _ _); apply/val_inj => //=.
  by move/eqP: jT; rewrite /= eqn_add2l eq_sym => /eqP.
Qed.

Definition row_ind (o : 'I_p) := Ordinal (ltn_pmod o w0).
Definition col_ind_prf (o : 'I_p) : (o %/ w < n)%nat.
Proof.
  case: o => o oH.
  by apply/leq_ltn_trans/pwn/(leq_div2r _ (ltnW oH)).
Qed.
Definition col_ind (o : 'I_p) :=
  Ordinal (col_ind_prf o).

Definition arr_ind_prf (x : 'I_n) (y : 'I_w) : (x * w + y < n * w)%nat.
Proof.
 case: x => x xn; case: y => y yw.
 apply/leq_ltn_trans; first apply leq_add.
  apply: (_ : _ <= n.-1 * w)%nat.
   apply leq_mul => //.
   by case: n xn n0.
  apply: (_ : _ <= w.-1)%nat.
  by case: w w0 yw.
 case: n n0 => // n' _; case: w w0 => // w' _ /=.
 by rewrite !mulSn !mulnS addnCA -!addnA ltn_add2l addnC ltn_add2r.
Qed.
Definition arr_ind_large (x : 'I_n) (y : 'I_w) := Ordinal (arr_ind_prf x y).
Definition arr_ind (x : 'I_n) (y : 'I_w) :=
match split (cast_ord (esym tecpr) (arr_ind_large x y)) with
| inl l => l
| inr r => cast_ord (esym tecp) ord0
end.

Definition incomplete_array (x : 'M['F_2]_(n, w)) :=
  \row_i x (col_ind i) (row_ind i).

Definition array_incomplete (y : 'rV['F_2]_p) : 'M_(n, w) :=
  \matrix_(i, j) y ord0 (arr_ind i j).

Lemma array_incompleteK : cancel array_incomplete incomplete_array.
Proof.
move=> y; rewrite /incomplete_array /array_incomplete; apply/rowP => j.
rewrite !mxE; congr (y _ _); apply/ord_inj.
rewrite /arr_ind; set T := cast_ord _ _.
case: (splitP T) => s Ts; rewrite /= -divn_eq in Ts.
 by rewrite Ts.
suff: (p < p)%nat by rewrite ltnn.
suff: (p + s < p)%nat; first by apply/leq_trans; rewrite ltnS leq_addr.
by rewrite -Ts.
Qed.

Definition b (v : 'rV['F_2]_p) := v ord0 (Ordinal wrp).

Definition Phi S : 'rV['F_2]_p :=
  \row_i b (S *m (castmx (esym tecp, esym tecp) (castmx (tecp, tecp) B ^+ i))).

Lemma linear_Phi : linear Phi.
Proof.
  move=> c x y.
  apply/rowP => i.
  rewrite !mxE mulmxDl /b !mxE big_distrr.
  congr (_ + _)%R.
  apply/eq_bigr => j _.
  case: c => [][|[]]// i0.
   have->: Ordinal i0 = 0 by apply/ord_inj.
   by rewrite /= !mxE !GRing.mul0r.
  have->: Ordinal i0 = 1 by apply/ord_inj.
  by rewrite /= !mxE !GRing.mul1r.
Qed.

Canonical Phi_linearType := Linear linear_Phi.

(* Lemma PhiE c i j : *)
(*   Phi (c *: delta_mx 0 i) ord0 j = *)
(*   (c * (b (row j (castmx (esym tecp, esym tecp) (castmx (tecp, tecp) B ^+ i))))). *)
(* Proof. *)

Definition Phi_long S : 'rV['F_2]_(2 * p) :=
  \row_i b (S *m (castmx (esym tecp, esym tecp) (castmx (tecp, tecp) B ^+ i))).

Lemma bij_Phi : bijective Phi.
Proof.
  Admitted.

Definition decimate_ind (i : 'I_p) : 'I_(2 * p).
apply: (@Ordinal _ (2 * i)).
case: i => [][|i] i0.
 by rewrite /= muln0 mul2n -addnn ltn_addr.
rewrite /= mulnS addnC addn2.
have: (2 * i.+1 < 2 * p)%N by rewrite ltn_mul2l i0.
apply/leq_trans.
by rewrite /= ltnS mulnS add2n.
Defined.

Definition decimate (x : 'rV['F_2]_(2 * p)) : 'rV['F_2]_p :=
  \row_i x ord0 (decimate_ind i).

Definition H x :=
  castmx (erefl, size_phi)
  (irreducible.H pm' (castmx (erefl, esym size_phi) x)).

Lemma poly_sum (R : ringType) s (E : nat -> R) :
\poly_(k < s) E k = \sum_(k < s) (E k)%:P * ('X ^+ k).
Proof.
elim: s.
 apply/eqP.
 by rewrite big_ord0 -size_poly_eq0 -leqn0 size_poly.
move=> s IHs.
apply/polyP => k.
rewrite big_ord_recr /= -IHs coefD !coef_poly ltnS coefMXn coefC subn_eq0
        leq_eqVlt orbC.
case ks: (k < s)%nat; first by rewrite GRing.addr0.
rewrite GRing.add0r; case: ifP => kse //.
by move/eqP: kse => ->.
Qed.

Lemma char2_poly : 2 \in [char {poly 'F_2}].
Proof. by apply (GRing.rmorph_char (polyC_rmorphism [ringType of 'F_2])). Qed.

Lemma Frobenius_aut_poly s (E : nat -> 'F_2) :
  Frobenius_aut char2_poly (\poly_(k < s) E k) =
  \sum_(k < s) (Frobenius_aut char2_poly ((E k)%:P * ('X ^+ k))).
Proof.
  elim: s => [|s IHs].
   by rewrite /= !poly_sum !big_ord0 GRing.rmorph0.
  rewrite poly_sum big_ord_recr /= -poly_sum.
  rewrite GRing.Frobenius_autD_comm ?IHs ?poly_sum ?big_ord_recr //.
  by rewrite /GRing.comm GRing.mulrC.
Qed.

Lemma modp_sum s (E : 'I_s -> {poly 'F_2}) (q : {poly 'F_2}) :
  (\sum_(k < s) E k) %% q = \sum_(k < s) (E k %% q).
Proof.
  elim: s E => [E |s IHs E].
   by rewrite !big_ord0 mod0p.
  by rewrite !big_ord_recr /= modp_add IHs.
Qed.

Lemma HE : H \o Phi =1 decimate \o Phi_long.
Proof.
  move=> x.
  apply/rowP => j.
  rewrite !(mxE, castmxE) /irreducible.F GRing.Frobenius_autE /=.
  rewrite -irreducible.piXn irreducible.reprE -(GRing.Frobenius_autE char2_poly).
  rewrite /= Frobenius_aut_poly -!Pdiv.IdomainMonic.modpE.
  set T := \sum__ _.
  set E := (fun k => Frobenius_aut char2_poly ((Phi x 0 k)%:P * 'X^k)).
  have->: T = (\sum_(k < p) E k).
   apply/eq_big_cond.
    by rewrite size_phi.
   move=> ? i; congr (Frobenius_aut _ _).
   case: insubP; last first.
    case: i => /= i.
    rewrite size_phi => C; by rewrite C.
   move=> u ? ui.
   rewrite /= castmxE; congr ((Phi x _ _)%:P * _); by apply/ord_inj.
  rewrite modp_sum coef_sum.
  rewrite (bigD1 j) //=.
  subst E.
  'X ^ (2 * i) %% phi = 'X ^ i
  apply eq_bigr => i _.
  rewrite /modp /edivp.
  rewrite GRing.Frobenius_autM_comm; last by rewrite /GRing.comm GRing.mulrC.
  rewrite GRing.Frobenius_autX !GRing.Frobenius_autE.
  rewrite /Phi mxE /b mxE.



  rewrite -/E.


  rewrite /=.


  set E := (Frobenius_aut char2_poly).
  set E := (fun k =>
    Frobenius_aut char2_poly (match insub k with
                                                       | Some i => _
                                                       | None => 0
                                                       end%:P * 'X^k)).
  apply irreducible.f2p_monic //.
  rewrite GRing.linear_sum.
End Main.
