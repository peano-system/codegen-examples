From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma f2p_monic (p : {poly 'F_2}) :
  (p != 0)%R -> p \is monic.
Proof.
  move=> /negPf p0; apply/eqP.
  case lp0: (lead_coef p == 0)%R.
   by rewrite lead_coef_eq0 p0 in lp0.
  case: (lead_coef p) lp0 => [][]//[]// *.
  by apply/val_inj.
Qed.

Lemma f2eqp_eq (p q : {poly 'F_2}) : (p %= q)%R = (p == q).
Proof.
  case q0: (q == 0%R).
   by move/eqP: q0 => ->; rewrite eqp0.
  case p0: (p == 0%R).
   by move/eqP: p0 => ->; rewrite eq_sym -eqp0 eqp_sym.
  rewrite eqp_monic // f2p_monic //.
  + by move/negP/negP: p0.
  + by move/negP/negP: q0.
Qed.

Lemma lem1 q n : prime q -> (n < q -> n.+1 != n %[mod q])%N.
Proof.
  move=> Hq nq.
  case n0: (n == 0)%N.
   move/eqP: n0 => ->.
   rewrite mod0n modn_small //.
   by case: q Hq nq => []//[].
  case nsq: (n.+1 == q).
   move/eqP: nsq => <-.
   by rewrite modnn modn_small // eq_sym n0.
  have nsq': (n.+1 < q)%N
   by rewrite ltn_neqAle nq nsq.
  rewrite !modn_small //.
  by elim n.
Qed.

Lemma exp2_dvd a b :
  2^(a * b) - 1 = (2^a - 1) * \sum_(i < b) 2 ^ (a * (b - i.+1)).
Proof.
elim: b => [|b IHb]; first by rewrite muln0 expn0 subn1 big_ord0 muln0.
rewrite big_ord_recl mulnDr -IHb mulnBl !subn1 -mulnBl mulnS expnD.
have H: forall a, 2 ^ a = 2 ^ a - 1 + 1 by move=> *; rewrite subnK // expn_gt0.
by rewrite [in LHS]H mulnDl mul1n [X in _ + X]H addn1 !addnS !subn1.
Qed.

Lemma m_is_prime m : prime (2 ^ m - 1) -> prime m.
Proof.
apply: contraLR => /primePn []; first by case: m => []//[].
case => a aH /dvdnP[] b mba; move: mba aH => -> mba.
rewrite exp2_dvd; apply/primePn; right.
exists (2 ^ b - 1); rewrite ?dvdn_mulr //.
have? : 1 < 2 ^ b - 1.
 case: b mba => [|[|b _]].
  by rewrite mul0n ltn0 andbF.
  by rewrite mul1n ltnn andbF.
 have: 2 ^ b > 0 by rewrite expn_gt0.
 rewrite subn1 !expnS !mul2n.
 by case: (2 ^ b).
apply/andP; split => //; apply/ltn_Pmulr/ltnW => //.
case: a mba => []//[]// a mba.
rewrite !big_ord_recr /= subnn muln0 expn0 -[X in X < _]add0n ltn_add2r.
by rewrite subSnn muln1 ltn_addl // expn_gt0.
Qed.

Section Quotient.
Variable phi : {poly 'F_2}.
Variable phi_gt1 : size phi > 1.
Local Open Scope ring_scope.
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Lemma phi_neq0 : phi != 0.
Proof.
  rewrite -size_poly_eq0.
  by case: (size phi) phi_gt1.
Qed.

Lemma phi_is_monic : phi \is monic.
Proof. by apply f2p_monic; rewrite -size_poly_gt0 ltnW. Qed.

Hint Resolve phi_is_monic phi_neq0 : core.

Definition phiI := rdvdp phi.
Fact phiI_key : pred_key phiI. Proof. by []. Qed.

Canonical keyd_phiI : keyed_pred phiI_key.
by apply (@PackKeyedPred _ _ phiI_key (rdvdp phi)).
Defined.

Lemma phiI_addr_closed: addr_closed phiI.
Proof.
  split => [|??].
  * by rewrite unfold_in; apply/eqP/rmod0p.
  * rewrite !unfold_in rmodp_add // => /eqP ->.
    by rewrite add0r.
Qed.

Lemma phiI_oppr_closed: oppr_closed phiI.
Proof.
  move=> x.
  rewrite !unfold_in -mulN1r -rmodp_mulmr // => /eqP ->.
  by rewrite mulr0 rmod0p.
Qed.

Lemma phiI_proper_ideal : proper_ideal phiI.
Proof.
  split => [|??].
  * by rewrite unfold_in rmodp_small ?size_polyC ?size_p oner_neq0.
  * rewrite !unfold_in -rmodp_mulmr ?f2p_monic // => /eqP ->.
    by rewrite mulr0 rmod0p.
Qed.

Canonical phiI_addrPred := AddrPred phiI_addr_closed.
Canonical phiI_zmodPred := ZmodPred phiI_oppr_closed.
Canonical phiI_idealr := MkIdeal phiI_zmodPred phiI_proper_ideal.

Local Open Scope quotient_scope.

Definition QphiI := {ideal_quot keyd_phiI}.

Definition QphiI_rV (x : QphiI) : 'rV['F_2]_(size phi).-1 :=
  poly_rV (rmodp (generic_quotient.repr x) phi).
Definition rVQphiI : 'rV['F_2]_(size phi).-1 -> QphiI :=
  \pi \o rVpoly.

Lemma QphiI_rV_K : cancel QphiI_rV rVQphiI.
Proof.
move=> x.
rewrite /rVQphiI /QphiI_rV /= poly_rV_K;
last by case: (size phi) (ltn_rmodpN0 (generic_quotient.repr x) phi_neq0) phi_gt1.
rewrite -[x in RHS]reprK !piE /=.
apply/eqP.
by rewrite -Quotient.idealrBE /= unfold_in rmodp_add //
           rmodp_small ?ltn_rmodp // -rmodp_add // subrr rmod0p.
Qed.

Canonical QphiI_finMixin := CanFinMixin QphiI_rV_K.
Canonical QphiI_finType := FinType QphiI QphiI_finMixin.
Canonical Quotient.rquot_comRingType.
Canonical QphiI_unitRingMixin :=
  Eval hnf in FinRing.Ring.UnitMixin [finRingType of QphiI].
Canonical QphiI_unitRingType := UnitRingType QphiI QphiI_unitRingMixin.
Canonical QphiI_comUnitRingType := Eval hnf in [comUnitRingType of QphiI].
Canonical QphiI_finComUnitRingType := Eval hnf in [finComUnitRingType of QphiI].
Canonical QphiI_finUnitRingType := Eval hnf in [finUnitRingType of QphiI].
End Quotient.

Section new.
Variable phi : {poly 'F_2}.
Local Notation m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).
Local Notation m_is_prime := (m_is_prime pm).

Lemma phi_gt1 : 1 < size phi.
Proof. by case: (size phi) m_is_prime => []//[]. Qed.

Lemma phi_gt2 : 2 < size phi.
Proof. by case: (size phi) m_is_prime => []//[]//[]. Qed.

Lemma phi_gt0 : 0 < size phi.
Proof. by case: (size phi) m_is_prime. Qed.

Lemma power_gt0 : 0 < 2 ^ m.
Proof. by case: (2 ^ m) pm. Qed.

Lemma predpower_gt0 : 0 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpower_neq0 : 0 != 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpower_gt_succpower : (2 ^ m).-1 < (2 ^ m).+1.
Proof. by case: (2 ^ m) pm. Qed.

Lemma phi_gtb (b : bool) : b < size phi.
Proof. by case: b; rewrite ?phi_gt1 ?phi_gt0. Qed.

Lemma predphi_neq0 : m != 0.
Proof. by case: m m_is_prime. Qed.

Lemma predphi_gt1 : 1 < m.
Proof. by case: m m_is_prime => []//[]. Qed.

Lemma predpredpower_power : (2 ^ m - 1).-1 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpredpower_gt0 : 0 < (2 ^ m - 1).-1.
Proof. by case: (2 ^ m - 1) pm => []//[]. Qed.

Lemma p_ord_prf : (2 ^ m - 1 < (2 ^ m).+1)%N.
Proof. by rewrite subn1 predpower_gt_succpower. Qed.

Lemma predphi_geq1 : 1 <= m.
Proof. by case: m m_is_prime => []//[]. Qed.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Hint Resolve (phi_is_monic phi_gt1) (phi_neq0 phi_gt1)
     phi_gt1 phi_gt2 phi_gt0
     phi_gtb predphi_neq0 predphi_gt1 predpredpower_power
     predpredpower_gt0 p_ord_prf predphi_geq1
     predpower_gt_succpower
     power_gt0 predpower_gt0 predpower_neq0 : core.

Section Order.
Definition stab (a : QphiI phi_gt1) n := (a ^+ n * a == a) && (n > 0)%nat.

Variable x : QphiI phi_gt1.
Variable H1 : (x ^ 2 != x)%R.
Variable H2 : (x ^ (2 ^ m)%N == x)%R.
Variable exstab : stab x (2 ^ m - 1)%nat.

Definition minstab := ex_minn (@ex_intro _ (stab x) _ exstab).

Lemma minstab_cond : stab x minstab.
Proof.
  rewrite /minstab.
  by case: (ex_minnP (@ex_intro _ (stab x) _ exstab)).
Qed.

Lemma minstab_exp y : x ^+ minstab ^+ y * x = x.
 elim: y => [|n IH].
  by rewrite GRing.expr0 GRing.mul1r.
 rewrite GRing.exprSr -GRing.mulrA.
 by case/andP: minstab_cond => /eqP -> _.
Qed.

Lemma minstab_dvd : forall y, stab x y -> (minstab %| y)%nat.
Proof.
move=> y.
rewrite /stab (divn_eq y minstab) addnC GRing.exprD mulnC GRing.exprM
 => /andP[] H3.
have H4: x ^+ minstab ^+ (y %/ minstab)%nat * x = x.
 by rewrite minstab_exp.
rewrite -GRing.mulrA H4 in H3.
case ym: (y %% minstab)%nat => *.
 by rewrite add0n dvdn_mulr.
have H5: stab x (y %% minstab)%N.
 by rewrite /stab H3 ym.
move: H5; rewrite /minstab.
case: (ex_minnP (@ex_intro _ (stab x) _ exstab)) => m /andP [] ?? H /H.
by rewrite leqNgt ltn_pmod.
Qed.

Lemma minstabE : minstab = (2 ^ m - 1)%nat.
Proof.
  case/primeP: pm => _ /(_ _ (minstab_dvd exstab))/orP [|/eqP []//].
  rewrite /minstab.
  case: (ex_minnP (@ex_intro _ (stab x) _ exstab)) => [][]//[]// /andP [].
  rewrite -exprSr => H3.
  by move/negP: H1; rewrite H3.
Qed.

Lemma minstab_attain :
forall l k : nat, x ^+ l * x = x ^+ k * x -> (k = l %[mod 2 ^ m - 1])%nat.
Proof.
move: minstabE => /eqP H3.
have base: forall l, (0 < l < 2 ^ m - 1)%N -> x ^+ l * x != x.
 move/eqP: H3 => H l /andP [] Hl0 Hl; apply/negP => /eqP C.
  move: H; rewrite /minstab.
  case: (ex_minnP (@ex_intro _ (stab x) _ exstab)) => m ? H5 H4.
  have/H5 : stab x l by rewrite /stab C Hl0 eqxx.
  by rewrite leqNgt H4 Hl.
have base1:
  forall l k, (l < 2 ^ m - 1 -> 0 < k < 2 ^ m - 1 ->
  (x ^+ l * x = x ^+ k * x)%R -> k = l)%N.
 move=> l k.
 case kl: (k == l %[mod (2 ^ m - 1)])%N.
  move: kl => + Hl1 /andP [] Hk1 Hk2.
  by rewrite !modn_small // => /eqP ->.
 move=> Hl Hk2.
 case kl': (k > l)%N.
  have: (0 < l + (2 ^ m - 1 - k) < 2 ^ m - 1)%N.
   apply/andP; split.
    rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
    move: l0 mk kl => ->.
    rewrite subn_eq0 leqNgt.
    by case/andP: Hk2 => ? ->.
   case/andP: Hk2 => ? Hk2.
   rewrite addnBA; last by apply ltnW.
   rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
   case: (2 ^ m - 1)%nat Hk2 => // ??.
   by rewrite /leq subSS -subnDA addnC subnDA subSn // subnn subnBA
             ?add1n ?subn_eq0 // ltnW.
  move/base => + lk.
  rewrite addnC GRing.exprD -GRing.mulrA lk GRing.mulrA -GRing.exprD subnK.
   by rewrite ?subn1 -GRing.exprSr prednK // H2.
  by case/andP: Hk2 => ??; rewrite ltnW.
 move/negP/negP: kl'; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP ->|] // kl'.
 have: (0 < k + (2 ^ m - 1 - l) < 2 ^ m - 1)%N.
  apply/andP; split.
   rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
   move: l0 mk kl => ->.
   by rewrite subn_eq0 leqNgt Hl.
  rewrite addnBA; last by apply ltnW.
  rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
  case/andP: Hk2 => ? Hk2.
   case: (2 ^ m - 1)%nat Hk2 => // ??.
   by rewrite /leq subSS -subnDA addnC subnDA subSn // subnn subnBA
             ?add1n ?subn_eq0 // ltnW.
 move/base => + lk.
 rewrite addnC GRing.exprD -GRing.mulrA -lk GRing.mulrA -GRing.exprD subnK //.
  by rewrite subn1 -GRing.exprSr prednK // H2.
 by rewrite ltnW.
have base2:
  forall l k : nat, (0 < k < 2 ^ m - 1)%N ->
  x ^+ l * x = x ^+ k * x -> (k = l %% (2 ^ m - 1))%N.
  move=> l k /base1 b.
  rewrite [X in (_ ^+ X * _)%R](divn_eq l (2 ^ m - 1)) addnC GRing.exprD
          -GRing.mulrA mulnC exprM -(eqP H3) minstab_exp.
  apply/b.
  by rewrite minstabE ltn_pmod //.
move=> l k.
rewrite (divn_eq k (2 ^ m - 1)) addnC GRing.exprD -GRing.mulrA
        mulnC exprM -(eqP H3) minstab_exp addnC mulnC modnMDl.
case k0: (k %% minstab)%N.
 rewrite expr0 mul1r.
 case l0: (l %% minstab)%N; first by rewrite mod0n.
 rewrite (divn_eq l minstab) addnC exprD -mulrA mulnC exprM minstab_exp => /eqP C.
 move: (base (l %% minstab)%nat).
 by rewrite !minstabE ltn_pmod // -!minstabE l0 /= -l0 C => /implyP.
move/base2 => /=.
rewrite -k0 !minstabE ltn_pmod // -!minstabE => C.
by rewrite modn_mod C.
Qed.

Lemma map_pi_inj :
injective (fun (i : 'Z_(2 ^ m - 1)) => x ^+ i * x).
Proof.
  move=> y z /eqP.
  rewrite eqE /= => /eqP /minstab_attain.
  case: y => y yH.
  case: z => z zH.
  rewrite !modn_small //=.
  by move=> yx; apply/val_inj.
  apply: (leq_trans yH); by rewrite prednK.
  apply: (leq_trans zH); by rewrite prednK.
Qed.

Lemma map_pi_card :
#|image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1)| = (2 ^ m - 1)%N.
Proof.
  have Hc : #|'Z_(2 ^ m - 1)| = (2 ^ m - 1)%nat.
   rewrite card_ord.
   by case: (2 ^ m - 1)%nat pm => [][].
  rewrite -[RHS]Hc.
  apply/eqP/image_injP => [][] y Hy1 [] z Hz1 _ _ /minstab_attain /esym H;
   apply/ord_inj.
  rewrite /= ?modn_small // in H.
  move: (Hy1) (Hz1) => ??.
  rewrite /= /Zp_trunc /= ?prednK // in Hy1, Hz1.
  rewrite /= /Zp_trunc /= ?prednK // in Hy1, Hz1.
Qed.

Lemma Xn_phi_neq0 (a : nat) : x ^+ a * x != 0.
Proof.
  move: minstab_attain => H0; apply/negP => /eqP Hc.
  move: (H0 a a.+1).
  rewrite GRing.exprS -GRing.mulrA Hc GRing.mulr0 => /(_ erefl)/eqP.
  rewrite (divn_eq a (2 ^ m - 1)) -addnS !modnMDl.
  by apply/negP/lem1 => //; rewrite ltn_mod.
Qed.

Lemma map_piE :
image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1)
=i (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
Proof.
 have H3: [seq x ^ i * x | i : 'Z_(2 ^ (size phi).-1 - 1)] \subset
          [set x | [finComRingType of QphiI phi_gt1] x] :\ 0.
  suff: codom (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x)
        \subset (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
   by apply/subset_trans/subsetP/image_codom.
  apply/subsetP => y.
  rewrite codomE !inE /=.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH -> //].
  by move: (Xn_phi_neq0 a) => ->.
 apply/subset_cardP => //.
 move: (subset_leq_card H3).
 rewrite !cardsDS /= ?sub1set ?inE // !cardsT !map_pi_card
         cards1 leq_eqVlt => /orP [/eqP //|].
 rewrite ltnNge /= leq_sub2r //.
 move: (@card_in_image _ _ (@QphiI_rV _ phi_gt1) predT) <-
  => [|????]; last by apply (can_inj (@QphiI_rV_K _ phi_gt1)).
 have<-: (#|'rV['F_2]_(size phi).-1| = 2 ^ (size phi).-1)%nat
  by rewrite card_matrix mul1n card_ord.
 by apply/subset_leq_card/subsetP.
Qed.

Lemma map_piP q :
reflect (exists (r : 'Z_(2 ^ m - 1)), x ^ r * x = q)
(q \in (image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1))).
Proof.
move: map_pi_inj => inj.
apply/(iffP idP).
* rewrite /image_mem.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH //]; by exists a.
* case => q0 <-.
  set T := (fun (i : 'Z_(2 ^ (size phi).-1 - 1)) => x ^ i * x).
  set S := x ^ q0 * x.
  have->: S = T q0 by [].
  by rewrite mem_map // mem_enum.
Qed.
End Order.

Section direct.
Variable H1 : ('X ^ 2 %% phi)%R != ('X %% phi)%R.
Variable H2 : ('X ^ (2 ^ m)%N %% phi)%R == ('X %% phi)%R.

Lemma H2E : (\pi 'X : QphiI phi_gt1)^(2 ^ m)%nat == \pi 'X.
  rewrite -exprnP -rmorphX /= -Quotient.idealrBE unfold_in rmodp_add // addr_eq0.
  set T := rmodp _ phi; have->: T = 'X ^ (2 ^ (size phi).-1)%N %% phi.
   by apply/eqP; rewrite -f2eqp_eq eqp_rmod_mod.
  set S := - _; have-> //: S = 'X %% phi.
  by rewrite /S rmodp_small ?modp_small ?opprK // ?size_opp ?size_polyX.
Qed.

Lemma exstab : stab (\pi 'X) (2 ^ m - 1)%nat.
by rewrite /stab -rmorphX -rmorphM -exprSr subn1 prednK //
           exprnP rmorphX H2E /= -subn1.
Qed.

Check minstab.

Lemma piX_unit : (\pi 'X : QphiI phi_gt1) \is a GRing.unit.
Proof.
  have H: stab (\pi 'X) (2 ^ m - 1)%nat.
   by rewrite /stab -rmorphX -rmorphM -exprSr subn1 prednK //
              exprnP rmorphX H2E /= -subn1.
  have:
   Check ex_minn (@ex_intro _ (stab (\pi 'X)) _ H).
   Check {stab (\pi 'X)}.
   Check ex_minn.
   Check (@ex_intro _ _ _ H).
  Check ex_minn H.


  ('X ^ (2 ^ m)%N %% phi)%R == ('X %% phi)%R.
  Check ex_minn (stab (\pi 'X)).

  apply/existsP.
Check FinRing.unit (QphiI phi_gt1) _.

  exists (\pi 'X : QphiI phi_gt1)^(2 ^ m)%na
  rewrite /= unfold_in.
  rewrite /=.

Lemma irreducibleP_direct : irreducible_poly phi.
Proof.
  split => //.
  rewrite /irreducible_poly.
  rewrite phi_gt1 /=.

Check {unit QphiI}.

Check FinRing.unit QphiI (\pi 'X).

Check {unit QphiI} _.

Check [unitRingType of QphiI].

Check [finRingType of QphiI].

Eval hnf in FinRing.Ring.UnitMixin [finRingType of QphiI].

Check
End new.

Check {ideal_quot _}.

Check idealr


Definition pI_pred : pred _ := rdvdp p.
Fact pI_key : pred_key pI_pred. Proof. by []. Qed.
Canonical pI := KeyedPred pI_key.


(*
based on:
 http://www.math.sci.hiroshima-u.ac.jp/~m-mat/TEACH/0407-2.pdf
 P. 27
*)

Section iter_lin.
  Variable K : fieldType.
  Variable R : vectType K.
  Variable f : {linear R -> R}%R.
  Lemma iter_linear m : linear (iter m f).
  Proof.
    elim: m => // m IHm a x y.
    by rewrite !iterSr !GRing.linearP IHm.
  Qed.
  Canonical iter_linearType m := Linear (iter_linear m).
End iter_lin.

Lemma ltn_subr a b : 0 < b < a -> a - b < a.
Proof.
  case/andP.
  elim: a => // a IH.
  case ab: (b == a).
   move/eqP: ab => ->.
   by rewrite subSnn !ltnS.
  move/IH => {IH} IH.
  rewrite ltnS leq_eqVlt ab => ba.
  by rewrite subSn ?ltnS ?IH // ltnW.
Qed.

Lemma ltn_size_polyC_X (R : fieldType) (p : {poly R}) (c : R) (n : nat) :
  p != 0%R -> (size (c%:P)%R < size (p * 'X)%R)%N.
Proof.
move=> ?; rewrite size_mul ?polyX_eq0 // size_polyX size_polyC addn2.
case: (c != 0%R) => //.
by rewrite ltnS lt0n size_poly_eq0.
Qed.

Lemma polyX_neq0 (R : fieldType) : (('X : {poly R}) != 0)%R.
Proof. by rewrite -size_poly_eq0 size_polyX. Qed.

Hint Resolve ltn_size_polyC_X polyX_neq0 : core.

Lemma polyXn_eq0 (R : fieldType) n :
  (('X^n : [ringType of {poly R}]) == 0)%R = false.
Proof. by rewrite -size_poly_eq0 size_polyXn. Qed.

Section irreducibility.
Variable phi : {poly 'F_2}.
Local Notation m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).

Local Notation m_is_prime := (m_is_prime pm).


Canonical qpoly_ringType_phi :=
  Eval hnf in qpoly_ringType phi_gt1.
Canonical qpoly_comRingType_phi :=
  Eval hnf in qpoly_comRingType phi_gt1.
Definition pi := canon_surj phi_gt1.

Hint Resolve phi_gt0 phi_gt1 phi_gt2 phi_gtb predphi_neq0
     predpredpower_power predpredpower_gt0 predphi_gt1 predphi_geq1
     predphi_neq0 predpower_neq0 predpower_gt0
     p_ord_prf predpower_gt_succpower power_gt0 phi_neq0 polyX_neq0 : core.

Lemma mod_ord (a : nat) y (x : ordinal y) : ordinal y.
  apply/(@Ordinal _ (x %% a))/(leq_ltn_trans (leq_mod _ _)).
  by case: x.
Defined.

Definition p_ord := Ordinal p_ord_prf.

Lemma one_ord : ordinal (2 ^ m).+1.
 have H: 1 < (2 ^ m).+1.
  case/primeP: pm => pm' _.
  apply/(ltn_trans pm').
  rewrite subn1.
  by case: (2 ^ m) pm.
 by apply (Ordinal H).
Defined.


Lemma map_pi_card :
(forall l k : nat, (pi 'X ^+ l * pi 'X = pi 'X ^+ k * pi 'X)%R
             -> k = l %[mod 2 ^ m - 1])
-> #|image (fun (x: [ringType of 'Z_(2 ^ m - 1)])
           => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)| = (2 ^ m - 1)%N.
Proof.
  move=> /map_pi_inj H.
  have Hc : #|'Z_(2 ^ m - 1)| = 2 ^ m - 1.
   rewrite card_ord.
   by case: (2 ^ m - 1) pm => [][].
  rewrite -[RHS]Hc.
  apply/eqP/image_injP => x y Hx Hy.
  rewrite !GRing.rmorphM !GRing.rmorphX.
  apply H.
Qed.

Lemma map_piE :
p_ord \in stab (pi 'X : {qpoly phi})%R (pi 'X)%R ->
(min_stab (pi 'X : {qpoly phi})%R (pi 'X)%R == (2 ^ m - 1)%N)%R ->
image (fun (x: [ringType of 'Z_(2 ^ m - 1)])
         => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)
=i (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
Proof.
 move=> H1 H3; move: (min_stab_attain H1 H3) => H.
 move/map_pi_card: (H) => Hc.
 apply/subset_cardP.
 by rewrite cardsDS /= ?sub1set ?inE // cardsT Hc card_npoly card_ord /m cards1.
 suff: codom (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R)
       \subset (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
  by apply/subset_trans/subsetP/image_codom.
 apply/subsetP => x.
 rewrite codomE !inE /=.
 elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
 rewrite in_cons => /orP [/eqP ->|/IH -> //].
 move: (Xn_phi_neq0 a H).
 by rewrite -!GRing.rmorphX -!GRing.rmorphM -!exprnP andbT !eqE.
Qed.

Lemma map_piP q :
(forall l k : nat, (pi 'X ^+ l * pi 'X)%R = (pi 'X ^+ k * pi 'X)%R
              -> k = l %[mod 2 ^ m - 1])
-> reflect (exists (r : 'Z_(2 ^ m - 1)), pi ('X ^ r * 'X)%R = q)
(q \in (image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R)
'Z_(2 ^ m - 1))).
Proof.
move/map_pi_inj => inj.
apply/(iffP idP).
* rewrite /image_mem.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH //]; by exists a.
* case => q0 <-.
  rewrite mem_image // => x y.
  rewrite ?(GRing.rmorphM, GRing.rmorphX).
  apply/inj.
Qed.

Lemma X2m_eqXE :
(('X ^ (2 ^ m)%N %% phi == 'X %% phi) = (p_ord \in stab (pi 'X) (pi 'X)))%R.
by rewrite inE -!GRing.rmorphX -!GRing.rmorphM -!exprnP !eqE /=
           -GRing.exprSr subn1 prednK.
Qed.

Lemma X2_neqXE :
(('X ^ 2 %% phi != 'X %% phi) = (one_ord \notin stab (pi 'X) (pi 'X)))%R.
by rewrite inE -!GRing.rmorphX -!GRing.rmorphM -!exprnP !eqE /=
           -GRing.exprSr.
Qed.

Section direct.
Variable H1 : ('X ^ 2 %% phi)%R != ('X %% phi)%R.
Variable H2 : ('X ^ (2 ^ (size phi).-1)%N %% phi)%R == ('X %% phi)%R.
Lemma irreducibleP_direct : irreducible_poly phi.
Proof.
  have H: (p_ord \in stab (pi 'X) (pi 'X))%R by rewrite -X2m_eqXE.
  case/min_stab_dvd: (H) pm => + /primeP [] o pm' => /pm' {pm'}.
  have: (one_ord \notin stab (pi 'X) (pi 'X))%R by rewrite -X2_neqXE.
  move/(@min_stab_neq1 _ _ _ _ H) => -> // x2m1.
  apply/irreducibleP/andP; split => //.
  apply/forallP => q; apply/implyP.
  case q0: (size q == 0); first by move/eqP: q0 => ->.
  move: (min_stab_attain H x2m1) => H0.
  have: q \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
   rewrite !inE andbT.
   apply/negP => /eqP T; move: T q0 => ->.
   by rewrite size_polyC eqxx.
  rewrite -!map_piE //.
  case/(map_piP _ H0) => q1 <-.
  have pq0: forall q1 : nat, pi ('X ^ q1 * 'X)%R != 0%R
   by move=> *; rewrite !GRing.rmorphM !GRing.rmorphX Xn_phi_neq0.
  case/Pdiv.RingMonic.rdvdpP => [|x pxp]; first by apply/f2p_monic/pq0.
  case x0: (x == 0)%R.
   move/eqP: x0 pxp phi_neq0 => ->.
   rewrite GRing.mul0r => <-.
   by rewrite eqxx.
  have/dvdp_leq: (x %| phi)%R by rewrite pxp dvdp_mulr.
  rewrite phi_neq0 => /implyP.
  rewrite leq_eqVlt => /orP [/eqP|] xp.
   have: size phi = size (x * pi ('X ^ q1 * 'X))%R by rewrite -pxp.
   rewrite size_mul ?x0 ?pq0 // xp => /eqP.
   by rewrite -subn1 -[X in X == _]addn0 -addnBA ?lt0n ?size_poly_eq0
              ?pq0 // eqn_add2l eq_sym subn_eq0.
  have xx: x = pi x by rewrite /= modp_small.
  have: pi phi == pi (x * pi ('X ^ q1 * 'X))%R by rewrite -pxp.
  have: (pi x)%R \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
   by rewrite !inE andbT eqE /= -size_poly_eq0 modp_small //
           ?ltn_size_polyC_X ?size_polyC size_poly_eq0 x0.
  rewrite GRing.rmorphM -!map_piE //.
  case/(map_piP _ H0) => x1 <-.
  rewrite -GRing.rmorphM eqE /= modpp modp_mul
          GRing.mulrCA !GRing.mulrA -GRing.exprD GRing.mulrC
          GRing.mulrA -GRing.exprS eq_sym => /negPn.
  by rewrite pq0.
Qed.
Check FinRing.unit _ _.
End direct.

Section inverse.
(*
   This direction is trivial.
   Because the statement just says that the galois group is nontrivial.
*)
Variable ip : irreducible_poly phi.

Lemma piX_neq0 : pi 'X%R != 0%R.
Proof.
  apply/negP => /eqP /(f_equal val).
  rewrite /= modp_small ?size_polyX // => /eqP.
  by rewrite -size_poly_eq0 size_polyX.
Qed.

Definition qpoly_fieldType_phi := Eval hnf in qpoly_fieldType ip.

Definition Xu: ((pi 'X : qpoly_fieldType_phi) \is a GRing.unit)%R.
  by rewrite GRing.unitfE piX_neq0.
Defined.

Definition L : fieldExtType [fieldType of 'F_2].
  by case/irredp_FAdjoin: ip.
Defined.

Definition dL : \dim (fullv : {vspace L}) = (size phi).-1.
  rewrite /L.
  by case/irredp_FAdjoin: ip.
Defined.

Definition z : L.
  rewrite /L.
  by case/irredp_FAdjoin: ip => ?? [].
Defined.

Definition zsp : root (map_poly (GRing.in_alg L) phi) z.
  rewrite /z /L /=.
  by case/irredp_FAdjoin: ip => ?? [].
Defined.

Definition sL : <<1; z>>%VS = (fullv : {vspace L}).
  rewrite /z /L /=.
  by case/irredp_FAdjoin: ip => ?? [].
Defined.

Definition e0 : {qpoly phi} -> L
  := (fun g => (map_poly (GRing.in_alg L) g).[z])%R.

Definition rme : rmorphism (e0 : qpoly_fieldType_phi -> _).
  rewrite /e0; repeat constructor.
   * move=> x y.
     by rewrite /= !GRing.rmorphB hornerD hornerN.
   * move=> x y.
     rewrite /= -hornerM -GRing.rmorphM.
     set T := (_ * _)%R.
     rewrite [in RHS](divp_eq T phi) GRing.rmorphD hornerD GRing.rmorphM hornerM.
     move/rootP: zsp => ->.
     by rewrite GRing.mulr0 GRing.add0r.
   * by rewrite /= modp_small ?GRing.rmorph1 ?hornerC // size_polyC.
Defined.

Definition e := RMorphism rme.

Lemma inje: injective e. Proof. by apply GRing.fmorph_inj. Qed.

Lemma a1f: agenv ([aspace of 1%AS] : {subfield L}) = fullv -> False.
Proof.
 have K1: ((\sum_(i < (size phi).-1)
       ([aspace of 1%AS] : {subfield L}) ^+ i)%VS = 1%VS).
  have: (size phi).-1 != 0 by [].
  elim: (size phi).-1 => // n IHn _.
  rewrite big_ord_recr expv1n /=.
  case n0: (n == 0).
   move/eqP: n0 => ->.
   by rewrite big_ord0 add0v.
  by rewrite IHn ?n0 // addvv.
 rewrite /agenv dL K1.
 move: dL => + f1.
 rewrite -f1 dimv1 => p1.
 by move: p1 m_is_prime => <-.
Qed.

Local Hint Resolve Xu : core.

Lemma piX2X : (pi ('X ^ 2) != pi 'X)%R.
Proof.
   set fT := qpoly_fieldType_phi.
   apply/negP => /eqP /(f_equal (fun x => (pi 'X : fT)^-1 * x))%R.
   rewrite GRing.mulVr //.
   have ->: (pi ('X ^ 2) = (pi 'X : fT) * (pi 'X : fT))%R.
    rewrite -exprnP GRing.exprS GRing.expr1 GRing.rmorphM.
   by apply/val_inj.
   rewrite GRing.mulKr // => /(f_equal e) z1; move: z1 sL.
   rewrite /e /e0 /= !modp_small ?size_polyC ?size_polyX //
           map_polyC hornerC map_polyX hornerX /= GRing.scale1r => ->.
   by rewrite addvv => /a1f.
Qed.

Definition piX := FinRing.unit [finFieldType of qpoly_fieldType_phi] Xu.

Lemma piX_order : #[piX]%g = 2 ^ m - 1.
Proof.
  have/cyclic.order_dvdG: piX \in
      [group of [set: {unit [finFieldType of qpoly_fieldType_phi]}]]
    by rewrite inE.
  rewrite card_finField_unit card_npoly card_ord.
  case/primeP: pm => _.
  rewrite !subn1 => H /H {H} /orP [|/eqP] //.
  rewrite order_eq1 => piX1.
  move: piX1 piX2X;
  rewrite /piX GRing.rmorphX !eqE /= !eqE /= => /eqP ->.
  (* TODO : fix canonical structure *)
  by rewrite !modp_small ?GRing.mulr1 ?size_polyC ?eqxx.
Qed.

Lemma val_piX_expE p : val (piX ^+ p)%g = pi ('X ^+ p)%R.
Proof.
  elim: p => [|p IHp].
   by apply/val_inj.
  rewrite !GRing.exprS GRing.rmorphM expgS /= IHp.
  by apply/val_inj.
Qed.

Lemma X2mp_eq1 : (pi ('X ^+ (2 ^ m - 1)) = 1)%R.
Proof.
  suff/(f_equal val): (piX ^+ (2 ^ m - 1))%g = 1%g.
   rewrite val_piX_expE /= => ->.
   by apply/val_inj.
  suff<-: #[piX]%g = 2 ^ m - 1 by rewrite expg_order.
  by rewrite piX_order.
Qed.

Lemma irreducibleP_inverse :
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
  apply/andP; split; first by move: piX2X; rewrite eqE.
  suff/(f_equal val) /= ->: (pi ('X ^ (2 ^ m)%N) = (pi 'X))%R by [].
  move: X2mp_eq1; rewrite GRing.rmorphX => H.
  have->: 2 ^ m = (2 ^ m - 1).+1 by rewrite subn1 prednK.
  by rewrite GRing.rmorphX GRing.exprS H GRing.mulr1.
Qed.

Lemma char2_phi : 2 \in [char {qpoly phi}]%R.
Proof.
by apply/(GRing.rmorph_char pi)
        /(GRing.rmorph_char (polyC_rmorphism [ringType of 'F_2])).
Qed.

Definition H := Frobenius_aut char2_phi.

Lemma linear_H : linear H.
Proof.
  move=> a x y.
  case: a => [][|[]//] i; set T := Ordinal i.
   have->: T = 0%R by apply/val_inj.
   by rewrite !GRing.scale0r !GRing.add0r.
  have->: T = 1%R by apply/val_inj.
  rewrite !GRing.scale1r /H GRing.Frobenius_autD_comm //.
  apply/val_inj.
  by rewrite /= GRing.mulrC.
Qed.

Canonical linearType_H := Eval hnf in Linear linear_H.

Lemma expXpE p x : iter p H x = (x ^+ (2 ^ p))%R.
Proof.
  elim: p x => [x|p IH x].
   by rewrite /= expn0 GRing.expr1.
  by rewrite iterS IH /H GRing.Frobenius_autE
             !GRing.exprS GRing.expr0 GRing.mulr1
             -GRing.exprD addnn expnS mul2n.
Qed.

Lemma expand_H q :
  reflect (iter q H =1 id) ('X^(2 ^ q) %% phi == 'X %% phi)%R.
Proof.
  apply/(iffP idP).
  * move/eqP=> H0 x.
    rewrite (coord_basis (npolyX_full _ _) (memvf x)).
    set e0 := npolyX _ _.
    rewrite GRing.linear_sum; apply/eq_big => // i _.
    rewrite GRing.linearZ_LR /= expXpE.
    congr (_ *: _)%R.
    rewrite (nth_map i) // ?size_enum_ord //=
            nth_enum_ord ?size_polyXn // .
    set Xi := npolyp _ _.
    have->: Xi = (pi 'X^i)%R.
     apply/npolyP => j.
     subst Xi => /=.
     rewrite npolypK ?modp_small ?size_polyXn // .
     case: i => i Hi.
     by case: (size phi) Hi phi_gt1.
    case p0: (q > 0); last first.
     rewrite lt0n in p0.
     by move/negP/negP/eqP: p0 ->.
    rewrite GRing.rmorphX GRing.exprAC -[in LHS]GRing.rmorphX.
    set T := (pi 'X^(2 ^ q))%R.
    suff->: T = (pi 'X)%R by [].
    apply/val_inj.
    by rewrite /= H0.
  * move=> H1.
    move/(f_equal val): (H1 (pi 'X))%R.
    by rewrite expXpE -GRing.rmorphX /= => ->.
Qed.

Lemma cycleH_dvdP p :
  reflect (iter p H =1 id) (2 ^ m - 1 %| 2 ^ p - 1).
Proof.
  have H0: (pi ('X ^ (2 ^ m)%N) = pi 'X)%R.
   apply/val_inj.
   by case/andP: irreducibleP_inverse => _ /eqP.
  apply/(iffP idP).
  * case/dvdnP => q H1 x.
    apply/expand_H.
    case p0: (p > 0); last first.
     rewrite lt0n in p0.
     by move/negP/negP/eqP: p0 ->.
    have->: (2 ^ p) = ((2 ^ p) - 1).+1.
     rewrite subn1 prednK // {H1}.
     elim: p p0 => // [][] // p IH _.
     have->: 0 = 2 * 0 by [].
     by rewrite expnS ltn_mul2l /= muln0 IH.
    rewrite H1 {H1} GRing.exprS.
    elim: q => [|q /eqP IH].
     by rewrite mul0n GRing.expr0 GRing.mulr1.
    rewrite mulSn addnC GRing.exprD GRing.mulrA GRing.mulrC -modp_mul IH
            modp_mul -GRing.exprSr subn1 prednK //.
    by move: (f_equal val H0) => /= ->.
  * move=> H1.
    move: (H1 (pi 'X))%R.
    rewrite expXpE -GRing.rmorphX -val_piX_expE -H0 -val_piX_expE => /val_inj/eqP.
    rewrite cyclic.eq_expg_mod_order piX_order.
    have H2: 2 ^ (size phi).-1 = ((2 ^ (size phi).-1) - 1) + 1
     by rewrite addn1 subn1 prednK.
    have H3: 1 = 0 + 1 by rewrite add0n.
    case p0: (p > 0); last first.
     rewrite lt0n in p0.
     by move/negP/negP/eqP: p0 ->.
    have H4: (2 ^ p) = ((2 ^ p) - 1) + 1.
     rewrite subn1 addn1 prednK // {H1}.
     elim: p p0 => // [][] // p IH _.
     have->: 0 = 2 * 0 by [].
     by rewrite expnS ltn_mul2l /= muln0 IH.
    rewrite [X in _ == X %[mod _]]H2 modnDl [X in _ == X %[mod _]]H3
            [X in X == _ %[mod _]]H4 eqn_modDr.
    by rewrite mod0n.
Qed.

Lemma iter_sand_H s :
   iter s ((@npoly_rV _ _) \o H \o (@rVnpoly _ _))
=1 (@npoly_rV _ _) \o iter s H \o (@rVnpoly _ _).
Proof.
  elim: s => [?|s IH x].
   by rewrite /= rVnpolyK.
  by rewrite iterS IH /= npoly_rV_K.
Qed.

Lemma iterHP q :
  iter q H =1 id <-> iter q ((@npoly_rV _ _) \o H \o (@rVnpoly _ _)) =1 id.
Proof.
  split => H0 x.
   by rewrite iter_sand_H /= H0 rVnpolyK.
  move: (H0 (npoly_rV x)).
  rewrite iter_sand_H /= npoly_rV_K.
  by move/(can_inj (@npoly_rV_K _ _)).
Qed.

Lemma piXE : (pi 'X = 'X %% phi :> {poly 'F_2})%R.
Proof. by []. Qed.

Lemma piXnE q : (pi ('X ^ q) = 'X ^ q %% phi :> {poly 'F_2})%R.
Proof. by []. Qed.

Lemma irreducibleE0 q :
  ('X^(2 ^ q) %% phi == 'X %% phi)%R =
  (iter q ((@npoly_rV _ _) \o H \o (@rVnpoly _ _)) (npoly_rV (pi 'X))
  == npoly_rV (pi 'X))%R.
Proof.
  rewrite iter_sand_H /= npoly_rV_K expXpE exprnP -piXnE -piXE.
  set T := _ == _; case H0: T; subst T.
   move/eqP: H0 => /= H0.
   apply/esym/eqP/f_equal/eqP.
   rewrite eqE /= -H0; set T := qpolify _ _; have->: (T = pi 'X)%R by [].
   by rewrite -GRing.rmorphX.
  apply/esym/negP/negP.
  move/negP/negP: H0; apply/contra.
  move/eqP/(can_inj (@npoly_rV_K _ _))/eqP.
  set T := qpolify _ _; have->: (T = pi 'X)%R by [].
  by rewrite GRing.rmorphX.
Qed.
End inverse.

Lemma irreducibleP :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
  apply/(iffP idP).
   by case/andP; apply irreducibleP_direct.
  by apply irreducibleP_inverse.
Qed.

Lemma irreducibleP1 q :
reflect (irreducible_poly phi)
  [exists x, (((@npoly_rV _ _) \o H \o (@rVnpoly _ _)) x != x) &&
        (iter q ((@npoly_rV _ _) \o H \o (@rVnpoly _ _)) x == x)%R].
Proof.
  apply/(iffP idP).
  + case/existsP => x /andP[] H1 H2.
    apply/irreducibleP/andP; split; last first.
    - rewrite irreducibleE0.

    - apply/expand_H.
        Check expand_H.
      rewrite -iterHP in H2.
    - move: H1; apply/contra => /eqP H1.
      rewrite /= (coord_basis (npolyX_full _ _) (memvf (rVnpoly x))).
      set e0 := npolyX _ _.
      rewrite GRing.linear_sum; apply/eqP/(can_inj (@rVnpolyK _ _)).
      rewrite npoly_rV_K.
              ; apply/etrans.
      apply/eq_big => [//|i _].
      rewrite /=.
      rewrite /= (nth_map (pi 'X%R)).
    rewrite GRing.linearZ_LR /= expXpE.
    congr (_ *: _)%R.
    rewrite (nth_map i) // ?size_enum_ord //=
            nth_enum_ord ?size_polyXn // .
    set Xi := npolyp _ _.
    have->: Xi = (pi 'X^i)%R.
     apply/npolyP => j.
     subst Xi => /=.
     rewrite npolypK ?modp_small ?size_polyXn // .
     case: i => i Hi.
     by case: (size phi) Hi phi_gt1.
    case p0: (q > 0); last first.
     rewrite lt0n in p0.
     by move/negP/negP/eqP: p0 ->.
    rewrite GRing.rmorphX GRing.exprAC -[in LHS]GRing.rmorphX.
    set T := (pi 'X^(2 ^ q))%R.
    suff->: T = (pi 'X)%R by [].
    apply/val_inj.
    by rewrite /= H0.
      rewrite /=.
    set e0 := npolyX _ _.

  rewrite irreducibleE0.
  rewrite iter_sand_H /= npoly_rV_K expXpE exprnP -piXnE -piXE.
  set T := _ == _; case H0: T; subst T.
   move/eqP: H0 => /= H0.
   apply/esym/eqP/f_equal/eqP.
   rewrite eqE /= -H0; set T := qpolify _ _; have->: (T = pi 'X)%R by [].
   by rewrite -GRing.rmorphX.
  apply/esym/negP/negP.
  move/negP/negP: H0; apply/contra.
  move/eqP/(can_inj (@npoly_rV_K _ _))/eqP.
  set T := qpolify _ _; have->: (T = pi 'X)%R by [].
  by rewrite GRing.rmorphX.
Qed.
End irreducibility.

Section Order.
Context {R : ringType}.
Variable t : R.
Implicit Types (a : R).
Local Open Scope ring_scope.

Definition stab a n := (t ^+ n * a == a) && (n > 0)%nat.
Check ex_minn.

Lemma foldl_min_cons x y z : foldl minn x (y :: z) = minn y (foldl minn x z).
Proof.
  elim: z x y => [*| ? z IH x y] /=;
  by rewrite minnC // -IH /= minnAC minnC.
Qed.

Definition min_stab a :=
foldl minn (2 ^ m)%N
      (filter (fun x => x > 0)%N (map (@nat_of_ord _) (enum (stab a)))).

Definition min_stab_ord a : ordinal (2 ^ m).+1.
  have H: (min_stab a < (2 ^ m).+1)%N.
   rewrite /min_stab.
   elim: [seq _ | _ <- _] => [|c l IH].
    by case: (2 ^ m)%N pm.
   apply/leq_ltn_trans/IH => {IH} /=.
   by case: ifP => //; rewrite foldl_min_cons geq_minr.
 by apply (Ordinal H).
Defined.

Lemma foldl_minn_in xs m' :
  has (fun x => x < m'.+1)%N xs -> foldl minn m' xs \in xs.
Proof.
  elim: xs m' => // x xs IH m'.
  rewrite /= in_cons.
  case xm: (x < m'.+1)%N.
   rewrite /minn ltnNge -ltnS xm /= -/minn => _ {IH xm}.
   elim: xs x => [?|y ? IH /= x].
    by rewrite /= eqxx.
   case xy: (x < y)%N.
    rewrite /minn xy /= -/minn in_cons.
    case/orP: (IH x) => -> //.
    by rewrite !orbT.
   rewrite /minn xy /= -/minn in_cons.
   by case/orP: (IH y) => ->; rewrite !orbT.
  move/negP/negP: xm; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP <-|mx].
  by rewrite /minn ltnSn -/minn => /IH ->; rewrite orbT.
  by rewrite /minn ltnW // -/minn => /IH ->; rewrite orbT.
Qed.

Lemma min_stab_gt0 a : (0 < min_stab_ord a)%N.
Proof.
  rewrite /min_stab_ord /min_stab /=.
  elim: (enum (pred_of_set (stab a))) => [|a' l IH /=] //.
  case: ifP => //.
  case: a' => []//[]// a' ??.
  rewrite foldl_min_cons /=.
  move: IH; set T := (foldl minn _  _).
  case: T => // ?.
  by rewrite minnSS.
Qed.

Lemma min_stab_in a y :
  y \in stab a -> 0 != y ->
  min_stab a \in (filter (fun x => x > 0)%N (map (@nat_of_ord _) (enum (stab a)))).
Proof.
  case: y => y Hy1 Hy2 y0.
  apply/foldl_minn_in/hasP/ex_intro2/Hy1.
  rewrite mem_filter lt0n eq_sym y0.
  have->: y = Ordinal Hy1 by [].
  by rewrite mem_map ?mem_enum ?Hy2 // => *; apply/val_inj.
Qed.

Lemma min_stab_min a y :
  y \in stab a -> 0 != y -> (min_stab_ord a <= y)%N.
Proof.
  rewrite -mem_enum /min_stab_ord /min_stab /=.
  elim: (enum (pred_of_set (stab a))) => // ?? IH.
  rewrite !in_cons /= lt0n => /orP [/eqP <-|/IH {IH} IH /IH {IH}].
   rewrite eq_sym => ->.
   by rewrite foldl_min_cons geq_minl.
  case: ifP => // a0 H.
  apply/leq_trans/H.
  by rewrite foldl_min_cons geq_minr.
Qed.

Lemma min_stab_cond a b y :
  y \in stab a -> 0 != y ->
  t ^+ (b * min_stab a)%N * a == a.
Proof.
  move=> ys y0.
  have H1: t ^+ (min_stab a) * a == a.
   suff: min_stab a \in (filter (fun x => x > 0)%N
                                (map (@nat_of_ord _) (enum (stab a)))).
    have->: min_stab a = min_stab_ord a by [].
    rewrite mem_filter mem_map.
     by rewrite mem_enum inE => /andP [].
    by move=> ?? H; apply/val_inj/H.
   apply: (@min_stab_in _ _ ys y0).
  elim: b => [|b IHb]; first by rewrite !mul0n GRing.mul1r.
  rewrite mulSn GRing.exprD -GRing.mulrA.
  by move/eqP: IHb => ->.
Qed.

Lemma min_stab_dvd a x : x \in stab a -> (min_stab a %| x)%N.
Proof.
  case x0: (0 == x); first by move/eqP: x0 => <-.
  move/negP/negP: x0 => x0 H; move: (H).
  rewrite inE (divn_eq x (min_stab a)) addnC GRing.exprD
  -GRing.mulrA (eqP (@min_stab_cond a (x %/ min_stab a) x H x0)) => H0.
  rewrite dvdn_addr ?dvdn_mull //.
  case x0': (0 != @mod_ord (min_stab a) _ x).
   have: @mod_ord (min_stab a) _ x \in stab a by rewrite inE H0.
   move/(fun x => @min_stab_min a _ x x0') => H1.
   suff: false by [].
   move: (@ltn_pmod x _ (min_stab_gt0 a)).
   by rewrite ltnNge H1.
  move/negP/negP: x0'; rewrite /= eq_sym => /dvdnP [] ? ->;
  by rewrite modnMl.
Qed.

Lemma min_stab_neq1 a y :
y \in stab a -> 0 != y ->
one_ord \notin pred_of_set (stab a) -> min_stab a == 1%N = false.
Proof.
  move=> Hy Hy' H; apply/eqP/eqP; move: H; apply: contra => /eqP H.
  have->: one_ord = min_stab_ord a by apply/val_inj; rewrite /= H.
  rewrite inE /=.
  move: (@min_stab_cond a 1 y Hy Hy').
  by rewrite mul1n.
Qed.

Lemma min_stab_attain :
  p_ord \in stab t -> min_stab t == (2 ^ m - 1)%N ->
forall l k : nat, t ^+ l * t = t ^+ k * t -> k = l %[mod 2 ^ m - 1].
Proof.
move=> H1 H3.
have H2: t ^+ (2 ^ m) == t
 by move: H1; rewrite inE /= -GRing.exprSr subn1 prednK.
have base: forall l, (0 < l < 2 ^ m - 1)%N -> t ^+ l * t != t.
 move/eqP: H3 => H l /andP [] Hl0 Hl; apply/negP => /eqP C.
  have Hl': (l < (2 ^ m).+1)%N.
   by apply (ltn_trans Hl).
  have: Ordinal Hl' \in enum (stab t)
   by rewrite mem_enum inE /= C.
  have Hl2: (l < 2 ^ m - 1)%N.
   by apply/(leq_trans Hl).
  rewrite lt0n eq_sym in Hl0.
  rewrite mem_enum.
  move/min_stab_min.
 by rewrite /= Hl0 H leqNgt Hl2 => /implyP.
have base1:
  forall l k, (l < 2 ^ m - 1 -> 0 < k < 2 ^ m - 1 ->
  (t ^+ l * t = t ^+ k * t)%R -> k = l)%N.
 move=> l k.
 case kl: (k == l %[mod (2 ^ m - 1)])%N.
  move: kl => + Hl1 /andP [] Hk1 Hk2.
  by rewrite !modn_small // => /eqP ->.
 move=> Hl Hk2.
 case kl': (k > l)%N.
  have: (0 < l + (2 ^ m - 1 - k) < 2 ^ m - 1)%N.
   apply/andP; split.
    rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
    move: l0 mk kl => ->.
    rewrite subn_eq0 leqNgt.
    by case/andP: Hk2 => ? ->.
   case/andP: Hk2 => ? Hk2.
   rewrite addnBA; last by apply ltnW.
   rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
   apply/andP; split.
    by rewrite lt0n subn_eq0 -ltnNge.
   by apply/(leq_ltn_trans (leq_subr _ _)).
  move/base => + lk.
  rewrite addnC GRing.exprD -GRing.mulrA lk GRing.mulrA -GRing.exprD subnK.
   by rewrite ?subn1 -GRing.exprSr prednK // H2.
  by case/andP: Hk2 => ??; rewrite ltnW.
 move/negP/negP: kl'; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP ->|] // kl'.
 have: (0 < k + (2 ^ m - 1 - l) < 2 ^ m - 1)%N.
  apply/andP; split.
   rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
   move: l0 mk kl => ->.
   by rewrite subn_eq0 leqNgt Hl.
  rewrite addnBA; last by apply ltnW.
  rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
  apply/andP; split.
   by rewrite lt0n subn_eq0 -ltnNge.
  by apply/(leq_ltn_trans (leq_subr _ _)).
 move/base => + lk.
 rewrite addnC GRing.exprD -GRing.mulrA -lk GRing.mulrA -GRing.exprD subnK //.
  by rewrite subn1 -GRing.exprSr prednK // H2.
 by rewrite ltnW.
have base2:
  forall l k : nat, (0 < k < 2 ^ m - 1)%N ->
  t ^+ l * t = t ^+ k * t -> (k = l %% (2 ^ m - 1))%N.
  move=> l k /base1 b.
  rewrite [X in (_ ^+ X * _)%R](divn_eq l (2 ^ m - 1)) addnC GRing.exprD
          -GRing.mulrA.
  move/eqP: H3 (min_stab_cond (l %/ (2 ^ m - 1)) H1 predpower_neq0) =>
            -> /eqP -> /b; apply.
  by rewrite ltn_mod.
move=> l k.
rewrite (divn_eq k (2 ^ m - 1)) addnC GRing.exprD -GRing.mulrA.
move: (min_stab_cond (k %/ (2 ^ m - 1)) H1 predpower_neq0).
move/eqP: (H3) => -> /eqP ->.
rewrite addnC modnMDl modn_mod.
case k0: (k %% (2 ^ m - 1))%N.
 case l0: (l %% (2 ^ m - 1))%N => //.
 rewrite (divn_eq l (2 ^ m - 1)) addnC GRing.exprD -GRing.mulrA.
 move: (min_stab_cond (l %/ (2 ^ m - 1)) H1 predpower_neq0).
 move/eqP: (H3) => -> /eqP -> /esym/base2.
 by rewrite ltn_mod l0 /= mod0n => ->.
move/base2.
by rewrite /= -k0 ltn_mod; apply.
Qed.

Lemma map_pi_inj :
(forall l k : nat, t ^+ l * t = t ^+ k * t -> k = l %[mod 2 ^ m - 1])
-> injective (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => t ^+ x * t).
Proof.
  move=> H x y /eqP.
  rewrite eqE /= => /eqP /H.
  case: y => y yH.
  case: x => x xH.
  rewrite !modn_small //=.
  by move=> yx; apply/val_inj.
  apply: (leq_trans xH); by rewrite prednK.
  apply: (leq_trans yH); by rewrite prednK.
Qed.

Lemma Xn_phi_neq0 (a : nat) :
(forall l k : nat, t ^+ l * t = t ^+ k * t -> k = l %[mod 2 ^ m - 1])
-> t ^+ a * t != 0.
Proof.
  move=> H0; apply/negP => /eqP Hc.
  move: (H0 a a.+1).
  rewrite GRing.exprS -GRing.mulrA Hc GRing.mulr0 => /(_ erefl)/eqP.
  rewrite (divn_eq a (2 ^ m - 1)) -addnS !modnMDl.
  by apply/negP/lem1 => //; rewrite ltn_mod.
Qed.
End order.
