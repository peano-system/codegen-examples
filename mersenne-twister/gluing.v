From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import mt cycle BinNat BinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma break_if (T : 'F_2) :
  (if T == 1%R then 1%R else 0%R) = T.
Proof.
  case: ifP => [/eqP/esym //|].
  case: T => [][|[]]// *.
  by apply/val_inj.
Qed.

Lemma if_xorb (T1 T2 : bool)  :
  (if xorb T1 T2 then 1%R else 0%R : 'F_2) =
  ((if T1 then 1%R : 'F_2 else 0%R) + (if T2 then 1%R else 0%R))%R.
Proof.
  case: T1 T2 => [][]//=.
   by rewrite GRing.addrr_char2.
  by rewrite GRing.addr0.
Qed.

Local Open Scope N_scope.

Section gluing.
Variable (w n r m a : N).
Hypothesis rw : (r < w)%nat.
Hypothesis nmn : ((n - m).+1 < n.-2)%nat.
Hypothesis nm : (0 < n - m)%nat.
Hypothesis r0 : (0 < r)%nat.
Hypothesis nwr : (2 < n * w - r)%nat.
Hypothesis pm : prime (2 ^ (n * w - r) - 1).

Lemma w0 : (0 < w)%nat.
Proof.
  case: (nat_of_bin r) rw => // r'.
  by apply/ltn_trans.
Qed.

Hint Resolve w0 : core.

Definition N_of_word (t : w.-tuple 'F_2) :=
  foldr (fun x y => 2*y + x) 0
        (map_tuple (fun x => if (x == 1 :> 'F_2)%R then 1%N else 0) t).

Fixpoint word_of_N_iter (fuel : nat) (p : positive) : seq 'F_2 :=
  match fuel, p with
  | f.+1, xI p0 => 1%R :: word_of_N_iter f p0
  | f.+1, xO p0 => 0%R :: word_of_N_iter f p0
  | f.+1, xH => 1%R :: map (fun _ => 0%R) (iota 0 f)
  | 0%nat, _ => [::]
  end.

Definition zero_size : size (map (fun _ => (0%R : 'F_2)) (iota 0 w)) == w.
Proof. by rewrite size_map size_iota. Qed.
Definition zero := Tuple zero_size.

Lemma word_of_N_iter0 p : size (word_of_N_iter 0 p) == 0.
Proof. by []. Qed.

Lemma size_word_of_N_iter p : size (word_of_N_iter w p) == w.
Proof.
  elim: (nat_of_bin w) p => // w' IH p.
  case: p => [p|p|].
    by rewrite /= (eqP (IH _)).
   by rewrite /= (eqP (IH _)).
  by rewrite /= size_map size_iota.
Defined.

Definition word_of_N (n' : N) :=
  match n' with
  | N0 => zero
  | N.pos p => Tuple (size_word_of_N_iter p)
  end.

Lemma word_of_N0 d (i : 'I_w) : nth d (word_of_N 0) i = 0%R.
Proof.
  case: i => //= i iw.
  by rewrite (nth_map 0%nat) // size_iota.
Qed.

Lemma bin_of_add_nat n1 n2 :
  bin_of_nat n1 + bin_of_nat n2 = bin_of_nat (n1 + n2)%nat.
Proof.
  apply: (can_inj nat_of_binK).
  by rewrite bin_of_natK nat_of_add_bin !bin_of_natK.
Qed.

Lemma succ_nat i : bin_of_nat i.+1 = N.succ (bin_of_nat i).
Proof.
  elim: i => // i IH.
  by rewrite -addn1 -bin_of_add_nat IH N.add_1_r.
Qed.

Lemma Num_succ i : [Num of i] + 1 = [Num of i.+1].
Proof. by rewrite N.add_1_r succ_nat. Qed.

Lemma pos_Num i : 0 <= [Num of i].
Proof. by case: i. Qed.

Lemma nat_of_pos_pred i : (nat_of_pos i).-1 = nat_of_bin (Pos.pred_N i).
Proof.
  elim: i => // i IH; rewrite /= natTrecE.
  case: i IH => //= p; rewrite /= ?natTrecE // => <-.
  rewrite -!subn1 doubleB subn2 subn1 prednK //.
  have: (nat_of_pos p > 0)%nat.
   elim: p => //= p IH.
   rewrite natTrecE.
   by case: (nat_of_pos p) IH.
  by case: (nat_of_pos p).
Qed.

Lemma pos_of_nat_pred_succ i : Pos.pred_N (pos_of_nat i i) = bin_of_nat i.
Proof.
  apply: (can_inj nat_of_binK).
  rewrite bin_of_natK -nat_of_pos_pred.
  have->: nat_of_pos (pos_of_nat i i) = nat_of_bin (bin_of_nat i.+1) by [].
  by rewrite bin_of_natK.
Qed.

Lemma nth_word_of_N x d (i : 'I_w) :
  nth d (word_of_N x) i =
  if N.testbit x [Num of (val i)]
  then 1%R : 'F_2 else 0%R.
Proof.
case: x; first by rewrite word_of_N0.
rewrite /word_of_N => p.
rewrite -tnth_nth (tnth_nth 0%R).
have->: tval (Tuple (size_word_of_N_iter p)) = word_of_N_iter w p by [].
elim: (nat_of_bin w) i p => [[][]//|] w' IH i p.
case: p => [p|p|].
+ case: i => [][]//= i; rewrite ltnS => i0.
  by move: (IH (Ordinal i0) p) ->; rewrite pos_of_nat_pred_succ.
+ case: i => [][]//= i; rewrite ltnS => i0.
  by move: (IH (Ordinal i0) p) ->; rewrite pos_of_nat_pred_succ.
+ case: i => [][]//= i _.
  by elim: (iota 0 w') i => [*|? l IHl []//]; rewrite nth_default.
Qed.

Hint Resolve pos_Num : core.

Lemma N_of_wordK : cancel N_of_word word_of_N.
Proof.
  move=> x; apply/eq_from_tnth => j.
  rewrite (tnth_nth 0%R) nth_word_of_N /N_of_word.
  set T := (fun x0 y : N => 2 * y + x0).
  case: x j => x xH [] i iH.
  rewrite (tnth_nth 0%R) /= => {xH iH}.
  elim: x i => [?|x0 x IH i].
   by rewrite nth_default.
  case: i => [|i].
   case: x0 => [][|[]]//= i.
    rewrite /T /= N.add_0_r N.testbit_even_0.
    by apply/val_inj.
   rewrite /T /= N.testbit_odd_0.
   by apply/val_inj.
  rewrite succ_nat /= N.testbit_succ_r_div2.
  have->: (N.div2 (T (if x0 == 1%R then 1 else 0)
                  (foldr T 0 [seq (if x1 == 1%R then 1 else 0) | x1 <- x])))
        = (foldr T 0 [seq (if x1 == 1%R then 1 else 0) | x1 <- x]).
   rewrite /T.
   case: (x0 == 1%R).
    by rewrite -N.succ_double_spec N.div2_succ_double.
   by rewrite N.add_0_r -N.double_spec N.div2_double.
  rewrite IH //.
  by elim: i.
Qed.

Lemma N_of_word_last v : N.testbit (N_of_word v) [Num of w] = false.
Proof.
  case: v => v i; rewrite /N_of_word; set T := [Num of w].
  have-> /=: T = [Num of (size v)] by rewrite (eqP i).
  have: (size v > 0)%nat by rewrite (eqP i).
  elim: v {i T} => // ? l IHl _.
  case l0: (size l).
   rewrite /= l0.
   move/size0nil:l0 => -> /=.
   by case: ifP.
  rewrite succ_nat /=.
  case: ifP.
   rewrite N.testbit_odd_succ ?IHl -/size ?l0 //.
  by rewrite N.add_0_r N.testbit_even_succ ?IHl -/size ?l0 //.
Qed.

Definition N_of_vector (x : 'rV['F_2]_w) := N_of_word (mktuple (x ord0)).
Definition vector_of_N n := (\row_i (tnth (word_of_N n) i))%R.

Lemma N_of_vectorK : cancel N_of_vector vector_of_N.
Proof.
  move=> x.
  rewrite /N_of_vector /vector_of_N N_of_wordK.
  apply/rowP => i.
  by rewrite mxE tnth_mktuple.
Qed.

Local Notation ai := (@array_incomplete w n (n - m) r nmn nm r0 rw nwr).
Local Notation ia := (@incomplete_array w n (n - m) r nmn nm r0 rw).

Definition array_of_state (y : random_state) :=
  ia (\matrix_(i, j) nth 0%R (nth (word_of_N 0)
      [seq (@rev_tuple _ _ \o word_of_N) i | i <- rev (rot (index y) (state_vector y))] i) j)%R.

Definition state_of_array (y : 'rV['F_2]_(n * w - r)) :=
  {| index:=0;
     state_vector:=rev (map (N_of_word \o (@rev_tuple _ _))
      (mktuple (fun j => mktuple (fun x => ai y j x))));|}.

Lemma state_of_arrayK : cancel state_of_array array_of_state.
Proof.
  move=> x.
  rewrite /array_of_state /state_of_array rot0.
  set T := (\matrix_(_, _) _)%R; have->: T = (ai x)%R.
   apply/matrixP => i j; subst T.
   rewrite !mxE !revK (nth_map 0) /=; last by rewrite 2!size_map size_enum_ord.
   rewrite (nth_map (word_of_N 0)) /=; last by rewrite size_tuple card_ord.
   by rewrite N_of_wordK ?revK ?nth_mktuple ?(castmxE, mxE).
  by rewrite array_incompleteK.
Qed.

Local Notation B := (@B w n (n - m) r (rev_tuple (word_of_N a)) nmn nm r0 rw).
Local Notation next_random_state := (next_random_state n m r a).
Definition computeB :=
  array_of_state \o snd \o next_random_state \o state_of_array.

Lemma size_next_random_state v :
size (state_vector (next_random_state (state_of_array v)).2) = n.
Proof.
rewrite /next_random_state size_set_nth size_tuple.
by case: (nat_of_bin n) nm => []//[].
Qed.

Lemma index_next_random_state v :
index (next_random_state (state_of_array v)).2 = 1.
Proof.
  have: n != 1.
   apply/eqP => n1.
   move: n1 nmn => ->.
   by rewrite ltn0.
  by case: n => []//[]//.
Qed.

Lemma nth_next_random_state v i :
  nth 0 (state_vector (next_random_state (state_of_array v)).2) i.+1%N
= nth 0 (state_vector (state_of_array v)) i.+1.
Proof. by rewrite nth_set_nth. Qed.

Lemma nth_state_vector v (i : 'I_n) :
  nth 0 (state_vector (state_of_array v)) i =
  N_of_word (rev_tuple (mktuple (ai v (rev_ord i)))).
Proof.
rewrite nth_rev; last by rewrite 2!size_map size_enum_ord.
rewrite (nth_map (word_of_N 0)) size_map size_tuple ; last by rewrite rev_ord_proof.
have ord0n: 'I_n.
 case: (nat_of_bin n) nmn => // *.
 by apply ord0.
have ord0w: 'I_w.
 case: (nat_of_bin w) w0 => // *.
 by apply ord0.
rewrite (nth_map ord0n) ?size_tuple ?rev_ord_proof //.
congr N_of_word.
apply/eq_from_tnth => j.
rewrite !(tnth_nth ord0) !nth_rev ?size_tuple //
        !(nth_map ord0w) ?size_tuple ?rev_ord_proof
        ?(esym (enumT _), size_enum_ord, rev_ord_proof) //.
by congr (ai _ _); apply/ord_inj; rewrite /= nth_enum_ord ?rev_ord_proof.
Qed.

Lemma testbit_N_of_word v a' :
  N.testbit (N_of_word v) [Num of val a'] = (tnth v a' == 1%R).
Proof.
rewrite (tnth_nth 0%R) -[in RHS](N_of_wordK v) nth_word_of_N.
by case: ifP.
Qed.

Local Lemma tns v b a' (Ha : (a' < w)%nat) (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of a']
= (ai v (rev_ord (Ordinal Hb)) (rev_ord (Ordinal Ha)) == 1%R).
Proof.
  have ord0w: 'I_w.
   case: (nat_of_bin w) w0 => // *.
   by apply ord0.
  have H: b = val (Ordinal Hb) by [].
  rewrite [in LHS]H nth_state_vector.
  have {H} H : a' = val (Ordinal Ha) by [].
  rewrite [in LHS]H testbit_N_of_word (tnth_nth ord0) nth_rev ?size_tuple //
          (nth_map ord0w) ?size_tuple ?rev_ord_proof //.
  congr (_ == _); congr (ai _ _); apply/ord_inj.
  by rewrite nth_enum_ord ?rev_ord_proof.
Qed.

Local Lemma tnsw v b (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of w] = false.
Proof.
  by rewrite /state_of_array /= nth_rev ?(size_enum_ord, size_map) //
          (nth_map (word_of_N 0%N)) ?(size_enum_ord, size_map)
          ?(rev_ord_proof (Ordinal Hb)) // N_of_word_last.
Qed.

Notation upper_mask := (N.shiftl 1 r).
Notation lower_mask := (upper_mask - 1).

Lemma ltP' i p : reflect ([Num of i] < [Num of p]) (i < p)%nat.
Proof.
  apply/(iffP idP).
   elim: p i => // p IH []// i.
   rewrite ltnS -!Num_succ => {}/IH H.
   by apply/N.add_lt_le_mono.
  elim: p i => [[]//|p IH []// i].
  by rewrite -!Num_succ -N.add_lt_mono_r ltnS; apply IH.
Qed.

Lemma upper_maskF i : (i < r)%nat -> N.testbit upper_mask [Num of i] = false.
Proof.
  move=> ir.
  rewrite N.shiftl_spec_low // -[r]nat_of_binK.
  by apply/ltP'.
Qed.

Lemma lower_maskT i : (i < r)%nat -> N.testbit lower_mask [Num of i] = true.
rewrite /lower_mask.
Proof. by do 31!(case: i => // i). Qed.

Lemma testbita i :
  (i < r)%nat ->
  (if N.testbit a [Num of i] then 1%R else 0%R) = nth 0%R (word_of_N a) i.
Proof. by do 32!(case: i => // i). Qed.

Lemma computeBE v : computeB v = (v *m B)%R.
Proof.
  rewrite /computeB mulBE /cycle.computeB.
  apply/rowP => i.
  rewrite !mxE ?castmxE ?mxE (nth_map 0)
          ?nth_rev ?size_tuple ?size_rot ?ltn_pmod //
          ?size_rev ?size_rot ?size_next_random_state //.
  set R := row_ind _ _ _.
  have<-: (rev_ord R = w - R.+1 :> nat)%nat by [].
  set I := (cast_ord _ i); subst R.
  rewrite nth_word_of_N /cycle.B index_next_random_state
          ?size_rot ?size_next_random_state ?nth_drop //
          nth_cat size_drop ?size_next_random_state.
  set I' := col_ind _ _ _ _ _.
  case: (splitP I) => j Ij; rewrite /= in Ij; last first.
   have I'0: (I' > 0)%nat.
    by rewrite /= Ij divnDl.
   have->: (n - I'.+1 < n - 1%N)%nat.
    rewrite /leq subn1 subnS.
    case H: (n - I' > 0)%nat.
     by rewrite prednK // subnAC -subn1 subnBA.
    rewrite lt0n in H.
    by move/negP/negP/eqP: H => ->.
   rewrite nth_drop add1n nth_next_random_state tns => *.
     rewrite /leq -!subSn //;last by apply/leqW.
     by rewrite subnAC subSn //.
    by rewrite (rev_ord_proof (Ordinal (@ltn_pmod i w erefl))).
   rewrite break_if !mxE !castmxE.
   congr (v _ _); apply/ord_inj => //.
   rewrite /arr_ind /=.
   set T := cast_ord _ _.
   case: (splitP T) => k /=.
    rewrite Ij 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn.
     rewrite subn2 /= !divnDl // divnn add1n modnDl // -subSn
             ?ltn_mod // subSS subKn; last by rewrite ltnW // ltn_mod.
     by rewrite -divn_eq => ->.
    rewrite divnDl // add1n /leq !subSS subn_eq0.
    case: j {Ij} => j H.
    apply/leq_trans.
     apply leq_div2r.
     by apply H.
    by [].
   rewrite Ij 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn.
    rewrite subn2 /= !divnDl // divnn add1n modnDl // -subSn
            ?ltn_mod // subSS subKn; last by rewrite ltnW // ltn_mod.
    rewrite -divn_eq => jnwr.
    case: j {Ij} jnwr => j H jnwr.
    suff: (n.-1 * w - r < n.-1 * w - r)%nat by rewrite ltnn.
     apply/leq_trans.
      apply: (_ : _ < n * w - r)%nat; first by rewrite ltn_sub2r.
     apply/leq_trans.
      apply: (_ : _ <= n * w - r + k)%nat; first by rewrite leq_addr.
     apply/ltnW.
     by rewrite -jnwr.
    rewrite divnDl // add1n /leq !subSS subn_eq0.
    case: j {Ij} => j H.
    apply/leq_trans.
     apply leq_div2r.
     by apply H.
    by [].

   have->: val I' = 0 by rewrite /= Ij divn_small.
   rewrite subn1 ltnn ?(mxE, castmxE) subnn nth_take // nth_set_nth.
   rewrite !N.lxor_spec // N.shiftr_spec // N.lor_spec !N.land_spec.
   rewrite !if_xorb tns ?(rev_ord_proof (Ordinal (@ltn_pmod i w erefl))) // => Hp.
   rewrite !break_if.
   rewrite mxE -!GRing.addrA.
   congr (_ + _)%R; first congr (v _ _); apply/ord_inj => //.
   rewrite /= /arr_ind; set P := cast_ord _ _.
   case: (splitP P) => l Pl.
    by rewrite /= modn_small ?Ij // 2!subSS subKn // -ltnS in Pl.
   move/eqP: Pl; rewrite /= modn_small ?Ij //.
   have H: (n = n - m.+1 + m.+1)%nat by rewrite subnK.
   rewrite [X in _ == (X * _ - _ + _)%nat]H mulnDl eqn_add2l => /eqP je.
   suff: (w < w)%nat by rewrite ltnn.
   apply/leq_trans/(_ : j < w)%nat => //.
   rewrite 2!subSS // subKn // in je; last by rewrite -ltnS.
   by rewrite ltnS je.

   set R := cast_ord _ _.
   case: (splitP (R : 'I_(1 + w.-1))) => r Rr.
    rewrite /= in Rr.
    case: r Rr => [][]// ? Rr.
    rewrite Num_succ.
    set T := (val (rev_ord _)).+1.
    have->: T = w by rewrite /T /= Ij Rr mod0n subn1.
    rewrite ?tnsw // ?mxE !GRing.add0r.
    set S := cast_ord _ _; case: (splitP S) => s Ss; first by case: s Ss => [][].
    rewrite ?(mxE, castmxE).
    rewrite ?N.lor_spec ?N.land_spec.
    have->: 0 = [Num of 0] by [].
    rewrite ?tns // !mxE /= andbF andbT.
    set L := v _ _; set R0 := v _ _; have<-: L = R0.
     congr (v _ _); apply/ord_inj => //.
     rewrite /arr_ind.
     set T' := cast_ord _ _.
     case: (splitP T') => t //= T't.
     rewrite /= in T't, Ss.
     have-> //: val s = 30.
     rewrite subSn // subnn add1n in Ss.
     by case: Ss.
    rewrite /= Ij Rr mod0n subn1 /=.
    case L1: (L == 1%R).
     rewrite mxE.
     case: (splitP (R : 'I_(1 + w.-1))) => r' Rr'.
      case: r' Rr' => [][]// *.
      by rewrite mxE -GRing.mulr_natr.
     by rewrite /= Rr in Rr'.
    by rewrite mxE.
   (**)
   rewrite !Num_succ !tns.
    rewrite /= in Rr.
    by rewrite /= Ij Rr add1n modn_small ?subSS ?ltnS ?leq_subr // -ltnS //.
    rewrite /= in Rr.
    by rewrite /= Ij Rr add1n modn_small ?subSS ?ltnS ?leq_subr // -ltnS //.
   move=> ? ?.
   rewrite ?N.lor_spec ?N.land_spec.
   have->: 0 = [Num of 0] by [].
   rewrite ?tns // !mxE andbF andbT ?(castmxE, mxE).
   set P := cast_ord _ _; set Q' := cast_ord (esym _) _; set Q := cast_ord (esym _) _.
   case: (splitP Q) => q Qq.
    by case: q Qq => [][]//.
   rewrite /= in Qq.
   case: (splitP P) => p Pp.
    case: p Pp => [][]// p Pp.
    rewrite /= in Pp, Rr.
    set TT := val (rev_ord _).
    have TT30: TT = 30.
     subst TT.
     by rewrite /= Ij Rr Pp addn0 modn_small //.
    have->: N.testbit lower_mask [Num of TT.+1] = false by rewrite TT30.
    have->: N.testbit upper_mask [Num of TT.+1] = true by rewrite TT30.
    rewrite ?(mxE, castmxE) andbT andbF orbF.
    set X := v _ _; set Y := v _ _; set Z := v _ _; set W := v _ _.
    have->: X = Z.
     congr (v _ _); apply/ord_inj => //.
     rewrite /arr_ind /=.
     set Tmp := cast_ord _ _.
     case: (splitP Tmp) => t Tmpt.
      by rewrite -Tmpt /= TT30.
     by rewrite /= TT30 in Tmpt.
    have q30: val q = 30.
     rewrite /= subSn // subnn add1n in Qq.
     by case: Qq.
    have->: Y = W.
     congr (v _ _); apply/ord_inj => //.
     rewrite /arr_ind /=.
     set Tmp := cast_ord _ _.
     case: (splitP Tmp) => t Tmpt //.
     by rewrite -Tmpt /= q30.
    case: (W == 1)%R.
     rewrite mxE.
     case: (splitP (R : 'I_(1 + w.-1))) => r' Rr';
      rewrite /= in Rr'.
      case: r' Rr' => [][]//= ? Rr'.
      by rewrite Rr' in Rr.
     rewrite Rr' !add1n in Rr.
     case: Rr => Rr.
     rewrite TT30 /= mxE /= Rr Pp /=.
     case ZE: (Z == 1)%R.
      by move/eqP: ZE => ->.
     by case: Z ZE => [][]//[]//.
    rewrite mxE TT30 /=.
    by case: Z => [][]//[]//.
   rewrite /= in Pp, Rr.
   have q30: val q = 30.
    rewrite /= subSn // subnn add1n in Qq.
    by case: Qq.
   rewrite ?(mxE, castmxE).
   set A := v _ _.
   set X := v _ _; set Y := v _ _; set Z := v _ _; set W := v _ _.
   have->: X = Z.
    congr (v _ _); apply/ord_inj => //.
    rewrite /= /arr_ind.
    set Tmp := cast_ord _ _.
    case: (splitP Tmp) => t Tmpt.
     rewrite -Tmpt /= Ij Rr Pp.
     rewrite modn_small; last by rewrite -Pp add1n ltnS.
     by rewrite 3!subSS !subnDA subn1 -subnDA subKn subSn // -Pp -ltnS.
    rewrite /= Ij Rr Pp modn_small in Tmpt; last by rewrite -Pp add1n ltnS.
    rewrite 3!subSS !subnDA subn1 -subnDA subKn subSn // -Pp in Tmpt;
     last by rewrite -ltnS.
    suff: (n.-2 * w + r < n.-2 * w + r)%nat by rewrite ltnn.
    rewrite [X in (_ < X)%nat]Tmpt.
    apply/leq_trans.
     apply: (_ : _ < n.-2 * w + w.-1)%nat; first by rewrite ltn_add2l.
    by [].
   have->: W = Y.
    congr (v _ _); apply/ord_inj => //.
    rewrite /= /arr_ind.
    set Tmp := cast_ord _ _.
    case: (splitP Tmp) => t Tmpt //.
    by rewrite -Tmpt /= q30.
   set TT := val (rev_ord _).
   have TTwp2: (TT = gluing.r - p.+2)%nat.
    subst TT.
    by rewrite /= Ij modn_small // Rr Pp subSS.
   have->: N.testbit lower_mask [Num of TT.+1] = true.
    rewrite add1n in Pp.
    rewrite lower_maskT // TTwp2 -subSn.
     by rewrite subSS ?rev_ord_proof.
    by rewrite -Pp.
   have->: N.testbit upper_mask [Num of TT.+1] = false.
    rewrite add1n in Pp.
    rewrite upper_maskF // TTwp2 -subSn.
     by rewrite subSS ?rev_ord_proof.
    by rewrite -Pp.
   rewrite andbF andbT /= break_if.
   case YE: (Y == 1%R).
    rewrite TTwp2 mxE.
    case: (splitP (R : 'I_(1 + w.-1))) => r' Rr';
     rewrite /= in Rr'.
     case: r' Rr' => [][]// ? Rr'.
     by rewrite Rr' in Rr.
    rewrite Rr' !add1n in Rr.
    case: Rr => Rr.
    have->: r' = r by apply/ord_inj.
    have->: p.+1 = r by rewrite Pp.
    rewrite mxE nth_rev ?size_tuple // ?subSS; last by rewrite ltnS.
    rewrite testbita //.
    apply/leq_ltn_trans.
     apply leq_subr.
    by [].
   by rewrite mxE /=.
Qed.
