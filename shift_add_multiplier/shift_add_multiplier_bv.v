Require Import Lia.
From stdpp Require Import base.
From stdpp Require Import bitvector.

(* - Start with accumulator C = 0 (2n bits)
   - For each bit of multiplier B (from LSB to MSB):
      - Shift C left by 1 bit FIRST
      - If current LSB of B is 1, add multiplicand A to C
      - Shift B right by 1 bit (to examine next bit)
   - After n iterations, C contains the product
*)

Lemma bv_shiftr_add {n : N} (b : bv n) (s1 s2 : bv n) :
  (bv_unsigned s1 + bv_unsigned s2 < Z.of_N n)%Z ->
  bv_shiftr (bv_shiftr b s1) s2 = bv_shiftr b (bv_add s1 s2).
Proof.
  (* intros Hrange.
  apply bv_eq.
  
  repeat rewrite bv_shiftr_unsigned.

  rewrite Z.shiftr_shiftr by (bv_saturate; lia).
  
  rewrite bv_add_unsigned.
  f_equal.
  - rewrite bv_wrap_small.
    split.
    * bv_saturate. rewrite Hrange. Search bv_modulus.
      unfold bv_modulus.
      apply (Z.lt_trans _ (Z.of_N n)); [exact Hrange|].
      apply Z.log2_lt_pow2; [lia|].
      apply Z.log2_lt_lin; lia.
  - reflexivity. *)
Admitted.

Lemma bv_unsigned_Z_to_bv (m : N) (z : Z) :
  (0 <= z < 2 ^ Z.of_N m)%Z ->
  bv_unsigned (Z_to_bv m z) = z.
Proof.
  intros. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  apply Z.mod_small. apply H.
Qed.

(* Helper lemma: n > 0 implies Z.of_N n >= 1 *)
Lemma Z_of_N_pos (n : N) :
  (n > 0)%N -> (Z.of_N n >= 1)%Z.
Proof.
Admitted.

Section WithContext.
    Context {n: N}.
    Context {pf_n_gt_zero: (n > 0)%N}.

Record Multiplier :=
{ OperandA : bv n;
  OperandB : bv n;
  C        : bv (n + n);
  i        : bv n;
  is_done  : bool
}.
Arguments Multiplier : clear implicits.

(* Extract the least significant bit using bitwise AND with 1 *)
Definition bv_lsb (b : bv n) : bv n :=
  bv_and b (Z_to_bv n 1).

(* Check if LSB is 1 by comparing with 1 *)
Definition bv_lsb_is_one (b : bv n) : bool :=
  if decide (bv_lsb b = Z_to_bv n 1) then true else false.

(* Constants *)
Definition bv_one : bv n := Z_to_bv n 1.

(* Initial state for given operands A and B *)
Definition init_multiplier (a b : bv (n)) : Multiplier :=
  {| OperandA := a;
     OperandB := b;
     C        := Z_to_bv (n + n) 0;    (* 0 in 2n bits *)
     i        := Z_to_bv (n) 0;          (* start at iteration 0 *)
     is_done  := false
  |}.

(* shift-and-add step:
   - Shift C left by 1 bit first
   - Extract LSB of B using bitwise AND
   - If LSB is 1, add A (zero-extended to 2n bits) to C
   - Shift B right by 1 bit
   - Increment iteration counter as bitvector
*)
Definition shift_and_add_step (st : Multiplier) : Multiplier :=
  (* Shift C left first *)
  let C_shifted : bv (n + n) := 
    bv_shiftl (st.(C)) (Z_to_bv (n + n) 1)
  in
  let lsb_check := bv_lsb_is_one (st.(OperandB)) in
  let A_ext : bv (n + n) := bv_zero_extend _ (st.(OperandA)) in
  let C_with_A :=
    if lsb_check
    then bv_add C_shifted A_ext
    else C_shifted
  in
  if (st.(is_done))
  then st
  else 
    {| OperandA := st.(OperandA);
      OperandB := bv_shiftr st.(OperandB) (Z_to_bv n 1);  (* Shift B right by 1 *)
      C        := C_with_A;
      i        := bv_add (st.(i)) (@bv_one);   (* Increment counter *)
      is_done  := if (decide ((st.(i)) = Z_to_bv _ (Z.of_N(n-1)))) then true else false
    |}.

(* Iterate the step function n times *)
Fixpoint iter {A} (k : nat) (f : A -> A) (x : A) : A :=
  match k with
  | O    => x
  | S k' => iter k' f (f x)
  end.

(* n-step shift-and-add multiplier *)
Definition shift_and_add_multiplier (k : nat) (a b : bv n) : bv (n + n) :=
  let st0 := init_multiplier a b in
  let stf := iter k (shift_and_add_step) st0 in
  C stf.


Definition partial_mul (a b : Z) (i : Z) :=
  (a * (b mod (2^i)))%Z.

Open Scope Z_scope.
Inductive Invariant (st: Multiplier) (a b : bv n) : Prop :=
  | CaseDone:
      st.(is_done) = true ->
      bv_unsigned st.(C) = bv_unsigned a * bv_unsigned b ->
      Invariant st a b
  | CaseBusy:
      st.(is_done) = false ->
      st.(OperandA) = a ->
      st.(OperandB) = bv_shiftr b st.(i) ->
      0 <= bv_unsigned(i st) < Z.of_N n ->
      bv_unsigned st.(C) = partial_mul (bv_unsigned a) (bv_unsigned b) (bv_unsigned(st.(i))) ->
      Invariant st a b.

Lemma partial_mul_correct :
  forall a b i,
  0 <= i ->
  partial_mul a b (i+1) =
  partial_mul a b (i) + a * (if (Z.testbit b i) then 1 else 0) * 2^i.
Proof.
Admitted.

Lemma partial_mul_rewrite :
  forall (a b i : bv n) (C : bv (n+n)),
  bv_unsigned (C) = partial_mul (bv_unsigned a) (bv_unsigned b) (bv_unsigned (i)) ->
  Z_to_bv _ (partial_mul (bv_unsigned a) (bv_unsigned b) (bv_unsigned (i + bv_one))) = 
    if bv_lsb_is_one (bv_shiftr b i)
    then
      (C ≪ Z_to_bv (n + n) 1 + bv_zero_extend (n + n) a)%bv
    else (C ≪ Z_to_bv (n + n) 1)%bv.
Proof.
Admitted.

Lemma mul_to_partial_mul :
  forall a b i,
  0 <= b < 2^i ->
  a * b = partial_mul a b i.
Proof.
  unfold partial_mul. intros a b i0 HGreater. rewrite Zmod_small.
  - reflexivity.
  - auto.
Qed.

Search bv_modulus.

Lemma n_gt_0_pow_gt_1:
  forall n, (n > 0)%N -> 2^(Z.of_N n) > 1.
Proof.
  intros. rewrite Z.gt_lt_iff. apply Z.pow_gt_1. lia. lia.
Qed.

Lemma n_le_pow_of_2:
  forall n, n >= 0 -> n < 2^n.
Proof.
  intros. apply Z.pow_gt_lin_r. lia. lia.
Qed.

Lemma shift_and_add_step_correct :
  forall st a b, Invariant st a b -> Invariant (shift_and_add_step st) a b.
Proof.
  intros *. intros HInv. destruct HInv.
  - unfold shift_and_add_step. rewrite H. apply CaseDone.
    + auto.
    + auto.
  - unfold shift_and_add_step. rewrite H. rewrite H0. rewrite H1.
  rewrite <- partial_mul_rewrite; auto. case_decide.
    + apply CaseDone. simpl. reflexivity. simpl.
    rewrite mul_to_partial_mul with (i := bv_unsigned(i st + bv_one)).
    rewrite Z_to_bv_small; auto.
      * unfold partial_mul. rewrite Zmod_small.
        ** rewrite bv_modulus_add.
          pose proof (bv_unsigned_in_range _ a).
          pose proof (bv_unsigned_in_range _ b).
          split. lia. apply Zmult_lt_compat; lia.
        ** rewrite H4. unfold bv_one. rewrite bv_add_unsigned.
          rewrite Z_to_bv_unsigned. rewrite Z_to_bv_unsigned.
          rewrite bv_wrap_add_idemp.
          replace (Z.of_N (n-1) + 1) with (Z.of_N n) by lia.
          split. bv_saturate. lia. replace (bv_wrap n  (Z.of_N n)) with (Z.of_N n).
          *** bv_saturate. unfold bv_modulus in *. apply H5.
          *** unfold bv_wrap. unfold bv_modulus.
              assert (Z.of_N n < 2 ^ Z.of_N n).
              {
                rewrite Z.log2_lt_pow2. apply Z.log2_lt_lin. lia. lia.
              }
              symmetry. apply Z.mod_small. lia.
      * rewrite H4 in *. unfold bv_one. rewrite bv_add_unsigned.
        rewrite Z_to_bv_unsigned. rewrite Z_to_bv_unsigned.
        rewrite bv_wrap_add_idemp.
        replace (Z.of_N (n - 1) + 1) with (Z.of_N n) by lia.
        replace (bv_wrap n (Z.of_N n)) with (Z.of_N n).
        ** bv_saturate. unfold bv_modulus in *. lia.
        ** unfold bv_wrap, bv_modulus. symmetry. apply Z.mod_small. split.
          *** lia.
          *** apply Z.log2_lt_pow2; try lia.
              apply Z.log2_lt_lin; lia.
    + apply CaseBusy.
      * simpl. reflexivity.
      * reflexivity.
      * simpl. 
        unfold bv_one.
        apply bv_eq. 
        rewrite <- bv_shiftr_add. reflexivity.
        destruct H2 as [_ Hi_lt_n].
        assert (
          bv_unsigned (i st) < Z.of_N (n - 1) \/
          bv_unsigned (i st) = Z.of_N (n - 1)
        ) by lia.
        
        assert (bv_unsigned (i st) <> Z.of_N (n - 1)). intro H_equal. apply H4.
        apply bv_eq. rewrite bv_unsigned_Z_to_bv. apply H_equal. split.
        ** lia.
        ** Search Z.log2. rewrite <- H_equal in H4. rewrite Z_to_bv_bv_unsigned in H4. contradiction.
        ** rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Zmod_small. lia.
        pose proof (bv_modulus_gt_1 n). split. lia. apply bv_modulus_gt_1. lia.
      * cbn. rewrite bv_add_unsigned.
        pose proof (n_gt_0_pow_gt_1 n pf_n_gt_zero).
        assert (Z.of_N n >= 0) as H_ge_0 by lia.
        pose proof (n_le_pow_of_2 (Z.of_N n) H_ge_0).
        {
          rewrite bv_wrap_small. split. Search (bv_unsigned _).
          - apply Z.add_nonneg_nonneg. lia. apply bv_unsigned_in_range.
          - apply bv_neq in H4. rewrite bv_unsigned_Z_to_bv in H4. unfold bv_one.
            rewrite bv_unsigned_Z_to_bv; lia. lia.
          - unfold bv_modulus. unfold bv_one. rewrite bv_unsigned_Z_to_bv by lia.
            apply bv_neq in H4. rewrite bv_unsigned_Z_to_bv in H4; lia.
        }
      * cbn. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small. reflexivity.
        unfold partial_mul. unfold bv_modulus.
        assert (0 <= bv_unsigned b `mod` 2 ^ bv_unsigned (i st + bv_one) < 2 ^ bv_unsigned (i st + bv_one)).
        Search (_ `mod` ?a < ?a).
        apply Z.mod_pos_bound. apply Z.pow_pos_nonneg. lia. destruct H2.
        rewrite H2. unfold bv_one. rewrite bv_add_unsigned. unfold bv_wrap. unfold bv_modulus.
        set (u := bv_unsigned (i st)).
        set (M := 2 ^ Z.of_N n).
        assert (Hone : bv_unsigned (Z_to_bv n 1) = 1).
        {
          apply bv_unsigned_Z_to_bv.
          split; [lia|].
          subst M.
          pose proof (n_gt_0_pow_gt_1 n pf_n_gt_zero) as Hgt1.
          lia.
        }

        rewrite Hone.
        subst u M.
        assert (Hrange :
          0 <= bv_unsigned (i st) + 1 < 2 ^ Z.of_N n).
        {
          split; [lia|].
          assert (Hn_lt_pow : Z.of_N n < 2 ^ Z.of_N n).
          { apply Z.pow_gt_lin_r; lia. }
          lia.
        }
        rewrite (Z.mod_small (bv_unsigned (i st) + 1) (2 ^ Z.of_N n)) by exact Hrange.
        lia.
        
        set (A := bv_unsigned a).
        set (M := bv_unsigned b `mod` 2 ^ bv_unsigned (i st + bv_one)).

        pose proof (bv_unsigned_in_range n a) as HA.
        pose proof (bv_unsigned_in_range n b) as HB.

        (* split Goal: lower and upper *)
        split.
        apply Z.mul_nonneg_nonneg. subst A; exact (proj1 HA). subst M; exact (proj1 H5).

        assert (HMle : M <= bv_unsigned b).
        {
          subst M.
          apply Z.mod_le.
          - exact (proj1 HB).
          - apply Z.pow_pos_nonneg. lia. unfold bv_one. rewrite bv_add_unsigned. unfold bv_wrap. lia.
        }

        assert (HAm_le : A * M <= A * bv_unsigned b).
        {
          apply Z.mul_le_mono_nonneg_l.
          - subst A; exact (proj1 HA).
          - exact HMle.
        }

        assert (HAb_lt : A * bv_unsigned b < bv_modulus n * bv_modulus n).
        {
          eapply Z.mul_lt_mono_nonneg.
          - subst A; exact (proj1 HA).
          - subst A. lia.
          - lia.
          - exact (proj2 HB).
        }

        assert (HAm_lt : A * M < bv_modulus n * bv_modulus n).
        { eapply Z.le_lt_trans; [exact HAm_le | exact HAb_lt]. }
        unfold bv_modulus in HAm_lt.
        unfold bv_modulus.

        rewrite N2Z.inj_add.
        rewrite Z.pow_add_r by lia.
        exact HAm_lt.
Qed.

Print iter.
Lemma iter_commute:
  forall (A : Type) (k : nat) (f : A → A) (x : A),
  f (iter k f x) = iter k f (f x).
Proof.
  induction k. cbn. reflexivity. cbn. intros. rewrite IHk. reflexivity.
Qed.


Lemma shift_and_add_constant_time':
  forall (a b : bv n),
  let st0 := init_multiplier a b in
  (* let stn := iter (N.to_nat n) shift_and_add_step st0 in
  is_done stn = true. *)

  let stn m := iter m shift_and_add_step st0 in
  forall (m : nat),
  Invariant (stn m) a b.
Proof.
  induction m.
  {
    unfold stn. unfold st0. simpl. unfold init_multiplier.
    apply CaseBusy; simpl; auto.
    * apply bv_eq. rewrite bv_shiftr_unsigned. rewrite Z.shiftr_0_r. reflexivity.
    * rewrite bv_unsigned_Z_to_bv; lia.
    * rewrite bv_unsigned_Z_to_bv; [| lia]. unfold partial_mul. rewrite Z_to_bv_unsigned.
      unfold bv_wrap. rewrite Zmod_0_l. rewrite Z.pow_0_r. rewrite Z.mod_1_r. lia.
  }
  unfold stn. unfold st0. simpl. apply shift_and_add_step_correct in IHm.
  unfold stn in *. unfold st0 in *.
  rewrite <- (iter_commute Multiplier m shift_and_add_step (init_multiplier a b)).
  exact IHm.
Qed.

End WithContext.


Compute shift_and_add_multiplier 4 (Z_to_bv 4 13) (Z_to_bv 4 9).
Compute shift_and_add_multiplier 3 (Z_to_bv 4 13) (Z_to_bv 4 9).
Compute shift_and_add_multiplier 5 (Z_to_bv 4 13) (Z_to_bv 4 9).
Compute shift_and_add_multiplier 10 (Z_to_bv 4 13) (Z_to_bv 4 9).
