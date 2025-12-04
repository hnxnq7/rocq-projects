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

Section WithContext.
    Context {n: N}.

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
      * 

End WithContext.

Compute shift_and_add_multiplier 4 (Z_to_bv 4 13) (Z_to_bv 4 9).
Compute shift_and_add_multiplier 3 (Z_to_bv 4 13) (Z_to_bv 4 9).
Compute shift_and_add_multiplier 5 (Z_to_bv 4 13) (Z_to_bv 4 9).
Compute shift_and_add_multiplier 10 (Z_to_bv 4 13) (Z_to_bv 4 9).


(* Correctness *)

(* Lemma bv_shiftr_correct (n : N) (a : bv n) :
  (2 * (bv_unsigned (bv_shiftr a bv_one)))%Z = (bv_unsigned a)%Z.
Proof.
Admitted. *)

(* Proof:
     The algorithm maintains the invariant that after k iterations:
     - C = (sum of A * 2^i for each bit i of B examined so far) * 2^(n-k)
     - The remaining bits of B are in OperandB
     
     After n iterations:
     - All bits of B have been examined
     - C contains the full product
     
     lemmas:
     - bv_shiftr (divides by 2)
     - bv_shiftl (multiplies by 2)
     - bv_add correctness
     - bv_extract for LSB extraction
     - bv_zero_extend correctness
  *)

Theorem shift_and_add_multiplier_correct (n : nat) (a b : bv (N.of_nat n)) :
  bv_unsigned (shift_and_add_multiplier n a b) = 
  (bv_unsigned a * bv_unsigned b)%Z.
Proof.
  intros a .


Compute shift_and_add_multiplier 4 (Z_to_bv 4 13) (Z_to_bv 4 9).


