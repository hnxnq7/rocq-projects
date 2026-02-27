Require Import Lia.
From stdpp Require Import base.
From stdpp Require Import bitvector.
From Coq Require Import NArith.BinNat.

Print bv.
Search bv.

Record Multiplier {n} :=
{ OperandA : bv n;
  OperandB : bv n;
  C : bv (n+n);
  i : bv n
}.
Arguments Multiplier : clear implicits.

Definition to_N {n} (w: bv n) : N := Z.to_N (bv_unsigned w).

(* State transition function that takes a multiplier and perform a shift-and-add to result in another *)
Definition shift_and_add_step n (state : Multiplier n) : Multiplier n :=
let is_one := bv_extract (to_N state.(i)) 1 state.(OperandB) in 
{| OperandA :=    state.(OperandA);
   OperandB :=    state.(OperandB);
   C :=           if decide (is_one = (Z_to_bv _ 1))
                  then bv_add state.(C) (bv_shiftl (bv_zero_extend (n+n) state.(OperandA)) (bv_zero_extend (n+n) state.(i)))
                  else state.(C);
   i :=           bv_add state.(i) (Z_to_bv _ 1)
|}.

(* for i = 0 to n:
    if b[i] == 1: add a shift n-i to c
    else ignore
 *)
(* state what it means to iterate something N times *)
(* theorem for what it means for it to be correct *)
(* look up how to do EFFECTIVELY in hardware,
  i.e., shift right and only look at 0th (rightmost) bit *)
(* fold ~= for loop *)
(* overflow? *)

  


Fixpoint shift_add_pos (a : N) (p : positive) {struct p} : N :=
  match p with
  | xH => a
  | xO p' => shift_add_pos (a + a) p'
  | xI p' => a + shift_add_pos (a + a) p'
  end.

Definition shift_add_mul (a b : N) : N :=
  match b with
  | N0 => 0
  | Npos p => shift_add_pos a p
  end.

Compute shift_add_mul 5 3.
Compute shift_add_mul 7 4.
Compute shift_add_mul 0 10.
Compute shift_add_mul 9 0.
Compute shift_add_mul 25 98.


(* Proof *)
Lemma shift_add_pos_correct :
  forall p a, shift_add_pos a p = (a * (Npos p))%N.
Proof.
  induction p.
  - cbn. intros a. rewrite IHp. lia.
  - cbn. intros a. rewrite IHp. lia.
  - cbn. intros a. rewrite N.mul_1_r. reflexivity.
Qed.

Theorem shift_add_mul_correct :
  forall a b : N, shift_add_mul a b = (a * b)%N.
Proof.
  intros a b. destruct b as [|p]; simpl.
  - rewrite N.mul_0_r. reflexivity.
  - apply shift_add_pos_correct.
Qed.


