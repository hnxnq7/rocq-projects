Require Import Lia.

Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin).

Fixpoint inc (x : bin) : bin :=
  match x with
  | Z        => B1 Z
  | B0 x'    => B1 x'
  | B1 x'    => B0 (inc x')
  end.

Fixpoint bin_add_carry (a b : bin) (c : bool) {struct a} : bin :=
  match a with
  | Z =>
      if c then inc b else b
  | B0 a' =>
      match b with
      | Z        => if c then inc (B0 a') else B0 a'
      | B0 b'    => if c then B1 (bin_add_carry a' b' false)
                          else B0 (bin_add_carry a' b' false)
      | B1 b'    => if c then B0 (bin_add_carry a' b' true)
                          else B1 (bin_add_carry a' b' false)
      end
  | B1 a' =>
      match b with
      | Z        => if c then inc (B1 a') else B1 a'
      | B0 b'    => if c then B0 (bin_add_carry a' b' true)
                          else B1 (bin_add_carry a' b' false)
      | B1 b'    => if c then B1 (bin_add_carry a' b' true)
                          else B0 (bin_add_carry a' b' true)
      end
  end.

Definition bin_add (a b : bin) : bin :=
  bin_add_carry a b false.

(* Example tests *)
Definition one   := B1 Z.
Definition two   := B0 (B1 Z).
Definition three := B1 (B1 Z).
Definition four  := B0 (B0 (B1 Z)).
Definition five  := B1 (B0 (B1 Z)).

Compute (bin_add one one).
Compute (bin_add three five).
Compute (bin_add four one).


Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | Z => 0
  | B0 x => 2 * bin_to_nat x
  | B1 x => 2 * bin_to_nat x + 1
  end.

Compute (bin_to_nat (bin_add one one)).
Compute (bin_to_nat (bin_add three five)).
Compute (bin_to_nat (bin_add four one)).

(* Proof *)
Lemma inc_correct :
    forall b,
        bin_to_nat (inc b) = bin_to_nat b+1.
Proof.
    induction b. simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite IHb. lia.
Qed.

Lemma bin_add_carry_correct :
  forall a b c,
    bin_to_nat (bin_add_carry a b c) =
    bin_to_nat a + bin_to_nat b + (if c then 1 else 0).

Proof.
    induction a. intros. simpl.
        - destruct c. apply inc_correct. lia.
        - destruct b; destruct c; simpl; repeat rewrite IHa; try lia.
        - destruct b; destruct c; simpl; repeat rewrite inc_correct; repeat rewrite IHa; try lia.
Qed.
