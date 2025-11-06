Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith_base.
From Stdlib Require Import Lia.

Import ListNotations.

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma nth_error_nil:
  forall {A: Type} (i: nat) (v: A),
  nth_error [] i = Some v ->
  False.
Proof.
  intros. destruct i; simpl in *; discriminate.
Qed.

Ltac t :=
  match goal with
  | H: nth_error [] _  = Some _ |- _ =>
      apply nth_error_nil in H; contradiction
  end.

Lemma sorted_sorted': forall al, sorted al -> sorted' al.
Proof.
  induction 1.
  - unfold sorted'. intros. destruct i; t.
  - unfold sorted' in *. intros.
    destruct i; destruct j; simpl in *; try t. lia.
  - unfold sorted' in *.
    intros.
    destruct i; destruct j.
    + lia.
    + simpl in *. 
      inversion H2. subst.
      assert (y <= jv).
      {destruct j. 
       - simpl in *. inversion H3. lia.
       - apply IHsorted with (i := 0) (j := S j). lia. simpl in *. auto. simpl in *. auto.
      }
      { lia. }
    + lia.
    + simpl in *.
      assert (i < j).
      lia.
      apply IHsorted with (i := i) (j := j). auto. auto. auto.
Qed.

