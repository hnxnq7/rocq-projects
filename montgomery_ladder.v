Require Import ZArith.
Require Import Lia.
From stdpp Require Import base.
From stdpp Require Import bitvector.

Open Scope Z_scope.

Record AffinePoint {p : Z} := {
  aX : Z;
  aY : Z;
  aX_range : 0 <= aX < p;
  aY_range : 0 <= aY < p
}.
Arguments AffinePoint : clear implicits.

(* A pair (pX, pZ) represents the affine value  pX * pZ^{-1} mod p.
   LadderStep works entirely in projective coords - inversion happens once at the end via proj_to_affine. *)
Record ProjX (p : Z) := {
  pX : Z;
  pZ : Z
}.

Definition x_of {p : Z} (Q : AffinePoint p) : Z := aX Q.

Section Montgomery.
  Variable p      : Z.             (* prime modulus                          *)
  Variable p_gt_0 : p > 0.
  Variable fp_inv : Z -> Z -> Z.   (* fp_inv p z = z^{-1} mod p             *)
  Variable A24    : Z.             (* (A+2)/4 mod p precomputed from curve  *)

  (* field operations *)
  Definition fadd (a b : Z) : Z := (a + b) mod p.
  Definition fsub (a b : Z) : Z := (a - b) mod p.
  Definition fmul (a b : Z) : Z := (a * b) mod p.
  Definition fsq  (a : Z)   : Z := fmul a a.

  Lemma fmul_bounded:
    forall (a b : Z),
    0 <= fmul a b < p.
  Proof.
    intros. unfold fmul. apply Z.mod_pos_bound. lia.
  Qed.

  Create HintDb field.
  Hint Resolve fmul_bounded : field.

  (* Definition scalar_mul (k : Z) (point : AffinePoint p) : AffinePoint p.
  Proof.
    refine {|
      aX := fmul point.(aX) k;
      aY := fmul point.(aY) k;
      aX_range := _;
      aY_range := _;
    |}.
    all: auto with field.
  Qed. *)

  Definition affine_to_proj (x : Z) : Z * Z := (x, 1).
  Definition proj_to_affine (pX pZ : Z) : Z :=
    fmul pX (fp_inv p pZ).
  
  Parameter scalar_mul : Z -> AffinePoint p -> AffinePoint p.

  (* Doubling: given projective coords (X:Zc) for [k]P,
     the doubling formula outputs projective coords for [2k]P.
     Encodes: x(2P) = U²V² / ((U²-V²)(V²+A24(U²-V²)))
     where U=X+Z, V=X-Z *)
  Axiom doubling_formula :
    forall k (Q : AffinePoint p) (X Zc : Z),
    proj_to_affine X Zc = x_of (scalar_mul k Q) ->
    let U  := fadd X Zc in
    let V  := fsub X Zc in
    let U2 := fsq U in
    let V2 := fsq V in
    let d  := fsub U2 V2 in
    proj_to_affine (fmul U2 V2) (fmul d (fadd V2 (fmul A24 d))) =
      x_of (scalar_mul (2 * k) Q).
  
  (* Differential addition: given projective coords for [k]P and [k+1]P,
     and the affine x-coord of P, the formula outputs projective coords for [2k+1]P.
     Encodes: x(P+Q) = (UT+VW)² / (X1*(UT-VW)²)
    where U=X2+Z2, V=X2-Z2, W=X3+Z3, T=X3-Z3 *)
  Axiom diff_add_formula :
    forall k (Q : AffinePoint p) (X2 Z2 X3 Z3 X1 : Z),
    proj_to_affine X2 Z2 = x_of (scalar_mul k Q) ->
    proj_to_affine X3 Z3 = x_of (scalar_mul (k + 1) Q) ->
    X1 = x_of Q ->
    let U  := fadd X2 Z2 in
    let V  := fsub X2 Z2 in
    let W  := fadd X3 Z3 in
    let T  := fsub X3 Z3 in
    let Sp := fadd (fmul U T) (fmul V W) in
    let Sm := fsub (fmul U T) (fmul V W) in
    proj_to_affine (fsq Sp) (fmul (fsq Sm) X1) =
      x_of (scalar_mul (2 * k + 1) Q).

  (* Inputs:
         X1        : x(P) affine — fixed base point, used only in diff. add.
         (X2, Z2)  : projective x-coord of R0 = [k]P
         (X3, Z3)  : projective x-coord of R1 = [k+1]P
       Output: (X2', Z2', X3', Z3') representing ([2k]P, [2k+1]P) *)
  Definition LadderStep (X1 X2 Z2 X3 Z3 : Z) : Z * Z * Z * Z :=
    let U  := fadd X2 Z2 in          (* U  = X2 + Z2  *)
    let V  := fsub X2 Z2 in          (* V  = X2 - Z2  *)
    let W  := fadd X3 Z3 in          (* W  = X3 + Z3  *)
    let T  := fsub X3 Z3 in          (* T  = X3 - Z3  *)

    let U2 := fsq U in               (* U^2            *)
    let V2 := fsq V in               (* V^2            *)

    let UT := fmul U T in            (* UT              *)
    let VW := fmul V W in            (* VW              *)
    let Sp := fadd UT VW in          (* UT + VW         *)
    let Sm := fsub UT VW in          (* UT - VW         *)

    let X3' := fsq Sp in             (* (UT + VW)^2           *)
    let Z3' := fmul (fsq Sm) X1 in  (* (UT - VW)^2 * X1      *)
    
    let X2'  := fmul U2 V2 in        (* U^2 * V^2                          *)
    let diff := fsub U2 V2 in        (* U^2 - V^2                           *)
    let Z2'  := fmul diff
                  (fadd V2 (fmul A24 diff)) in (* (U^2-V^2)(V^2 + A24*(U^2-V^2))     *)
    (X2', Z2', X3', Z3').
  
  
  (* U²V² = (X²-Z²)²  i.e. the doubling numerator in its standard form.
     proof: (X+Z)²(X-Z)² = ((X+Z)(X-Z))² = (X²-Z²)²  by ring mod p *)
  Lemma doubling_num_algebra (X Zc : Z) :
    fmul (fsq (fadd X Zc)) (fsq (fsub X Zc)) =
      fsq (fsub (fsq X) (fsq Zc)).
  Admitted.

  (* (UT+VW)² = 4(X₂X₃ - Z₂Z₃)²
     proof: UT+VW = 2(X₂X₃-Z₂Z₃)  by expanding, then square  *)
  Lemma diff_add_sum_algebra (X2 Z2 X3 Z3 : Z) :
    let U  := fadd X2 Z2 in let V := fsub X2 Z2 in
    let W  := fadd X3 Z3 in let T := fsub X3 Z3 in
    fsq (fadd (fmul U T) (fmul V W)) =
      fmul 4 (fsq (fsub (fmul X2 X3) (fmul Z2 Z3))).
  Admitted.

  (* (UT-VW)² = 4(X₂Z₃ - X₃Z₂)²
     proof: UT-VW = -2(X₂Z₃-X₃Z₂)  by expanding, then square *)
  Lemma diff_add_dif_algebra (X2 Z2 X3 Z3 : Z) :
    let U  := fadd X2 Z2 in let V := fsub X2 Z2 in
    let W  := fadd X3 Z3 in let T := fsub X3 Z3 in
    fsq (fsub (fmul U T) (fmul V W)) =
      fmul 4 (fsq (fsub (fmul X2 Z3) (fmul X3 Z2))).
  Admitted.

  Lemma LadderStep_correct (X1 X2 Z2 X3 Z3 k : Z) (P : AffinePoint p) :
    proj_to_affine X2 Z2 = x_of (scalar_mul k P) ->
    proj_to_affine X3 Z3 = x_of (scalar_mul (k + 1) P) ->
    X1 = x_of P ->
    let '(X2', Z2', X3', Z3') := LadderStep X1 X2 Z2 X3 Z3 in
    proj_to_affine X2' Z2' = x_of (scalar_mul (2 * k)     P) /\
    proj_to_affine X3' Z3' = x_of (scalar_mul (2 * k + 1) P).
  Proof.
    intros H_R0 H_R1 H_X1.
    unfold LadderStep. simpl.
    split.
    - exact (doubling_formula k P X2 Z2 H_R0).
    - exact (diff_add_formula k P X2 Z2 X3 Z3 X1 H_R0 H_R1 H_X1).
  Qed.

  
  (* algorithm 1 *)
  Definition MontLadder_step
      (X1 : Z) (bit : bool) (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    let '(X2, Z2, X3, Z3) := st in
    if bit then
      let '(X3', Z3', X2', Z2') := LadderStep X1 X3 Z3 X2 Z2 in
      (X2', Z2', X3', Z3')
    else
      LadderStep X1 X2 Z2 X3 Z3.

  (* bit extraction *)
  Definition bit_i (n : Z) (i : nat) : bool :=
    Z.testbit n (Z.of_nat i).
  
  Fixpoint MontLadder_rec
      (m : nat) (X1 n : Z) (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    match m with
    | O => st
    | S m' =>
        let bit := bit_i n m' in
        MontLadder_rec m' X1 n (MontLadder_step X1 bit st)
    end.

  Definition MontLadder (m : nat) (xP n : Z) : Z * Z :=
    let st0 := (1, 0, xP, 1) in
    let '(X2, Z2, _, _) := MontLadder_rec m xP n st0 in
    (X2, Z2).
  
  Tactic Notation "case_match_in" ident(H) "eqn" ":" ident(Hd) :=
    match type of H with
    | context [ match ?x with _ => _ end ] => destruct x eqn:Hd
    end.
  
  Tactic Notation "case_goal_match" "eqn" ":" ident(Hd) :=
    match goal with
    | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
    end.
  
  (* Lemma MontLadder_rec_correct:
    forall m X1 n,
    MontLadder_rec m X1 N =  *)

  (* invariant proof *)
  (* for each st n+1 -> X3 *)
  (* given x-coord xP of a point P --> x-coord of nP *)
  (* Lemma MontLadder_correct:
    forall (m : nat) (xP n : Z) x' z',
    MontLadder m xP n = (x', z') -> x' = fmul n xP.
  Proof.
    intros. unfold MontLadder in *.
    case_match_in H eqn : Hrec. *)

  (* algorithm 3 *)
  Definition CSwap
      (X2 Z2 X3 Z3 : Z) (b : bool) : Z * Z * Z * Z :=
    if b
    then (X3, Z3, X2, Z2)
    else (X2, Z2, X3, Z3).

  Definition MontLadderCSwap_step
      (X1 : Z) (bit prevbit : bool) (st : Z * Z * Z * Z)
      : (Z * Z * Z * Z) * bool :=
    let swap := xorb bit prevbit in
    let '(X2, Z2, X3, Z3) := st in
    let '(X2s, Z2s, X3s, Z3s) := CSwap X2 Z2 X3 Z3 swap in
    let '(X2', Z2', X3', Z3') := LadderStep X1 X2s Z2s X3s Z3s in
    ((X2', Z2', X3', Z3'), bit).
  
  Fixpoint MontLadderCSwap_rec
      (m : nat) (X1 n : Z)
      (st : (Z * Z * Z * Z) * bool)
      : (Z * Z * Z * Z) * bool :=
    match m with
    | O => st
    | S m' =>
        let '(regs, prevbit) := st in
        let bit := bit_i n m' in
        let st' := MontLadderCSwap_step X1 bit prevbit regs in
        MontLadderCSwap_rec m' X1 n st'
    end.

  Definition MontLadderCSwap (m : nat) (xP n : Z) : Z * Z :=
    let st0 := ((1, 0, xP, 1), false) in
    let '(regs, final_prev) := MontLadderCSwap_rec m xP n st0 in
    (* normalize: if final_prev=true the registers are still swapped *)
    let '(X2, Z2, X3, Z3) := regs in
    let '(X2f, Z2f, _, _) := CSwap X2 Z2 X3 Z3 final_prev in
    (X2f, Z2f).

  (* swap the two projective register pairs *)
  Definition swap_regs (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    let '(X2, Z2, X3, Z3) := st in (X3, Z3, X2, Z2).

  (* undo the current logical swap: if swapped=true, flip back *)
  Definition norm_regs (st : Z * Z * Z * Z) (swapped : bool) : Z * Z * Z * Z :=
    if swapped then swap_regs st else st.
  
  (* One step of Algorithm 3, when normalized by its output swap bit,
   equals one step of Algorithm 1 starting from the normalized input. *)
  Lemma MontLadder_step_norm:
    forall X1 X2 Z2 X3 Z3 (prev bit : bool),
    let '(regs3, new_prev) := MontLadderCSwap_step X1 bit prev (X2, Z2, X3, Z3) in
    norm_regs regs3 new_prev
    = MontLadder_step X1 bit (norm_regs (X2, Z2, X3, Z3) prev).
  Proof.
    intros.
    unfold MontLadderCSwap_step, MontLadder_step, CSwap, norm_regs, swap_regs.
    (* case split on all four combinations of prev and bit *)
    destruct prev, bit; simpl; try reflexivity.
  Qed.

  Lemma simple_tuple_inversion:
    forall {A} {B} (a: A) (b: B) x y,
    (a,b) = (x,y) ->
    a = x /\ b = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  Ltac simplify_tuples :=
    repeat match goal with
    | [ H: (_,_) = (_,_) |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
      apply simple_tuple_inversion in H; destruct H as [H1 H2]
    end.
  
  Ltac simplify_tupless := simplify_tuples; subst.

  Lemma rec_eq : 
    forall m xP n st st' st1 st1' prev new_prev,
    (* let '(regs3, new_prev) := MontLadderCSwap_rec m xP n (st, prev) in norm_regs regs3 new_prev
    = MontLadder_rec m xP n st. *)

    st1 = norm_regs st prev ->
    MontLadderCSwap_rec m xP n (st, prev) = (st', new_prev) ->
    MontLadder_rec m xP n st1 = st1' ->
    st1' = norm_regs st' new_prev.
  Proof.
    induction m.
    - simpl. intros. simplify_tupless. reflexivity.
    - intros xP n st st' st1 st1' prev new_prev H_norm H_cswap H_ladder.
      destruct st as [[[X2 Z2] X3] Z3].
      cbn [MontLadderCSwap_rec MontLadder_rec] in H_cswap, H_ladder.
      set (bit := bit_i n m) in *. (* name current bit *)
      remember (MontLadderCSwap_step xP bit prev (X2, Z2, X3, Z3)) as step_res eqn:H_step. (* freeze intermediate state/result *)
      destruct step_res as [st_mid bit_mid].
      pose proof (MontLadder_step_norm xP X2 Z2 X3 Z3 prev bit) as H_sn.
      rewrite <- H_step in H_sn.
      cbn in H_sn.
      rewrite <- H_norm in H_sn.
      apply (IHm xP n st_mid st' (MontLadder_step xP bit st1) st1' bit_mid new_prev).
      + symmetry. exact H_sn.
      + exact H_cswap.
      + exact H_ladder.
  Qed.

  (* show result of alg 1 and alg 3 are the same *)
  Lemma CSwap_eq m xP n :
    MontLadderCSwap m xP n = MontLadder m xP n.
  Proof.
    unfold MontLadderCSwap, MontLadder.
    remember (MontLadderCSwap_rec m xP n ((1, 0, xP, 1), false)) as cswap_res eqn:HCSwap.
    destruct cswap_res as [st' final_prev].
    remember (MontLadder_rec m xP n (1, 0, xP, 1)) as ladder_res eqn:Hladder.
    assert (H_eq : ladder_res = norm_regs st' final_prev).
    { apply (rec_eq m xP n (1, 0, xP, 1) st' (1, 0, xP, 1) ladder_res false final_prev).
      (* (1,0,xP,1) = norm_regs (1,0,xP,1) false - trivially true since norm_regs _ false = id
          CSwap-rec output = (st', final_prev) -> HCSwap
          Ladder-rec output = ladder_res *)
      - reflexivity.        (* norm_regs (1,0,xP,1) false = (1,0,xP,1) *)
      - symmetry. exact HCSwap.
      - symmetry. exact Hladder. }
    destruct st' as [[[X2' Z2'] X3'] Z3'].
    rewrite H_eq.
    destruct final_prev; simpl; reflexivity.
  Qed.

  (* 1. Define HW of a bv *)
  (* 2. Define operations given inputs associated with uniformly random vars *)
      (* HW of a + uniformly random var --> HW of something uniformly random var *)
  (* 3. start thinking of defining a language w/ only the field operations *)

  (* Definition masked_add_secure :=
  forall (a1 a2 b r : bv n),
  distribution of numOfOnes((a1 XOR r) + b) over uniform r
     = distribution of numOfOnes((a2 XOR r) + b) * *)
End Montgomery.

Section HammingWeight.
  Variable n : N. (* width of bv *)
  Variable p : bv n. 

  (* check if mod at every operation? *)
  (* signed or unsigned? *)

  (* Definition fadd (a b : Z) : Z := (a + b) mod p.
  Definition fsub (a b : Z) : Z := (a - b) mod p.
  Definition fmul (a b : Z) : Z := (a * b) mod p.
  Definition fsq  (a : Z)   : Z := fmul a a. *)

  (* bv version *)
  Definition fadd_bv (a b : bv n) : bv n := bv_modu (bv_add a b) p .
  Definition fsub_bv (a b : bv n) : bv n := bv_modu (bv_sub a b) p.
  Definition fmul_bv (a b : bv n) : bv n := bv_modu (bv_mul a b) p.
  Definition fsq_bv  (a : bv n)   : bv n := fmul_bv a a.

  Definition num_true (bools : list bool) : nat.
  Admitted.

  Inductive ProbType :=
    | Prob_concrete
    | Prob_random (* seed *)
    | Prob_unknown.
  
  Record ProbVar :=
  { Value : bv n;
    Ptype : ProbType
  }.

   (* ProbVar version *)
  Definition faddsub_prob (a b : ProbType) : ProbType := 
    match a, b with
    | Prob_unknown, _ => Prob_unknown
    | _, Prob_unknown => Prob_unknown
    | Prob_concrete, Prob_concrete => Prob_concrete
    | Prob_concrete, Prob_random => Prob_random
    | Prob_random, Prob_concrete => Prob_random
    | Prob_random, Prob_random => Prob_random
    end.

  Definition fmul_prob (a b : ProbType) : ProbType := 
    match a, b with
    | Prob_unknown, _ => Prob_unknown
    | _, Prob_unknown => Prob_unknown
    | Prob_concrete, Prob_concrete => Prob_concrete
    | Prob_concrete, Prob_random => Prob_random
    | Prob_random, Prob_concrete => Prob_random
    | Prob_random, Prob_random => Prob_unknown
    end.
  
  Definition fadd_probvar (a b : ProbVar) : ProbVar := {| 
    Value := fadd_bv a.(Value) b.(Value);
    Ptype := faddsub_prob a.(Ptype) b.(Ptype)
  |}.

  (* another direction: duplicate circuit --> invert? --> HW same without masking *)

  Inductive ProbHW :=
    | ProbHW_concrete (n : N)
    | ProbHW_random
    | ProbHW_unknown.
  
  (* Todo: toy example of masking? *)

  (* language *)
  Inductive exp : Type :=
    | Constant (c : ProbVar)
    | Add (a b : exp)
    | Sub (a b : exp)
    | Mul (a b : exp).
  
  Fixpoint interp_exp (e : exp) : ProbVar.
    refine (match e with
            | Constant c => c
            | Add a b => fadd_probvar (interp_exp a) (interp_exp b)
            (* TODO *)
            | _ => _
            end).
  
  (* add variables? --> try to implement mont ladder using this language *)

  Definition HW (a : bv n) : nat := num_true (bv_to_bits a).
  
    


  

End HammingWeight.