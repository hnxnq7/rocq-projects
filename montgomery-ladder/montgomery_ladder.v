Require Import ZArith.
Require Import Lia.
Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
From stdpp Require Import base.
From stdpp Require Import bitvector.
From stdpp Require Import list.

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
  Proof.
    unfold fsq, fadd, fsub, fmul.
    rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r,
            ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r.
    f_equal.
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

  (* bv version *)
  Definition fadd_bv (a b : bv n) : bv n := bv_modu (bv_add a b) p .
  Definition fsub_bv (a b : bv n) : bv n := bv_modu (bv_sub a b) p.
  Definition fmul_bv (a b : bv n) : bv n := bv_modu (bv_mul a b) p.
  Definition fsq_bv  (a : bv n)   : bv n := fmul_bv a a.

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

  (* NEW: sub and mul *)
  Definition fsub_probvar (a b : ProbVar) : ProbVar := {|
    Value := fsub_bv a.(Value) b.(Value);
    Ptype := faddsub_prob a.(Ptype) b.(Ptype)
  |}.

  Definition fmul_probvar (a b : ProbVar) : ProbVar := {|
    Value := fmul_bv a.(Value) b.(Value);
    Ptype := fmul_prob a.(Ptype) b.(Ptype)
  |}.

  (* another direction: duplicate circuit --> invert? --> HW same without masking *)
    (* would be cool *)

  Inductive ProbHW :=
    | ProbHW_concrete (n : N)
    | ProbHW_random
    | ProbHW_unknown.
  
  (* Todo: toy example of masking? *)

  (* language *)
  Definition var := nat.

  Inductive instr : Type :=
    (* | Constant (c : ProbVar)
    | Var      (i : nat) 
    | Add (a b : var)
    | Sub (a b : var)
    | Mul (a b : var). *)

    | IAdd (rd rs1 rs2 : var)
    | ISub (rd rs1 rs2 : var)
    | IMul (rd rs1 rs2 : var)
    | Observe (rd : var).
  
  Open Scope nat.

  Notation rX1  := 0  (only parsing).
  Notation rX2  := 1  (only parsing).
  Notation rZ2  := 2  (only parsing).
  Notation rX3  := 3  (only parsing).
  Notation rZ3  := 4  (only parsing).
  Notation rA24 := 5  (only parsing).
  Notation rU   := 6  (only parsing).   (* X2 + Z2 *)
  Notation rV   := 7  (only parsing).   (* X2 - Z2 *)
  Notation rW   := 8  (only parsing).   (* X3 + Z3 *)
  Notation rT   := 9  (only parsing).   (* X3 - Z3 *)
  Notation rU2  := 10 (only parsing).   (* U*U *)
  Notation rV2  := 11 (only parsing).   (* V*V *)
  Notation rUT  := 12 (only parsing).   (* U*T *)
  Notation rVW  := 13 (only parsing).   (* V*W *)
  Notation rSp  := 14 (only parsing).   (* UT + VW *)
  Notation rSm  := 15 (only parsing).   (* UT - VW *)
  Notation rX3' := 16 (only parsing).   (* Sp^2 *)
  Notation rSm2 := 17 (only parsing).   (* Sm^2 *)
  Notation rZ3' := 18 (only parsing).   (* Sm2 * X1 *)
  Notation rX2' := 19 (only parsing).   (* U2 * V2 *)
  Notation rD   := 20 (only parsing).   (* U2 - V2 *)
  Notation rAD  := 21 (only parsing).   (* A24 * D *)
  Notation rT2  := 22 (only parsing).   (* V2 + AD *)
  Notation rZ2' := 23 (only parsing).   (* D * T2 *)


  Definition program : list instr :=
    [ IAdd rU   rX2  rZ2    (* U   = X2 + Z2 *)
    ; ISub rV   rX2  rZ2    (* V   = X2 - Z2 *)
    ; IAdd rW   rX3  rZ3    (* W   = X3 + Z3 *)
    ; ISub rT   rX3  rZ3    (* T   = X3 - Z3 *)
    ; IMul rU2  rU   rU     (* U2  = U  * U *)
    ; IMul rV2  rV   rV     (* V2  = V  * V *)
    ; IMul rUT  rU   rT     (* UT  = U  * T *)
    ; IMul rVW  rV   rW     (* VW  = V  * W *)
    ; IAdd rSp  rUT  rVW    (* Sp  = UT + VW *)
    ; ISub rSm  rUT  rVW    (* Sm  = UT - VW *)
    ; IMul rX3' rSp  rSp    (* X3' = Sp^2 *)
    ; IMul rSm2 rSm  rSm    (* Sm2 = Sm^2 *)
    ; IMul rZ3' rSm2 rX1    (* Z3' = Sm2 * X1 *)
    ; IMul rX2' rU2  rV2    (* X2' = U2 * V2 *)
    ; ISub rD   rU2  rV2    (* D   = U2 - V2 *)
    ; IMul rAD  rA24 rD     (* AD  = A24 * D *)
    ; IAdd rT2  rV2  rAD    (* T2  = V2 + AD *)
    ; IMul rZ2' rD   rT2    (* Z2' = D * T2 *)
    ].
  
  (* todo: reuse registers --> use less regs *)
    (* program counter & fetch memory *)

  Definition ProbEnv := list ProbVar.

  Definition prob_default_var : ProbVar := {|
    Value := bv_0 n;
    Ptype := Prob_unknown
  |}.
  
  (* secret register & public register --> only do dual circuits on the secret *)

  Definition prob_read_register (env : ProbEnv) (i : var) : ProbVar := nth i env prob_default_var.
  Definition prob_write_register (env : ProbEnv) (i : var) (data : ProbVar) : ProbEnv := list_insert i data env.

  Definition num_true (bools : list bool) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) bools 0.

  Definition HW (a : bv n) : nat := num_true (bv_to_bits a).

  Definition num_1s (a : bv n) : nat :=
    num_true (bv_to_bits a).
  
  Definition num_1s_in_list (bvs : list (bv n)) : nat :=
    fold_left (fun acc pv => acc + HW pv) bvs 0.

  Definition num_1s_in_env (env : ProbEnv) : nat :=
    num_1s_in_list (map Value env).

  Inductive Observation :=
    | RegObservation (r : var) (val : (bv n)).

  Definition prob_interp_instr (env : ProbEnv) (e : instr) : ProbEnv * list Observation :=
    match e with
    (* | Constant c => c *)
    (* | Var i      => nth i env default_var *)
    | IAdd rd a b    => (prob_write_register env rd (fadd_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | ISub rd a b    => (prob_write_register env rd (fsub_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | IMul rd a b    => (prob_write_register env rd (fmul_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | Observe rd     => (env, [RegObservation rd (prob_read_register env rd).(Value)])
    end.
  
  Section DualCircuit.

    (* Types & operational semantics *)

    Definition Env := list (bv n).
    Record state := { env : Env; denv : Env }.

    Definition default_var : bv n := bv_0 n.
    Definition read_register  (env : Env) (i : var) : bv n      := nth i env default_var.
    Definition write_register (env : Env) (i : var) (data : bv n) : Env := list_insert i data env.

    Definition interp_instr (env : Env) (e : instr) : Env * list Observation :=
      match e with
      | IAdd rd a b => (write_register env rd (fadd_bv (read_register env a) (read_register env b)), [])
      | ISub rd a b => (write_register env rd (fsub_bv (read_register env a) (read_register env b)), [])
      | IMul rd a b => (write_register env rd (fmul_bv (read_register env a) (read_register env b)), [])
      | Observe rd  => (env, [RegObservation rd (read_register env rd)])
      end.

    (* dual circuit: env holds actual values, denv = map bv_not env *)
    Definition dual_interp_instr (s : state) (e : instr) : state * list Observation :=
      let '(env', obs) := interp_instr s.(env) e in
      ({| env := env'; denv := map bv_not env' |}, obs).

    (* run first [steps] instructions, accumulating observations *)
    Definition run (s : state) (prog : list instr) (steps : nat) : state * list Observation :=
      fold_left
        (fun '(s_acc, obs_acc) e =>
          let '(s', new_obs) := dual_interp_instr s_acc e in
          (s', obs_acc ++ new_obs))
        (firstn steps prog) (s, []).

      

    (* Security definitions *)

    (* invariant: denv is always the bitwise complement of env *)
    Definition valid_state (s : state) : Prop :=
      s.(denv) = map bv_not s.(env).

    Definition is_complement (e1 e2 : Env) : Prop :=
      forall i, read_register e2 i = bv_not (read_register e1 i).

    Definition num_1s_in_state (s : state) : nat :=
      num_1s_in_list s.(env) + num_1s_in_list s.(denv).

    (* security: total HW per cycle is constant regardless of secret *)
    Definition secure (prog : list instr) (s : state) :=
      exists c, forall steps, num_1s_in_state (run s prog steps).1 = c.



    (* Length preservation *)

    Lemma write_register_length : forall (e : Env) (i : var) (v : bv n),
      length (write_register e i v) = length e.
    Proof. intros e i v. unfold write_register. apply length_insert. Qed.

    Lemma interp_instr_preserves_length : forall (e : Env) (i : instr),
      length (interp_instr e i).1 = length e.
    Proof.
      intros e i. destruct i; simpl; rewrite ?write_register_length; reflexivity.
    Qed.

    Lemma dual_interp_preserves_length : forall (s : state) (i : instr),
      length (env (dual_interp_instr s i).1) = length (env s).
    Proof.
      intros s i. unfold dual_interp_instr.
      destruct (interp_instr s.(env) i) as [env' obs] eqn:H.
      simpl. rewrite <- (interp_instr_preserves_length s.(env) i). rewrite H. reflexivity.
    Qed.

    Lemma fold_left_preserves_length : forall instrs s_init obs_init,
      length (env (fold_left
        (fun '(s_acc, obs_acc) e =>
          let '(s', new_obs) := dual_interp_instr s_acc e in
          (s', obs_acc ++ new_obs))
        instrs (s_init, obs_init)).1) = length (env s_init).
    Proof.
      induction instrs as [| i rest IH]; intros s_init obs_init.
      - simpl. reflexivity.
      - simpl. destruct (dual_interp_instr s_init i) as [s' new_obs] eqn:Hstep.
        rewrite IH. rewrite <- (dual_interp_preserves_length s_init i).
        rewrite Hstep. reflexivity.
    Qed.

    Lemma run_preserves_length : forall (s : state) (prog : list instr) (steps : nat),
      length (env (run s prog steps).1) = length (env s).
    Proof. intros s prog steps. unfold run. apply fold_left_preserves_length. Qed.

    
    
    (* Valid state preservation *)

    Lemma dual_interp_preserves_valid : forall (s : state) (e : instr),
      valid_state (dual_interp_instr s e).1.
    Proof.
      intros s e. unfold dual_interp_instr, valid_state.
      destruct (interp_instr s.(env) e) as [env' obs]. simpl. reflexivity.
    Qed.

    Lemma fold_left_run_valid : forall instrs s_init obs_init,
      valid_state s_init ->
      valid_state (fold_left
        (fun '(s_acc, obs_acc) e =>
          let '(s', new_obs) := dual_interp_instr s_acc e in
          (s', obs_acc ++ new_obs))
        instrs (s_init, obs_init)).1.
    Proof.
      induction instrs as [| e rest IH]; intros s_init obs_init Hvalid.
      - simpl. exact Hvalid.
      - simpl. destruct (dual_interp_instr s_init e) as [s' new_obs] eqn:Hstep.
        apply IH.
        assert (Hv := dual_interp_preserves_valid s_init e).
        rewrite Hstep in Hv. simpl in Hv. exact Hv.
    Qed.

    Lemma run_preserves_valid : forall (s : state) (prog : list instr) (steps : nat),
      valid_state s -> valid_state (run s prog steps).1.
    Proof. intros s prog steps H. unfold run. apply fold_left_run_valid. exact H. Qed.

    

    (* HW counting *)

    Lemma fold_left_plus : forall (rest : list bool) (acc : nat),
      fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) rest acc
      = fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) rest 0 + acc.
    Proof.
      induction rest. simpl. reflexivity.
      simpl. intros. destruct a; auto. rewrite IHrest. rewrite IHrest with (acc := 1). lia.
    Qed.

    Lemma num_true_complement : forall (bools : list bool),
      num_true bools + num_true (map negb bools) = length bools.
    Proof.
      induction bools as [| b rest IH]; simpl.
      - reflexivity.
      - unfold num_true in *. simpl filter.
        destruct b; simpl. rewrite fold_left_plus. lia. rewrite fold_left_plus with (acc := 1). lia.
    Qed.

    (* Helpers for bv_to_bits_not *)
    Create HintDb List.
    Hint Rewrite length_map : List.
    Hint Rewrite @length_bv_to_bits : List.

    Lemma Some_ne_None' : forall A (opt : option A) a,
      opt = Some a -> opt <> None.
    Proof.
      destruct opt; auto.
    Qed.

    (* nth_error and stdpp's !! coincide; idx avoids clash with section variable n *)
    Lemma nth_error_lookup : forall A (xs : list A) (idx : nat) (d : A),
      nth_error xs idx = xs !! idx.
    Proof.
      intros.
      destruct (list_basics.list.nth_lookup_or_length xs idx d).
      { rewrite e.
        apply nth_error_nth'.
        eapply list_basics.list.lookup_lt_Some; eauto. }
      { destruct (nth_error _ _) eqn:?.
        { rewrite <- nth_error_None in l. congruence. }
        { symmetry. rewrite list_basics.list.lookup_ge_None. auto. } }
    Qed.

    Lemma bv_to_bits_not : forall (a : bv n),
      bv_to_bits (bv_not a) = map negb (bv_to_bits a).
    Proof.
      intros.
      apply nth_error_ext.
      intros. repeat rewrite nth_error_lookup by (try exact false).
      setoid_rewrite list_monad.list.list_lookup_fmap.
      destruct (decide (n0 < N.to_nat n)).
      { repeat match goal with
        | |- context[?x !! ?y] => destruct (x !! y) eqn:?
        | H: _ !! _ = None |- _ => rewrite list_basics.list.lookup_ge_None in H
        | |- Some _ = Some _ => f_equal
        | |- _ => autorewrite with List in *; auto; try lia; simpl in *
        end.
        rewrite bv_to_bits_lookup_Some in *.
        destruct_and !. subst.
        rewrite bv_not_unsigned.
        setoid_rewrite <- Z.lnot_spec; [ | lia].
        rewrite bv_wrap_spec_low; auto.
        lia. }
      { repeat rewrite list_basics.list.lookup_ge_None_2
          by (autorewrite with List; lia); done. }
    Qed.

    Lemma hw_complement : forall (a : bv n),
      HW a + HW (bv_not a) = N.to_nat n.
    Proof.
      intro a. unfold HW. rewrite bv_to_bits_not. rewrite num_true_complement.
      apply length_bv_to_bits.
    Qed.

    (* General accumulator lemma for HW sums — same pattern as fold_left_plus.
       NB: parameter named [l] not [env] to avoid the state field projector. *)
    Lemma num_1s_in_list_fold_plus : forall (l : list (bv n)) (k : nat),
      fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l k =
      fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l 0 + k.
    Proof.
      induction l as [| x rest IH]; simpl; intros k.
      - lia.
      - rewrite IH. rewrite IH with (k := HW x). lia.
    Qed.

    Lemma fold_left_plus_HW : forall (l : list (bv n)) (acc : nat) (a : bv n),
      fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l (acc + (HW a))
      = fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l (HW a) + acc.
    Proof.
      intros.
      rewrite num_1s_in_list_fold_plus.
      rewrite num_1s_in_list_fold_plus with (k := HW a).
      lia.
    Qed.

    Lemma valid_state_num_1s_induct : forall (env0 : Env) (acc : nat),
      fold_left (λ (acc : nat) (pv : bv n), acc + HW pv) env0 acc +
      fold_left (λ (acc : nat) (pv : bv n), acc + HW pv) (map bv_not env0) acc =
      length env0 * N.to_nat n + 2 * acc.
    Proof.
      (* induction before intros acc so the IH generalises over acc *)
      induction env0 as [| a rest IH].
      - simpl. lia.
      - simpl. intros acc.
        (* shift both accumulators to 0 using the general fold-left lemma *)
        rewrite (num_1s_in_list_fold_plus rest).
        rewrite (num_1s_in_list_fold_plus (map bv_not rest)).
        (* IH at acc=0: fold rest 0 + fold (map bv_not rest) 0 = length rest * n *)
        pose proof (IH 0) as IH0.
        (* hw_complement: HW a + HW (bv_not a) = n *)
        pose proof (hw_complement a) as Hc.
        (* simpl already expanded S (length rest) * n and 2 * acc; lia closes *)
        lia.
    Qed.

    Lemma valid_state_num_1s : forall (s : state),
      valid_state s ->
      num_1s_in_state s = length s.(env) * N.to_nat n.
    Proof.
      intros. unfold valid_state in *. unfold num_1s_in_state, num_1s_in_list. rewrite H.
      destruct s. simpl in *. rewrite valid_state_num_1s_induct. lia.
    Qed.



    (* Main security theorem *)

    Lemma all_secure : forall (prog : list instr) (init_s : state),
      valid_state init_s -> secure prog init_s.
    Proof.
      unfold secure. intros prog init_s Hvalid.
      exists (length init_s.(env) * N.to_nat n). intros steps.
      rewrite (valid_state_num_1s _ (run_preserves_valid init_s prog steps Hvalid)).
      rewrite run_preserves_length. reflexivity.
    Qed.

    

    (* secret register vs public *)

    Inductive RegClass := | SecretReg | PublicReg.

    (* In the ladder X1 and A24 are public inputs, everything else is secret *)
    Definition ladder_classify (r : var) : RegClass :=
      match r with
      | 0 => PublicReg   (* rX1 - base point, known to attacker *)
      | 5 => PublicReg   (* rA24 — curve constant, public *)
      | _ => SecretReg
      end.

    (* sum HW only over a given list of register indices *)
    Definition num_1s_regs (env : Env) (regs : list var) : nat :=
      fold_left (fun acc r => acc + HW (read_register env r)) regs 0.

    (* secret register indices for the ladder program *)
    Definition ladder_secret_regs : list var :=
      [ rX2; rZ2; rX3; rZ3
      ; rU; rV; rW; rT
      ; rU2; rV2; rUT; rVW
      ; rSp; rSm; rX3'; rSm2; rZ3'
      ; rX2'; rD; rAD; rT2; rZ2' ].

    (* total HW of secret registers across both sides of dual circuit *)
    Definition num_1s_secret_state (s : state) (regs : list var) : nat :=
      num_1s_regs s.(env) regs + num_1s_regs s.(denv) regs.

    (* security focused on secret registers only *)
    Definition secure_secret (prog : list instr) (s : state) (regs : list var) :=
      exists c, forall steps,
        num_1s_secret_state (run s prog steps).1 regs = c.

    (* helper: reading from a complemented env gives the complement *)
    Lemma read_register_map_not : forall (env : Env) (r : var),
      r < length env ->
      read_register (map bv_not env) r = bv_not (read_register env r).
    Proof.
      intros env r Hr. unfold read_register.
      unfold default_var. rewrite <- map_nth with (f := bv_not). apply nth_indep. rewrite length_map. auto.
    Qed.

    (* fold_left accumulator lemma for num_1s_regs — same pattern as fold_left_plus.
       NB: parameter named [e] not [env] to avoid shadowing the state field projector. *)
    Lemma num_1s_regs_fold_plus : forall (e : Env) (regs : list var) (acc : nat),
      fold_left (fun (acc : nat) (r : var) => acc + HW (read_register e r)) regs acc =
      fold_left (fun (acc : nat) (r : var) => acc + HW (read_register e r)) regs 0 + acc.
    Proof.
      induction regs as [| r rest IH]; simpl; intros acc.
      - lia.
      - rewrite IH. rewrite IH with (acc := HW (read_register e r)). lia.
    Qed.

    (* peeling the head off num_1s_regs *)
    Lemma num_1s_regs_cons : forall (e : Env) (r : var) (regs : list var),
      num_1s_regs e (r :: regs) = HW (read_register e r) + num_1s_regs e regs.
    Proof.
      intros e r regs. unfold num_1s_regs. simpl.
      rewrite num_1s_regs_fold_plus. lia.
    Qed.

    (* HW of secret registers is constant under valid_state *)
    Lemma valid_state_num_1s_regs : forall (s : state) (regs : list var),
      valid_state s ->
      (forall r, In r regs -> r < length s.(env)) ->
      num_1s_secret_state s regs = length regs * N.to_nat n.
    Proof.
      intros s regs Hvalid.
      (* introduce Hbounds AFTER induction so the IH generalises it for the tail *)
      induction regs as [| r rest IH]; intros Hbounds.
      - (* nil: both sides 0 *)
        unfold num_1s_secret_state, num_1s_regs. simpl. lia.
      - unfold num_1s_secret_state.
        rewrite !num_1s_regs_cons.
        (* head register: HW(env[r]) + HW(denv[r]) = n *)
        assert (Hstep : HW (read_register s.(env) r) + HW (read_register s.(denv) r) = N.to_nat n).
        { rewrite Hvalid.
          rewrite read_register_map_not.
          - apply hw_complement.
          - apply Hbounds. left. reflexivity. }
        (* tail: IH applies with bounds restricted to rest *)
        assert (IHapp : num_1s_secret_state s rest = length rest * N.to_nat n).
        { apply IH. intros r' Hr'. apply Hbounds. right. exact Hr'. }
        unfold num_1s_secret_state in IHapp.
        simpl length. lia.
    Qed.

    (* HW of secret registers is constant throughout execution *)
    Lemma all_secure_secret : forall (prog : list instr) (init_s : state),
      valid_state init_s ->
      (forall r, In r ladder_secret_regs -> r < length init_s.(env)) ->
      secure_secret prog init_s ladder_secret_regs.
    Proof.
      unfold secure_secret. intros prog init_s Hvalid Hbounds.
      exists (length ladder_secret_regs * N.to_nat n).
      intros steps.
      apply valid_state_num_1s_regs.
      - apply run_preserves_valid. exact Hvalid.
      - (* run preserves register bounds - needs a lemma? *)
        admit.
    Admitted.

    (* Compact register allocation *)

    Notation cX1  := 0  (only parsing).   (* public: base point x-coord     *)
    Notation cX2  := 1  (only parsing).   (* secret                          *)
    Notation cZ2  := 2  (only parsing).   (* secret                          *)
    Notation cX3  := 3  (only parsing).   (* secret                          *)
    Notation cZ3  := 4  (only parsing).   (* secret                          *)
    Notation cA24 := 5  (only parsing).   (* public: curve constant          *)
    Notation cT0  := 6  (only parsing).   (* temp, reused across the step   *)
    Notation cT1  := 7  (only parsing).   (* temp                             *)
    Notation cT2  := 8  (only parsing).   (* temp                            *)
    Notation cT3  := 9  (only parsing).   (* temp                            *)
    Notation cT4  := 10 (only parsing).   (* temp                            *)
    Notation cT5  := 11 (only parsing).   (* temp                            *)

    Definition compact_program : list instr :=
      [ IAdd cT0  cX2  cZ2    (* T0 = X2+Z2        = U                       *)
      ; ISub cT1  cX2  cZ2    (* T1 = X2−Z2        = V                       *)
      ; IAdd cT2  cX3  cZ3    (* T2 = X3+Z3        = W                       *)
      ; ISub cT3  cX3  cZ3    (* T3 = X3−Z3        = T                       *)
      ; IMul cT4  cT0  cT0    (* T4 = U·U          = U²                      *)
      ; IMul cT5  cT1  cT1    (* T5 = V·V          = V²   [peak: 8 live]     *)
      ; IMul cT0  cT0  cT3    (* T0 = U·T          = UT   [T3 dead]          *)
      ; IMul cT3  cT1  cT2    (* T3 = V·W          = VW   [T1,T2 dead]       *)
      ; IAdd cT1  cT0  cT3    (* T1 = UT+VW        = Sp                      *)
      ; ISub cT2  cT0  cT3    (* T2 = UT−VW        = Sm   [T0,T3 dead]       *)
      ; IMul cT1  cT1  cT1    (* T1 = Sp·Sp        = X3'                     *)
      ; IMul cT0  cT2  cT2    (* T0 = Sm·Sm        = Sm²  [T2 dead]          *)
      ; IMul cT2  cT0  cX1    (* T2 = Sm²·X1       = Z3'  [T0,X1 dead]       *)
      ; IMul cT0  cT4  cT5    (* T0 = U²·V²        = X2'                     *)
      ; ISub cT3  cT4  cT5    (* T3 = U²−V²        = D    [T4 dead]          *)
      ; IMul cT4  cA24 cT3    (* T4 = A24·D        = AD   [A24 dead]         *)
      ; IAdd cT5  cT5  cT4    (* T5 = V²+AD        = T2'  [T5,T4 dead]       *)
      ; IMul cT3  cT3  cT5    (* T3 = D·T2'        = Z2'  [T3,T5 dead]       *)
      ].
      (* Final: cT0=X2', cT1=X3', cT2=Z3', cT3=Z2'  (4 output regs)         *)

    (* Generalised public/secret classification
       declare a list of public registers --> derive the classify function from it *)

    Definition classify_by_list (pub : list var) (r : var) : RegClass :=
      if decide (r ∈ pub) then PublicReg else SecretReg.

    (* Retrofit the original program with the general classifier *)
    Definition ladder_public_regs : list var := [rX1; rA24].  (* 0 and 5     *)
    Definition ladder_classify' : var -> RegClass :=
      classify_by_list ladder_public_regs.

    (* Compact program: same two public inputs, same physical register slots  *)
    Definition compact_public_regs : list var := [cX1; cA24].  (* also 0,5   *)
    Definition compact_classify : var -> RegClass :=
      classify_by_list compact_public_regs.

    (* Secret registers for the compact program (everything except public)    *)
    Definition compact_secret_regs : list var :=
      [cX2; cZ2; cX3; cZ3; cT0; cT1; cT2; cT3; cT4; cT5].

    (* HW of secret registers in compact program is constant
       same proof structure as all_secure_secret?  *)
    Lemma compact_all_secure_secret : forall (init_s : state),
      valid_state init_s ->
      (forall r, In r compact_secret_regs -> r < length init_s.(env)) ->
      secure_secret compact_program init_s compact_secret_regs.
    Proof.
      unfold secure_secret. intros init_s Hvalid Hbounds.
      exists (length compact_secret_regs * N.to_nat n).
      intros steps.
      apply valid_state_num_1s_regs.
      - apply run_preserves_valid. exact Hvalid.
      - intros r Hr.
        rewrite run_preserves_length. apply Hbounds. exact Hr.
    Admitted.  (* valid_state_num_1s_regs *)

    (* 1. set of public registers --> public are not duplicated *)
        (* ISA contract? write another update function where only have shadow regs for secret *)

    (* run function on env --> list of obs --> functional correctness hold across run on env and on goal circuit *)
      (* definition of functional correctness - how to state *)
    (* observation of circuit & dual same at every  *)

    (* add memory? *)
      (* define machine: consists of registers & a memory --> 1. InstrMem: list of instructions (alt: store as bv --> translate to instr
         2. DataMem: store secret & public data
        --> implement a simple processor: program counter (also public), fetch --> memory respond in 1 cycle with instruction -->
         decode execute in single cycle *)
    (* hardware-software contract? *)
    (* language?  *)
    (* duplicate dynamically? some registers are 0 until you allocate a pair *)
  End DualCircuit.

  (* normal probability theory *)
  (* standard probability notation? *)
  (* probability > normal draws -->  *)
  (* justify from first principle? *)
    (* probability defined - in information theory library? *)

  (* end goal: number of 1's per cycle *)
  (* cryptographic accelerator? *)

  (* whether the number of 1's is the right metric of measuring power? *)

End HammingWeight.

(* Pipeline stages as an enum — mutually exclusive, exactly one active per cycle *)
Inductive PipelineStage :=
  | Fetch
  | Execute
  | WriteBack.

Module StateMachine.
Section StateMachine.
  Variable n : N.

  (* secret_map.(j) names which Regs slot is duplicated into DRegs slot j.
     e.g. secret_map.[0] = Fin 3 means DRegs[0] mirrors Regs[3].          *)
  Variable secret_map : Vector.t (Fin.t 32) 16.

  Record state := mkState {
    pc        : bv n;
    Regs      : Vector.t (bv n) 32;      (* all 32 general-purpose registers   *)
    DRegs     : Vector.t (bv n) 16;      (* dual of the 16 secret registers    *)
    InstrMem  : list instr;              (* program — public                   *)
    DataMem   : nat -> bv n;             (* data heap                          *)
    Stage     : PipelineStage;           (* current pipeline stage             *)
    (* instruction memory bus — public: carries opcodes, no duplication needed *)
    toiMem    : bool * bv n;             (* (valid, fetch addr)                *)
    fromiMem  : bool * bv n;             (* (valid, fetched instr)             *)
    (* data memory bus — may carry secret values, so dualized                  *)
    todMem    : bool * bv n * bv n;      (* (valid, addr, data)   write bus    *)
    dtodMem   : bool * bv n * bv n;      (* dual write bus                     *)
    fromdMem  : bool * bv n;             (* (valid, loaded data)  read bus     *)
    dfromdMem : bool * bv n;             (* dual read bus                      *)
  }.

  (* Invariant: every dual register is the bitwise complement of its secret original.
     DRegs[j] = bv_not (Regs[secret_map[j]])  for all j : Fin.t 16            *)
  Definition valid_state (s : state) : Prop :=
    forall j : Fin.t 16,
      Vector.nth s.(DRegs) j =
      bv_not (Vector.nth s.(Regs) (Vector.nth secret_map j)).

  (* Stage handlers — admitted until we flesh out the ISA semantics *)
  Definition fetch     : state -> state. Admitted.
  Definition execute   : state -> state. Admitted.
  Definition writeback : state -> state. Admitted.

  (* One clock tick: dispatch on the current pipeline stage *)
  Definition tick (s : state) : state :=
    match s.(Stage) with
    | Fetch     => fetch s
    | Execute   => execute s
    | WriteBack => writeback s
    end.

  (* Memory-side ticks — admitted until bus protocol is defined *)
  Definition tick_dMem : state -> state. Admitted.
  Definition tick_iMem : state -> state. Admitted.

  (* ── Security theorems ───────────────────────────────────────────────────── *)

  (* valid_state is preserved by each tick *)
  Lemma tick_preserves_valid : forall (s : state),
    valid_state s -> valid_state (tick s).
  Proof.
  Admitted.

  (* total HW of secret registers + their duals is constant per cycle *)
  (* (same dual-circuit argument as all_secure_secret, now for a full processor) *)

End StateMachine.
End StateMachine.
