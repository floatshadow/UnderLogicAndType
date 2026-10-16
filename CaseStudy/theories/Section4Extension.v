(** * Small programs from Section 4 (nondeterminism and persistence)

    Paper: Section 5 ("Supporting Nondeterminism", pp. 18-21) of the draft
    "Context Types: Bunched Modalities for Unifying Safety and Reachability".

    The first part of this file (the section below) contains the programs
    and their basic (erased) typings.  The second part (after the section)
    gives extended context typings [∅; Γ ⊢ₓ e ⋮ τ] for them, factored into
    fully proved structural derivations and separately named semantic
    obligations [<program>_obl_<what>], and documents the paper judgments
    that are NOT derivable in the Rocq system.  See the "Findings" comment
    block at the start of the second part. *)

(* The extra semantic imports must come before the ProofAutomation imports,
   otherwise [CoreLang.Sugar.vnat] shadows [CaseSyntax.vnat].  They are
   used by the semantic helper lemmas of Part 2 (round 1 also used them for
   a local copy of the generic subsumption lemmas, which is now replaced by
   the shared, proved [ProofAutomation.ExtendedSubsumption]). *)
From stdpp Require Import gmap.
From CoreLang Require Import Syntax BasicTyping BasicTypingProps.
From ContextTypeLanguage Require Import Syntax WF.
From ContextBasicDenotation Require Import RelevantEnv.
From Denotation Require Import TypeEquivCore TypePersistBase ConstDenoteBase.
From ContextLogic Require Import FormulaSemantics FormulaConnectives FormulaConnectivesHigher.
From ContextAlgebra Require Import ResourceInterface.
From ContextBasicDenotation Require Import BasicTypingFormula.
From Denotation Require Import Context.
From ContextTyping Require Import Typing PrimOpConcreteContext.
From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section Section4ExtensionExamples.

Definition z : atom := 401%positive.
Definition x : atom := 402%positive.
Definition y : atom := 403%positive.
Definition f : atom := 404%positive.
Definition y1 : atom := 405%positive.
Definition y2 : atom := 406%positive.
Definition r : atom := 407%positive.
Definition c : atom := 408%positive.
Definition c1 : atom := 409%positive.
Definition c2 : atom := 410%positive.

Definition bool_gen_program : tm :=
  op_boolGen ·₁ vbool false.

Definition nat_gen_program : tm :=
  op_natGen ·₁ vnat 0.

Definition nondet_choice_program : tm :=
  ret (vnat 0) ⊕ₙ ret (vnat 1).

Definition envir_x_program : tm :=
  let x := nat_gen_program in
  x ⟨ + ⟩ vnat 1.

Definition captured_z_fun : tm :=
  ret (ƛ x : 𝔹 => ret z).

Definition double_call_captured_z : tm :=
  let f := captured_z_fun in
  let y1 := f @ vbool true in
  let y2 := f @ vbool false in
  ret y2.

Definition nat_gen_fun : tm :=
  ret (ƛ x : 𝔹 => nat_gen_program).

Definition choice_fun : tm :=
  ret (ƛ x : 𝔹 => ret (vnat 0)) ⊕ₙ
  ret (ƛ x : 𝔹 => nat_gen_program).

Definition nonpersistent_choice_use : tm :=
  let f := choice_fun in
  let r := f @ vbool true in
  let c := op_eq0 ·₁ r in
  if c then
    f @ vbool false
  else
    ret (vnat 0).

Definition bool_equality_body : tm :=
  if y then
    if x then ret (vbool true) else ret (vbool false)
  else
    if x then ret (vbool false) else ret (vbool true).

Definition bool_gen_closure_program : tm :=
  let x := bool_gen_program in
  ret (ƛ y : 𝔹 => bool_equality_body).

Definition bool_gen_sum_program : tm :=
  bool_gen_program.


(** ** Additional (paper-faithful / A-normalised) variants

    The core T-AppFun rule only types applications [v1 @ x] whose argument is
    a variable, so the original programs above that apply [f] to the
    constants [vbool true]/[vbool false] are not derivable at all (see
    [double_call_captured_z_not_derivable] below).  The variants below bind
    the argument first ([let a := ret true in f @ a]).  [choice_fun_paper]
    restores the "+1" of the paper's [λx.0 ⊕ λx.gen_nat () + 1] (p. 20),
    which [choice_fun] drops. *)

Definition a : atom := 412%positive.

(** Paper p. 20, line 938: [λx.0 ⊕ λx.gen_nat () + 1]. *)
Definition choice_fun_paper : tm :=
  ret (ƛ x : 𝔹 => ret (vnat 0)) ⊕ₙ
  ret (ƛ y : 𝔹 => envir_x_program).

(** Paper p. 20, line 944 (marked ✗), A-normalised. *)
Definition nonpersistent_choice_use_paper : tm :=
  let f := choice_fun_paper in
  let a := ret (vbool true) in
  let r := f @ a in
  let c := op_eq0 ·₁ r in
  if c then
    f @ a
  else
    ret (vnat 0).

(** Paper p. 19, (e_ND) (marked ✗), literally (constant arguments). *)
Definition e_ND_program : tm :=
  let f := captured_z_fun in
  let y1 := f @ vbool true in
  let y2 := f @ vbool false in
  y1 ⟨-⟩ y2.

(** (e_ND), A-normalised. *)
Definition e_ND_anf_program : tm :=
  let f := captured_z_fun in
  let a := ret (vbool true) in
  let y1 := f @ a in
  let y2 := f @ a in
  y1 ⟨-⟩ y2.

(** The generator version of (e_ND) that p. 19-20 intends to be typable
    with T-LetI and a persistent [f], A-normalised. *)
Definition e_ND_gen_program : tm :=
  let f := nat_gen_fun in
  let a := ret (vbool true) in
  let y1 := f @ a in
  let y2 := f @ a in
  y1 ⟨-⟩ y2.

(** A-normalised version of [double_call_captured_z]. *)
Definition double_call_captured_z_anf : tm :=
  let f := captured_z_fun in
  let a := ret (vbool true) in
  let y1 := f @ a in
  let y2 := f @ a in
  ret y2.

Definition bool_to_nat_ty : ty := (𝔹 : ty) →ᵦ ℕ.
Definition bool_to_bool_ty : ty := (𝔹 : ty) →ᵦ 𝔹.

Lemma bool_gen_program_basic_type :
  ∅ ⊢ₑ bool_gen_program ⋮ 𝔹.
Proof. unfold bool_gen_program. basic_check. Qed.

Lemma bool_gen_program_extended_type :
  ∅; Emp ⊢ₓ bool_gen_program ⋮
    primop_precise_ty op_boolGen (vbool false).
Proof. unfold bool_gen_program. eapply EXT_AppOpValue. extended_wf. Qed.

Lemma nat_gen_program_basic_type :
  ∅ ⊢ₑ nat_gen_program ⋮ ℕ.
Proof. unfold nat_gen_program. basic_check. Qed.

Lemma nat_gen_program_extended_type :
  ∅; Emp ⊢ₓ nat_gen_program ⋮
    primop_precise_ty op_natGen (vnat 0).
Proof. unfold nat_gen_program. eapply EXT_AppOpValue. extended_wf. Qed.

Lemma nondet_choice_program_basic_type :
  ∅ ⊢ₑ nondet_choice_program ⋮ ℕ.
Proof. unfold nondet_choice_program. basic_check. Qed.

Lemma envir_x_program_basic_type :
  ∅ ⊢ₑ envir_x_program ⋮ ℕ.
Proof. unfold envir_x_program, nat_gen_program. basic_check. Qed.

Lemma captured_z_fun_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ captured_z_fun ⋮ bool_to_nat_ty.
Proof. unfold captured_z_fun, bool_to_nat_ty. basic_check. Qed.

Lemma double_call_captured_z_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ double_call_captured_z ⋮ ℕ.
Proof.
  unfold double_call_captured_z, bool_to_nat_ty.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply captured_z_fun_basic_type.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply basic_typing_let_named.
      * basic_type_fresh.
      * basic_check.
      * basic_check.
Qed.

Lemma nat_gen_fun_basic_type :
  ∅ ⊢ₑ nat_gen_fun ⋮ bool_to_nat_ty.
Proof. unfold nat_gen_fun, nat_gen_program, bool_to_nat_ty. basic_check. Qed.

Lemma choice_fun_basic_type :
  ∅ ⊢ₑ choice_fun ⋮ bool_to_nat_ty.
Proof. unfold choice_fun, nat_gen_program, bool_to_nat_ty. basic_check. Qed.

Lemma nonpersistent_choice_use_basic_type :
  ∅ ⊢ₑ nonpersistent_choice_use ⋮ ℕ.
Proof.
  unfold nonpersistent_choice_use.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply choice_fun_basic_type.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply basic_typing_let_named.
      * basic_type_fresh.
      * basic_check.
      * basic_check.
Qed.

Lemma bool_equality_body_basic_type :
  <[y := (𝔹 : ty)]> (<[x := (𝔹 : ty)]> ∅) ⊢ₑ bool_equality_body ⋮ 𝔹.
Proof. unfold bool_equality_body. basic_check. Qed.

Lemma bool_gen_closure_program_basic_type :
  ∅ ⊢ₑ bool_gen_closure_program ⋮ bool_to_bool_ty.
Proof.
  unfold bool_gen_closure_program, bool_gen_program, bool_equality_body,
    bool_to_bool_ty.
  basic_check.
Qed.

Lemma bool_gen_sum_program_basic_type :
  ∅ ⊢ₑ bool_gen_sum_program ⋮ 𝔹.
Proof. unfold bool_gen_sum_program, bool_gen_program. basic_check. Qed.


Lemma choice_fun_paper_basic_type :
  ∅ ⊢ₑ choice_fun_paper ⋮ bool_to_nat_ty.
Proof.
  unfold choice_fun_paper, envir_x_program, nat_gen_program, bool_to_nat_ty,
    base_ty_as_ty.
  basic_check.
Qed.

Lemma nonpersistent_choice_use_paper_basic_type :
  ∅ ⊢ₑ nonpersistent_choice_use_paper ⋮ ℕ.
Proof.
  unfold nonpersistent_choice_use_paper.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply choice_fun_paper_basic_type.
  - unfold base_ty_as_ty. basic_check.
Qed.

Lemma e_ND_program_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ e_ND_program ⋮ ℕ.
Proof.
  unfold e_ND_program.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply captured_z_fun_basic_type.
  - unfold base_ty_as_ty. basic_check.
Qed.

Lemma e_ND_anf_program_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ e_ND_anf_program ⋮ ℕ.
Proof.
  unfold e_ND_anf_program.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply captured_z_fun_basic_type.
  - unfold base_ty_as_ty. basic_check.
Qed.

Lemma e_ND_gen_program_basic_type :
  ∅ ⊢ₑ e_ND_gen_program ⋮ ℕ.
Proof.
  unfold e_ND_gen_program.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply nat_gen_fun_basic_type.
  - unfold base_ty_as_ty. basic_check.
Qed.

Lemma double_call_captured_z_anf_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ double_call_captured_z_anf ⋮ ℕ.
Proof.
  unfold double_call_captured_z_anf.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply captured_z_fun_basic_type.
  - unfold base_ty_as_ty. basic_check.
Qed.

End Section4ExtensionExamples.

(** * Part 2: extended context typings

    ** Translation conventions

    - The paper's [unit] argument of thunks is modelled by [𝔹] (Rocq has no
      unit base type); [{ν:unit | ⊤}] becomes [OBool = {: 𝔹 | qual_top}].
    - The paper's [int]/[nat] become [ℕ]; [e1 - e2] is truncated subtraction.
    - [gen_b ()] is [op_bGen ·₁ <dummy constant>] ([nat_gen_program],
      [bool_gen_program]); [concrete_Φ] only gives primitives the top/top
      signature, so the precise case-study rule [EXT_AppOpValue] is used.
    - [e1 ⊕ e2] is [nondet_tm], i.e. [let b := boolGen false in if b ...]
      (paper footnote 7).
    - The paper's angelic top type [[ν:b | ⊤]] ("every value of [b] is
      reachable") is the SHARED alias [U[b]] / [UNat] / [UBool] =
      [[: b | q_base_all b]] of [CaseTypes] (round 2).  Its qualifier
      mentions [ν], so its exact atom demands that every value of [b] be
      reached.  (Round 1 used local aliases [NatTop]/[BoolTop] because the
      shared [U[b]] was then the vacuous [[: b | qual_top]], see F1; those
      local aliases are now gone and every statement uses [UNat]/[UBool].)
    - [{ν:nat | ν > 0}]-style under types use [q_nat_pred]; ℕ instead of
      int changes nothing in the qualifiers used here ([x+1 > 0] holds for
      every natural; [y1 - y2] is truncated subtraction, which still reaches
      every natural via [y2 = 0]).

    ** Findings (dependency / expressiveness problems found while typing)

    F1 (round 1, now FIXED in the shared library) the old aliases
       [U[b] = [: b | qual_top]] were vacuous: [qual_top] has an empty
       variable set, so [FUnder (FAtom qual_top)] is valid
       ([s4_under_qual_top_vacuous], kept as documentation), [ret 0]
       inhabited the old [UNat], and every ⊕-split of a generated boolean was
       false.  With the faithful [U[b]] all statements of this file have the
       intended meaning; they are semantically identical to round 1's
       [NatTop]/[BoolTop] statements ([q_base_all ℕ] and
       [q_nat_pred ν (λ _, True)] have the same satisfying stores).

    F2 T-AppFun (and T-AppFunD) only accept a variable argument.  The
       original programs [double_call_captured_z], [nonpersistent_choice_use]
       and the literal (e_ND) [e_ND_program] apply [f] to constants and are
       provably not derivable at ANY context/type
       ([double_call_captured_z_not_derivable],
        [nonpersistent_choice_use_not_derivable], [e_ND_program_not_derivable]);
       these proofs are by induction on the derivation and cover the new
       round-2 rules (T-VarComma and T-FixUnroll conclude [ret _] terms,
       T-CtxCase keeps the term, the named matches have a different head).
       The A-normalised variants [*_anf] are used instead.

    F3 [nonpersistent_choice_use] (Rocq transcription of the ✗ example of
       p. 20, l. 944) drops the "+1" of [λx.gen_nat () + 1].  Without it the
       program is NOT a counterexample: if [f] is the generator closure and
       its first call returns [0], the second call [f false] reaches every
       natural number, so [[ν:nat|⊤]] holds semantically.  The faithful
       version is [nonpersistent_choice_use_paper] (with [choice_fun_paper]);
       as in the paper we do not type it.  Its target [∅ ⊢ … : [ν:nat|⊤]] is
       SEMANTICALLY FALSE: [f] is (call-by-value) either [λx.0], and then
       [f a = 0] so the then-branch returns [f a = 0], or [λx.gen_nat () + 1],
       and then [f a > 0] so the else-branch returns [0].  Every run returns
       [0], so the ν-projection of any result world is [{0}] ≠ ℕ and the
       angelic [[ν:nat|⊤]] (= [UNat]) fails; the precise type [ν = 0] is the
       true one.  (The ✗ of the paper is thus both a non-derivability and a
       semantic-invalidity mark.)

    F4 Persistence works, but not through duplication.  The paper's
       [x:□τ ≤_{x} x:□τ ∗ x:□τ] (p. 19) is not a well-formed context in
       Rocq ([basic_ctx] for [CtxStar] requires disjoint domains,
       [s4_persist_dup_ctx_ill_formed]), so that literal CtxSub step cannot
       be replayed.  It is not needed: the generator (e_ND),
       [e_ND_gen_program : [ν:nat|⊤]], IS derivable
       ([e_ND_gen_program_extended_type]) by binding [f : □(..)] and a precise
       argument [a] with T-Let, then turning [Γa ,, y1:[nat|⊤]] into
       [Γa ∗ y1:[nat|⊤]] with a CtxSub that is valid precisely because [□]
       makes the [f]-projection a singleton
       ([e_ND_gen_program_obl_comma_to_star], proved), and finally using
       T-LetI ([EXT_LetDNamed]) with [Γ1 = Γa] for the second call.  The
       remaining semantic obligations are [□τ <: τ] (T-PersE) and the
       subtraction subtyping under [y1 ∗ y2] (both Admitted with arguments).
       Using T-Let for the second call instead gets stuck on a false premise
       ([e_ND_gen_program_reduces_to_obl]).
       Caveat: the program needs the argument [a] to be precise
       ([{ν=true}⊓[ν=true]]) rather than [{𝔹|⊤}] — an over-approximate
       argument variable has no singleton projection, and the comma-to-star
       step would fail.

    F5 Matching on a variable.
       (a) (round 1: "not derivable"; round 2: DERIVABLE) a demonic
           scrutinee [y : {ν:bool|⊤}] cannot be split by T-CtxSub into
           [Γt ⊕ Γf] (the world [{y↦true}] has no non-empty [false] part),
           but the new T-CtxCase splits it into "true only" / "false only" /
           "both": [bool_gen_closure_program_obool_wand_type] types
           [let x = gen_bool () in λy. y == x] at
           [y:{bool|⊤} -∗ [ν:bool|⊤]].
       (b) the ENTANGLED arrows [y:{bool|⊤} → [ν:bool|⊤]] and
           [y:[bool|⊤] → [ν:bool|⊤]] are SEMANTICALLY FALSE for that program
           (the argument may be correlated with the closure; counterexample
           in the comment before [bool_gen_closure_program_obool_wand_type]),
           so no rule can or should derive them;
       (c) the independent arrow [y:[bool|⊤] -∗ ...] works:
           [bool_gen_closure_program_wand_type].

    F6 T-PersI applies only to syntactic values ([ret v]); the paper's
       non-persistence of [λx.0 ⊕ λx.gen()+1] is thus also syntactic in Rocq
       ([choice_fun] is a [let], not a value), while [λx.z] fails because
       [z ∷ [ν:nat|⊤]] is not a persistent context (informal: the angelic
       binding needs ≥ 2 values of [z], so no singleton projection exists).

    F7/F8 (round 1, shared lemmas; now resolved in the library) the old
       [subtype_under_closed_by_qualifier] and
       [subtype_inter_over_under_to_under(_and)] were false as stated; this
       file uses the shared proved [*_corrected] versions (extra premises:
       variable inclusion and satisfiability of the target qualifier,
       discharged by [q_base_all_bool_sat] / [q_base_all_nat_sat]).

    F9 (round 2) the judgment of p. 19, l. 884,
       [z:[ν:nat|⊤] ⊢ λx.z + 1 : {ν:unit|⊤} → [ν:nat|0 < ν]], is now
       transcribed verbatim as [captured_z_succ_fun] and typed
       ([captured_z_succ_fun_extended_type]).  (An earlier round-2 draft of
       this comment claimed the paper prints [λx.x + 1]; that was a misreading
       — the PDF prints [λx.z + 1].) *)

(** ** Vacuity of [qual_top] under-types (finding F1). *)

Lemma s4_under_qual_top_vacuous (m : WfWorld (V := value)) :
  m ⊨ FUnder (FAtom (V := value) qual_top).
Proof.
  apply res_models_under_intro_same_from_model.
  exact (res_models_atom_top m).
Qed.

(** ** The persistent duplication context is ill-formed (finding F4). *)

Lemma s4_persist_dup_ctx_ill_formed (g : atom) (τ : context_ty) :
  ~ wf_ctx_under ∅ ((g ∷ □ τ) ∗ (g ∷ □ τ)).
Proof.
  unfold wf_ctx_under. cbn [basic_ctx ctx_dom]. intros (_ & _ & Hd). set_solver.
Qed.

(** ** Local semantic helper lemmas (proved) *)

Lemma s4_persistent_formula_of_fv_empty (φ : Formula (V := value)) :
  formula_fv φ = ∅ -> persistent_formula φ.
Proof.
  intros Hfv m Hm.
  assert (Heq : res_restrict m ∅ =
    (exist _ (singleton_world ∅) (wf_singleton_world ∅) : WfWorld)).
  { apply wfworld_ext. apply world_ext.
    - rewrite res_restrict_dom. cbn. set_solver.
    - intros σ. split.
      + intros [σ0 [_ Hσ]]. cbn. subst σ. apply map_eq. intros k.
        apply storeA_restrict_lookup_none_r. set_solver.
      + cbn. intros ->. destruct (world_wf m) as [[σ0 Hσ0] _].
        exists σ0. split; [exact Hσ0| ].
        apply map_eq. intros k. apply storeA_restrict_lookup_none_r. set_solver. }
  eapply res_models_persist_intro with (σ := ∅).
  - rewrite Hfv. reflexivity.
  - rewrite Hfv. exact Heq.
  - rewrite <- Heq.
    apply (proj1 (res_models_minimal_on ∅ m φ ltac:(rewrite Hfv; reflexivity))).
    exact Hm.
Qed.

(** The empty typing context is persistent (premise of T-PersI). *)
Lemma s4_persistent_emp : persistent_formula (ctx_denote_under ∅ Emp).
Proof.
  apply s4_persistent_formula_of_fv_empty.
  cbn [ctx_denote_under].
  rewrite formula_fv_and, (formula_fv_true (V:=value)), formula_fv_basic_world_formula.
  reflexivity.
Qed.

Lemma s4_store_restrict_empty_ty (X : aset) :
  storeA_restrict (∅ : gmap atom ty) X = ∅.
Proof. apply map_eq. intros k. apply storeA_restrict_lookup_none_l. reflexivity. Qed.

Lemma s4_store_restrict_to_empty_ty (Σ : gmap atom ty) :
  storeA_restrict Σ ∅ = ∅.
Proof. apply map_eq. intros k. apply storeA_restrict_lookup_none_r. set_solver. Qed.

Lemma s4_ctx_denote_under_closed Σ Γ :
  ctx_fv Γ = ∅ -> ctx_denote_under Σ Γ = ctx_denote_under ∅ Γ.
Proof.
  intros H. destruct Γ; cbn [ctx_denote_under];
    rewrite H, !s4_store_restrict_to_empty_ty; reflexivity.
Qed.

Lemma s4_ctx_denote_under_emp_models (m : WfWorld) :
  m ⊨ ctx_denote_under ∅ Emp.
Proof.
  cbn [ctx_denote_under erase_ctx]. apply res_models_and_intro_from_models.
  - exact (basic_world_formula_empty m).
  - apply res_models_true.
Qed.

(** Weakening to the empty context (only for closed judgments, X = ∅). *)
Lemma s4_ctx_sub_to_emp X Γ :
  wf_ctx_under ∅ Γ -> X = ∅ -> ctx_sub_under ∅ X Γ Emp.
Proof.
  intros Hwf ->. split; [exact Hwf| ]. split; [exact I| ]. split.
  - intros a Ha. set_solver.
  - intros r _. exists r. split; [apply res_restrict_le| ].
    apply s4_ctx_denote_under_emp_models.
Qed.

(** [Γ1 ,, Γ2 ≤ Γ1]: drop the (dependent) right part. *)
Lemma s4_ctx_sub_comma_drop_right X Γ1 Γ2 :
  wf_ctx_under ∅ (Γ1 ,, Γ2) -> X ⊆ ctx_dom Γ1 ->
  ctx_sub_under ∅ X (Γ1 ,, Γ2) Γ1.
Proof.
  intros Hwf HX. pose proof Hwf as Hwf0. unfold wf_ctx_under in Hwf.
  cbn [basic_ctx] in Hwf. destruct Hwf as (H1 & H2 & Hdisj).
  split; [exact Hwf0| ]. split; [exact H1| ]. split.
  - intros a Ha. cbn [erase_ctx].
    pose proof (basic_ctx_erase_dom _ _ H1) as Hd1.
    destruct (erase_ctx Γ1 !! a) eqn:Hl.
    + apply lookup_union_Some_l. exact Hl.
    + exfalso. apply not_elem_of_dom in Hl. rewrite Hd1 in Hl. set_solver.
  - intros r Hr. exists r. split; [apply res_restrict_le| ].
    cbn [ctx_denote_under] in Hr. rewrite !s4_store_restrict_empty_ty in Hr.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [Hr _]. exact Hr.
Qed.

(** [Γ1 ,, Γ2 ≤ Γ2] when [Γ2] does not mention [Γ1]'s variables. *)
Lemma s4_ctx_sub_comma_drop_left_closed X Γ1 Γ2 :
  wf_ctx_under ∅ (Γ1 ,, Γ2) -> wf_ctx_under ∅ Γ2 -> ctx_fv Γ2 = ∅ ->
  X ⊆ ctx_dom Γ2 ->
  ctx_sub_under ∅ X (Γ1 ,, Γ2) Γ2.
Proof.
  intros Hwf Hwf2 Hfv HX. pose proof Hwf as Hwf0. unfold wf_ctx_under in Hwf.
  cbn [basic_ctx] in Hwf. destruct Hwf as (H1 & H2 & Hdisj).
  split; [exact Hwf0| ]. split; [exact Hwf2| ]. split.
  - intros a Ha. cbn [erase_ctx].
    pose proof (basic_ctx_erase_dom _ _ H1) as Hd1.
    destruct (erase_ctx Γ1 !! a) eqn:Hl.
    + exfalso. apply elem_of_dom_2 in Hl. rewrite Hd1 in Hl. set_solver.
    + apply lookup_union_r. exact Hl.
  - intros r Hr. exists r. split; [apply res_restrict_le| ].
    cbn [ctx_denote_under] in Hr.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_and_iff in Hr as [_ Hr].
    rewrite s4_ctx_denote_under_closed in Hr by exact Hfv. exact Hr.
Qed.

(** [Γ1 ∗ Γ2 ≤ Γ1] and [Γ1 ∗ Γ2 ≤ Γ2] (affine projections of ∗). *)
Lemma s4_ctx_sub_star_drop_right X Γ1 Γ2 :
  wf_ctx_under ∅ (Γ1 ∗ Γ2) -> X ⊆ ctx_dom Γ1 ->
  ctx_sub_under ∅ X (Γ1 ∗ Γ2) Γ1.
Proof.
  intros Hwf HX. pose proof Hwf as Hwf0. unfold wf_ctx_under in Hwf.
  cbn [basic_ctx] in Hwf. destruct Hwf as (H1 & H2 & Hdisj).
  split; [exact Hwf0| ]. split; [exact H1| ]. split.
  - intros a Ha. cbn [erase_ctx].
    pose proof (basic_ctx_erase_dom _ _ H1) as Hd1.
    destruct (erase_ctx Γ1 !! a) eqn:Hl.
    + apply lookup_union_Some_l. exact Hl.
    + exfalso. apply not_elem_of_dom in Hl. rewrite Hd1 in Hl. set_solver.
  - intros r Hr. exists r. split; [apply res_restrict_le| ].
    cbn [ctx_denote_under] in Hr. rewrite !s4_store_restrict_empty_ty in Hr.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_star_iff in Hr as [m1 [m2 [Hc [Hle [Hm1 _]]]]].
    eapply res_models_kripke; [ | exact Hm1].
    etransitivity; [apply res_product_le_l | exact Hle].
Qed.

Lemma s4_ctx_sub_star_drop_left X Γ1 Γ2 :
  wf_ctx_under ∅ (Γ1 ∗ Γ2) -> X ⊆ ctx_dom Γ2 ->
  ctx_sub_under ∅ X (Γ1 ∗ Γ2) Γ2.
Proof.
  intros Hwf HX. pose proof Hwf as Hwf0. unfold wf_ctx_under in Hwf.
  cbn [basic_ctx] in Hwf. destruct Hwf as (H1 & H2 & Hdisj).
  split; [exact Hwf0| ]. split; [exact H2| ]. split.
  - intros a Ha. cbn [erase_ctx].
    pose proof (basic_ctx_erase_dom _ _ H1) as Hd1.
    destruct (erase_ctx Γ1 !! a) eqn:Hl.
    + exfalso. apply elem_of_dom_2 in Hl. rewrite Hd1 in Hl. set_solver.
    + apply lookup_union_r. exact Hl.
  - intros r Hr. exists r. split; [apply res_restrict_le| ].
    cbn [ctx_denote_under] in Hr. rewrite !s4_store_restrict_empty_ty in Hr.
    apply res_models_and_iff in Hr as [_ Hr].
    apply res_models_star_iff in Hr as [m1 [m2 [Hc [Hle [_ Hm2]]]]].
    eapply res_models_kripke; [ | exact Hm2].
    etransitivity; [apply res_product_le_r | exact Hle].
Qed.

(** T-AppFun specialised to a result type that does not depend on the
    argument (so [{0 ~> a} τ = τ]). *)
Lemma s4_ext_appfun_closed Σ Γ τx τ v1 (a : atom) :
  cty_open 0 a τ = τ ->
  Σ; Γ ⊢wf v1 @ a ⋮ τ ->
  a ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  Σ; Γ ⊢ₓ ret v1 ⋮ (τx → τ) ->
  Σ; Γ ⊢ₓ ret (avar a) ⋮ τx ->
  Σ; Γ ⊢ₓ v1 @ a ⋮ τ.
Proof.
  intros Hopen Hwf Hfresh Hf Ha.
  pose proof (EXT_AppFun Σ Γ τx τ v1 a) as H.
  change (open_one 0 a τ) with (cty_open 0 a τ) in H.
  rewrite Hopen in H. exact (H Hwf Hfresh Hf Ha).
Qed.

(** ** Target types *)

Definition q_nat_pos : type_qualifier := q_nat_pred vnu (fun n => 0 < n).
Definition UNatPos : context_ty := [: TNat | q_nat_pos].
Definition bool_sum_over_ty : context_ty := {: TBool | q_true} ⊕ {: TBool | q_false}.

Definition nat01_sum_ty : context_ty :=
  const_precise_ty (cnat 0) ⊕ const_precise_ty (cnat 1).

Definition bool_split_ctx (b : atom) : ctx :=
  (b ∷ bool_precise_ty true) ⊕ (b ∷ bool_precise_ty false).

Ltac s4_unfold_progs :=
  unfold choice_fun_paper, bool_gen_sum_program, bool_gen_program, nat_gen_program, envir_x_program,
    captured_z_fun, nat_gen_fun, choice_fun, nondet_choice_program,
    bool_gen_closure_program, bool_equality_body in *.

Ltac s4_none :=
  first [ apply lookup_empty
        | apply lookup_singleton_None;
          solve [congruence | set_solver | (intro; subst; set_solver) | discriminate]
        | apply lookup_union_None; split; s4_none
        | apply lookup_insert_None; split;
          [s4_none | solve [congruence | set_solver | discriminate]] ].

Ltac s4_lookup_raw :=
  first [ apply lookup_singleton_Some; split; reflexivity
        | apply lookup_insert_Some; left; split; reflexivity
        | apply lookup_insert_Some; right; split;
          [solve [congruence | set_solver | discriminate] | s4_lookup_raw]
        | apply lookup_union_Some_raw;
          first [ left; s4_lookup_raw | right; split; [s4_none | s4_lookup_raw] ] ].

Ltac s4_lookup := cbn [erase_ctx] in *; s4_lookup_raw.

Ltac s4_fresh := apply not_elem_of_dom; s4_none.

Ltac s4_basic :=
  unfold avar, vnat, vbool, Ret, case_app, prim_app, if_named in *;
  repeat match goal with
  | |- _ ⊢ₑ nondet_tm _ _ ⋮ _ => eapply basic_typing_nondet_tm
  | |- _ ⊢ₑ let_named _ _ _ ⋮ _ =>
      eapply basic_typing_let_named; [s4_fresh | | ]
  | |- _ ⊢ᵥ lam_named _ _ _ ⋮ _ =>
      eapply basic_typing_lam_named; [s4_fresh | ]
  | |- _ ⊢ₑ tret _ ⋮ _ => apply TT_Ret
  | |- _ ⊢ₑ tmatch _ _ _ ⋮ _ => apply TT_Match
  | |- _ ⊢ₑ tprim _ _ ⋮ _ => eapply TT_Op; [reflexivity | ]
  | |- _ ⊢ₑ tbinop _ _ _ ⋮ _ => eapply TT_BinOp; [reflexivity | | ]
  | |- _ ⊢ₑ tapp _ _ ⋮ _ => eapply TT_App
  | |- _ ⊢ₑ tlete _ _ ⋮ _ =>
      eapply (TT_Let _ _ _ _ _ ∅); [ | intros ? ?; cbn]
  | |- context [decide (?u = ?u)] => rewrite (decide_True (P := u = u)) by reflexivity
  | |- _ ⊢ᵥ vconst _ ⋮ _ => apply VT_Const
  | |- _ ⊢ᵥ vfvar _ ⋮ _ => apply VT_FVar; s4_lookup
  | |- _ ⊢ᵥ vlam _ _ ⋮ _ => apply (VT_Lam _ _ _ _ ∅); intros ? ?; cbn
  end.

Ltac s4_unfold_tys :=
  unfold UNat, UBool, q_base_all, q_nat_pred, q_bool_pred,
    q_const_pred, UNatPos, q_nat_pos, nat01_sum_ty, bool_sum_over_ty, vnu in *.

Ltac s4_wf :=
  s4_unfold_progs; s4_unfold_progs; s4_unfold_tys;
  extended_wf;
  try (unfold ONat, UNat, OBool, UBool, q_base_all, q_nat_pred, q_bool_pred, q_const_pred, UNatPos, base_ty_as_ty, const_precise_ty,
         bool_precise_ty, precise_ty, over_ty, under_ty, bool_to_nat_ty,
         bool_to_bool_ty in *;
       cbn [erase_ctx erase_ty base_ty_of_const] in *;
       solve [s4_basic]).

Ltac s4_fv :=
  s4_unfold_progs; s4_unfold_progs; s4_unfold_tys;
  unfold q_true, q_false, bool_split_ctx,
    ONat, UNat, OBool, UBool, over_ty, under_ty, qual_top,
    bool_precise_ty, const_precise_ty, precise_ty, bool_qual,
    mk_q_eq, primop_precise_ty, primop_result_qual, binop_precise_ty,
    binop_result_qual in *;
  cbn [ctx_fv ctx_dom] in *;
  unfold fv_cty, context_ty_lvars in *;
  cbn in *;
  repeat rewrite ?lvars_fv_union, ?lvars_fv_lvars_at_depth,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free, ?lvars_fv_empty;
  first [ reflexivity | set_solver ].

Lemma s4_lso_restrict_lookup D' D (s : LStoreOn (V := value) D) (H : D' ⊆ D) k :
  lso_store (lstore_on_restrict D' s H) !! k =
  if decide (k ∈ D') then lso_store s !! k else None.
Proof. destruct s as [s Hs]. cbn. apply storeA_restrict_lookup. Qed.

(** Satisfiability of the angelic-top qualifiers (premise of the corrected
    [subtype_under_closed_by_qualifier]). *)
Lemma q_base_all_bool_sat : exists s, qual_prop (q_base_all TBool) s.
Proof.
  unfold q_base_all, q_const_pred, vnu.
  cbn [qual_vars qual_prop lvar_value_keys].
  unshelve eexists {| storeAO_store := {[LVBound 0 := vconst (cbool true)]} |}.
  - rewrite dom_singleton_L. reflexivity.
  - exists (cbool true). split; [ | reflexivity].
    cbn [lso_store storeAO_store denote_lvar_value].
    apply lookup_singleton_Some. split; reflexivity.
Qed.

Lemma q_base_all_nat_sat : exists s, qual_prop (q_base_all TNat) s.
Proof.
  unfold q_base_all, q_const_pred, vnu.
  cbn [qual_vars qual_prop lvar_value_keys].
  unshelve eexists {| storeAO_store := {[LVBound 0 := vconst (cnat 0)]} |}.
  - rewrite dom_singleton_L. reflexivity.
  - exists (cnat 0). split; [ | reflexivity].
    cbn [lso_store storeAO_store denote_lvar_value].
    apply lookup_singleton_Some. split; reflexivity.
Qed.

(** ** gen_bool () : [ν:bool|⊤]  (p. 20, l. 972, left premise)

    Obligation: precise result type of [boolGen] is below [UBool].  Proved
    (Qed, no admitted lemma) from the shared CORRECTED generic lemmas of
    [ExtendedSubsumption]; the extra premises (variable inclusion, satisfiability
    of [q_bool_any]) are discharged here, as is the qualifier implication
    "ν is a bool ⇒ boolGen false ⇝ ν". *)
Lemma bool_gen_program_obl_sub_under :
  sub_type_under ∅ Emp (primop_precise_ty op_boolGen (vbool false)) UBool.
Proof.
  set (q := primop_result_qual op_boolGen (vbool false)).
  change (extended_semantic_subtype ∅ Emp
    (({: TBool | q}) ⊓ ([: TBool | q])) ([: TBool | q_base_all TBool])).
  apply subtype_inter_over_under_to_under_corrected.
  - unfold q. s4_wf.
  - cbn [ctx_dom]. set_solver.
  - cbn [ctx_dom]. set_solver.
  - set_solver.
  - apply subtype_under_closed_by_qualifier_corrected.
    + unfold q. s4_wf.
    + cbn [ctx_dom]. set_solver.
    + cbn [ctx_dom]. set_solver.
    + unfold qualifier_entails. intros st Hst.
      unfold q_base_all, q_const_pred, q, primop_result_qual, qual_and in *.
      cbn [qual_prop qual_vars qual_lvars] in *.
      unfold vnu, vbool in *.
      destruct Hst as [c [Hc Hcb]].
      cbn [denote_lvar_value] in *.
      rewrite !s4_lso_restrict_lookup in *.
      repeat (rewrite decide_True in * by (cbn [lvar_value_keys]; set_solver)).
      destruct c as [bb|m0|tt0|ll0]; cbn [base_ty_of_const] in Hcb; try discriminate.
      split; exists (cbool false), (cbool bb); repeat split; try reflexivity;
        try exact Hc; constructor.
    + unfold q_base_all, q_const_pred, q, primop_result_qual.
      cbn [qual_vars]. set_solver.
    + exact q_base_all_bool_sat.
Qed.

Lemma bool_gen_program_under_type :
  ∅; Emp ⊢ₓ bool_gen_program ⋮ UBool.
Proof.
  unfold bool_gen_program.
  eapply EXT_Sub; [extended_wf | eapply EXT_AppOpValue; extended_wf | ].
  exact bool_gen_program_obl_sub_under.
Qed.

(** ** gen_bool () : {ν=true} ⊕ {ν=false}  (p. 20, l. 972-973)

    [bool_gen_sum_program_obl_sub_sum] (ADMITTED, believed true):
    the paper's subtyping [[ν:bool|⊤] <: {ν=true} ⊕ {ν=false}] under ∅,
    which only holds with the lifted sum denotation of §5.2 (implemented in
    [ty_denote_gas] by [FForall (result ⇒ FPlus ..)]).
    Informal argument: let [m ⊨ [[UBool]] e] and extend [m] by the result
    variable [ν] of [e].  The guard gives that every value of [ν] is a
    boolean; the under part ([FFibVars ∅ (FUnder (FAtom q_bool_any))])
    gives a sub-world whose [ν]-projection is exactly [{true,false}], hence
    the [ν]-projection of [m_ν] is exactly [{true,false}].  Split [m_ν]
    (restricted to [{ν}]) into the non-empty worlds [m1 = {ν ↦ true}] and
    [m2 = {ν ↦ false}]; [m1 + m2 ⊑ m_ν], [m1 ⊨ [[{ν=true}]] ν] and
    [m2 ⊨ [[{ν=false}]] ν] (all stores satisfy the over-qualifier; the guards
    hold since [ret ν] is total and well typed).  Note this was FALSE with
    the round-1 vacuous [U[bool]] (finding F1). *)
Lemma bool_gen_sum_program_obl_sub_sum :
  sub_type_under ∅ Emp UBool bool_sum_over_ty.
Admitted.

Lemma bool_gen_sum_program_extended_type :
  ∅; Emp ⊢ₓ bool_gen_sum_program ⋮ bool_sum_over_ty.
Proof.
  unfold bool_gen_sum_program.
  eapply EXT_Sub; [unfold bool_sum_over_ty; s4_wf | exact bool_gen_program_under_type | ].
  exact bool_gen_sum_program_obl_sub_sum.
Qed.

(** ** gen_nat () : [ν:nat|⊤]  (p. 19, l. 908 / p. 20, l. 937)
    Proved like [bool_gen_program_obl_sub_under] (corrected lemmas). *)
Lemma nat_gen_program_obl_sub_under :
  sub_type_under ∅ Emp (primop_precise_ty op_natGen (vnat 0)) UNat.
Proof.
  set (q := primop_result_qual op_natGen (vnat 0)).
  change (extended_semantic_subtype ∅ Emp
    (({: TNat | q}) ⊓ ([: TNat | q])) ([: TNat | q_base_all TNat])).
  apply subtype_inter_over_under_to_under_corrected.
  - unfold q. s4_wf.
  - cbn [ctx_dom]. set_solver.
  - cbn [ctx_dom]. set_solver.
  - set_solver.
  - apply subtype_under_closed_by_qualifier_corrected.
    + unfold q. s4_wf.
    + cbn [ctx_dom]. set_solver.
    + cbn [ctx_dom]. set_solver.
    + unfold qualifier_entails. intros st Hst.
      unfold q_base_all, q_const_pred, q, primop_result_qual, qual_and in *.
      cbn [qual_prop qual_vars qual_lvars] in *.
      unfold vnu, vnat in *.
      destruct Hst as [c [Hc Hcb]].
      cbn [denote_lvar_value] in *.
      rewrite !s4_lso_restrict_lookup in *.
      repeat (rewrite decide_True in * by (cbn [lvar_value_keys]; set_solver)).
      destruct c as [bb|m0|tt0|ll0]; cbn [base_ty_of_const] in Hcb; try discriminate.
      split; exists (cnat 0), (cnat m0); repeat split; try reflexivity;
        try exact Hc; constructor.
    + unfold q_base_all, q_const_pred, q, primop_result_qual.
      cbn [qual_vars]. set_solver.
    + exact q_base_all_nat_sat.
Qed.

Lemma nat_gen_program_under_type :
  ∅; Emp ⊢ₓ nat_gen_program ⋮ UNat.
Proof.
  eapply EXT_Sub; [s4_wf | apply nat_gen_program_extended_type | ].
  exact nat_gen_program_obl_sub_under.
Qed.

Lemma nat_gen_fun_extended_type :
  ∅; Emp ⊢ₓ nat_gen_fun ⋮ (OBool → UNat).
Proof.
  unfold nat_gen_fun.
  eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
  eapply EXT_CtxSub; [s4_wf | apply nat_gen_program_under_type | ].
  apply s4_ctx_sub_to_emp; [s4_wf | ].
  s4_fv.
Qed.

(** ** gen_nat : □({ν:unit|⊤} → [ν:nat|⊤])   (p. 19, l. 908; p. 20, l. 937)
    Here [gen_nat] is the thunk [λx:𝔹. gen_nat 0]; T-PersI applies because
    the empty context is persistent ([s4_persistent_emp], proved). *)
Lemma nat_gen_fun_persistent_type :
  ∅; Emp ⊢ₓ nat_gen_fun ⋮ (□ (OBool → UNat)).
Proof.
  unfold nat_gen_fun.
  eapply EXT_PersistIntro; [s4_wf | exact s4_persistent_emp | ].
  exact nat_gen_fun_extended_type.
Qed.

(** ** z:[ν:nat|⊤] ⊢ λx.z : {ν:unit|⊤} → [ν:nat|⊤]   (p. 20, l. 936 ✓)
    Fully proved (no obligations).  It cannot be made persistent: T-PersI
    would need [persistent_formula ⟦z ∷ [ν:nat|⊤]⟧], which fails (F6). *)
Lemma captured_z_fun_extended_type :
  ∅; z ∷ UNat ⊢ₓ captured_z_fun ⋮ (OBool → UNat).
Proof.
  unfold captured_z_fun.
  eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
  eapply EXT_CtxSub; [s4_wf | eapply EXT_Var; s4_wf | ].
  apply s4_ctx_sub_comma_drop_right; [s4_wf | ].
  s4_fv.
Qed.

(** ** let x = gen_nat () in x + 1 : [ν:nat | ν > 0]
    (§2, contexts C_en / C_dis, p. 6, "C[y]" judgments with y = x + 1)

    [envir_x_program_obl_sub] (ADMITTED, believed true): under
    [x ∷ [ν:nat|⊤]], the precise result of [x + 1] reaches every positive
    number.  Informal argument: in any world [m] of the context the
    projection on [x] is exactly ℕ (guard: values are naturals; angelic part:
    every natural occurs).  The precise binop type is fibred over [x]
    ([FFibVars {x}]) and in each [x]-fibre fixes [ν = x + 1]; therefore the
    [ν]-projection of the extended world is exactly [{n+1 | n ∈ ℕ}] = the
    positives, which is the exact atom of [q_nat_pos], so the (unfibred)
    [FUnder (FAtom q_nat_pos)] holds with the world itself as witness.
    The shared lemma [subtype_under_closed_by_qualifier] does not apply
    because the source qualifier mentions the context variable [x].
    (Round 2: stated for an arbitrary variable [w] and the single binding
    [w ∷ U[nat]], so that it also serves [captured_z_succ_fun] below;
    [U[nat]] is now the shared faithful [[: ℕ | q_base_all ℕ]].) *)
Lemma envir_x_program_obl_sub (w : atom) :
  sub_type_under ∅ (w ∷ UNat)
    (binop_precise_ty bop_plus (avar w) (vnat 1)) UNatPos.
Admitted.

Lemma envir_x_program_extended_type :
  ∅; Emp ⊢ₓ envir_x_program ⋮ UNatPos.
Proof.
  unfold envir_x_program.
  eapply EXT_LetNamed; [s4_wf | exact nat_gen_program_under_type | ].
  eapply EXT_CtxSub with (Γ2 := x ∷ UNat);
    [s4_wf | |
     apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
  eapply EXT_Sub; [s4_wf | eapply EXT_BinOp; s4_wf | ].
  exact (envir_x_program_obl_sub x).
Qed.

(** ** z:[ν:nat|⊤] ⊢ λx. z + 1 : {ν:unit|⊤} → [ν:nat | 0 < ν]
    (p. 19, l. 884, transcribed verbatim; the paper's unit argument is
    rendered as a [𝔹] argument with the demonic top type [OBool], as
    elsewhere in this file).  NEW in round 2.  Structural: T-Lam, drop the
    argument binding, T-BinOp, T-Sub with [envir_x_program_obl_sub z]. *)
Definition captured_z_succ_fun : tm :=
  ret (ƛ x : 𝔹 => z ⟨ + ⟩ vnat 1).

Lemma captured_z_succ_fun_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ captured_z_succ_fun ⋮ bool_to_nat_ty.
Proof. unfold captured_z_succ_fun, bool_to_nat_ty. basic_check. Qed.

Lemma captured_z_succ_fun_extended_type :
  ∅; z ∷ UNat ⊢ₓ captured_z_succ_fun ⋮ (OBool → UNatPos).
Proof.
  unfold captured_z_succ_fun.
  eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
  eapply EXT_CtxSub with (Γ2 := z ∷ UNat);
    [s4_wf | | apply s4_ctx_sub_comma_drop_right; [s4_wf | s4_fv]].
  eapply EXT_Sub; [s4_wf | eapply EXT_BinOp; s4_wf | ].
  exact (envir_x_program_obl_sub z).
Qed.




(** ** Splitting a generated boolean (used by every [⊕ₙ] and by the
    closure example): [b ∷ [ν:bool|⊤] ≤_X b ∷ {ν=true}⊓[ν=true] ⊕ b ∷ {ν=false}⊓[ν=false]].

    ADMITTED, believed true.  Informal argument: let [r ⊨ b ∷ UBool].  As
    above, [r]'s projection on [{b}] is exactly [{b↦true, b↦false}].  Take
    [r' := r ↾ {b}]; since [X ⊆ {b}], [r ↾ X ⊑ r'].  [r'] is the sum of the
    two non-empty singleton worlds [{b↦true}] and [{b↦false}], and each
    satisfies the corresponding precise boolean binding (over part: every
    store has the right value; under part: the exact atom [b = c] holds;
    guards: [ret b] is total and boolean).  This is the CtxSub step of the
    paper's T-Match derivations (cf. p. 12, Example 3.4).  It was FALSE for
    the round-1 vacuous [U[bool]] (finding F1); with the faithful shared
    [U[bool]] it is the intended statement. *)
Lemma bool_gen_program_obl_ctx_split (b : atom) (X : aset) :
  X ⊆ {[b]} ->
  ctx_sub_under ∅ X (b ∷ UBool) (bool_split_ctx b).
Admitted.



(** ** 0 ⊕ 1 : [ν=0]⊓{ν=0} ⊕ [ν=1]⊓{ν=1}   (sugar of footnote 7)
    T-Let on [gen_bool ()], CtxSub into the sum context, T-Match. *)
Lemma nondet_choice_program_extended_type :
  ∅; Emp ⊢ₓ nondet_choice_program ⋮ nat01_sum_ty.
Proof.
  unfold nondet_choice_program, nondet_tm.
  eapply (EXT_Let ∅ Emp UBool _ _ _ ∅); [unfold nat01_sum_ty; s4_wf; exact nondet_choice_program_basic_type
    | exact bool_gen_program_under_type | ].
  intros b _. cbn.
  change (∅; Emp ,, b ∷ UBool ⊢ₓ
    (if avar b then ret (vnat 0) else ret (vnat 1)) ⋮ nat01_sum_ty).
  eapply EXT_CtxSub with (Γ2 := b ∷ UBool);
    [unfold nat01_sum_ty; s4_wf | |
     apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
  eapply EXT_CtxSub with (Γ2 := bool_split_ctx b);
    [unfold nat01_sum_ty; s4_wf | | apply bool_gen_program_obl_ctx_split; s4_fv].
  unfold bool_split_ctx, nat01_sum_ty.
  eapply EXT_MatchBoth;
    [s4_wf | eapply EXT_Var; s4_wf | eapply EXT_Var; s4_wf | | ].
  - eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
  - eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
Qed.

Definition choice_fun_branch_ty : context_ty :=
  (OBool → const_precise_ty (cnat 0)) ⊕ (OBool → UNat).

(** ** λx.0 ⊕ λx.gen_nat () : {ν:unit|⊤} → [ν:nat|⊤]
    (Rocq transcription [choice_fun]; the paper's l. 938 has "+1", see
    [choice_fun_paper] below).

    The structural derivation gives the branch-wise sum type
    [(OBool → [ν=0]) ⊕ (OBool → [ν:nat|⊤])]; the remaining obligation
    [choice_fun_obl_sub_sum_arrow] (ADMITTED, believed true) collapses it to
    an arrow.  Informal argument (lifted arrow denotation of §5.2): let the
    world [m_v] of results [v] be split as [m1 + m2] with [m1 ⊨ (OBool → [ν=0]) v]
    and [m2 ⊨ (OBool → UNat) v] (both non-empty).  For an arbitrary
    extension with an argument [x] (every store keeps at least one [x]) the
    application results over [m2]'s part reach every natural (generator
    closure), and those over [m1] reach [0]; hence the [ν]-projection of the
    whole result world is exactly ℕ, which is [FUnder (FAtom q_nat_any)];
    the guards (totality / basic typing of [v x]) hold on both parts.
    Technical gap (pointed out by the audit): the [FPlus] parts [m1], [m2]
    only satisfy [res_sum m1 m2 ⊑ m_v], so the proof must transport [m2]'s
    arrow body (an [FForall]-extension followed by [FImpl]) to the filtered
    sub-world of the target's argument/result extension of [m_v]; this needs
    a restriction/filter monotonicity lemma for the arrow body that is not
    in the library.  Coverage of ℕ then comes from the [m2] part alone
    ([FFibVars ∅], i.e. a whole-world [ν]-projection), and guards/totality
    from both parts by fiberwise joinability.  No counterexample is known. *)
Lemma choice_fun_obl_sub_sum_arrow :
  sub_type_under ∅ Emp choice_fun_branch_ty (OBool → UNat).
Admitted.

Lemma choice_fun_branch_type :
  ∅; Emp ⊢ₓ choice_fun ⋮ choice_fun_branch_ty.
Proof.
  unfold choice_fun, nondet_tm.
  eapply (EXT_Let ∅ Emp UBool _ _ _ {[x]});
    [unfold choice_fun_branch_ty; s4_wf; try exact choice_fun_basic_type
    | exact bool_gen_program_under_type | ].
  intros b Hb. cbn.
  change (∅; Emp ,, b ∷ UBool ⊢ₓ
    (if avar b then ret (ƛ x : 𝔹 => ret (vnat 0)) else ret (ƛ x : 𝔹 => nat_gen_program))
    ⋮ choice_fun_branch_ty).
  eapply EXT_CtxSub with (Γ2 := b ∷ UBool);
    [unfold choice_fun_branch_ty; s4_wf | |
     apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
  eapply EXT_CtxSub with (Γ2 := bool_split_ctx b);
    [unfold choice_fun_branch_ty; s4_wf | | apply bool_gen_program_obl_ctx_split; s4_fv].
  unfold bool_split_ctx, choice_fun_branch_ty.
  eapply EXT_MatchBoth;
    [s4_wf | eapply EXT_Var; s4_wf | eapply EXT_Var; s4_wf | | ].
  - eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
    eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
  - eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
    eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | exact nat_gen_program_under_type | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
Qed.

Lemma choice_fun_extended_type :
  ∅; Emp ⊢ₓ choice_fun ⋮ (OBool → UNat).
Proof.
  eapply EXT_Sub; [s4_wf; try exact choice_fun_basic_type
    | exact choice_fun_branch_type | exact choice_fun_obl_sub_sum_arrow].
Qed.

Definition choice_fun_paper_branch_ty : context_ty :=
  (OBool → const_precise_ty (cnat 0)) ⊕ (OBool → UNatPos).

(** ** λx.0 ⊕ λx.gen_nat () + 1 : {ν:unit|⊤} → [ν:nat|⊤]   (p. 20, l. 938 ✓)

    [choice_fun_paper_obl_sub_sum_arrow] (ADMITTED, believed true): same
    argument as [choice_fun_obl_sub_sum_arrow]; the two parts of the result
    world reach [{0}] and all positives respectively, whose union is ℕ
    (both [FPlus] parts are non-empty).  Same technical gap (sub-world
    transport of the arrow body) as [choice_fun_obl_sub_sum_arrow]. *)
Lemma choice_fun_paper_obl_sub_sum_arrow :
  sub_type_under ∅ Emp choice_fun_paper_branch_ty (OBool → UNat).
Admitted.

Lemma choice_fun_paper_branch_type :
  ∅; Emp ⊢ₓ choice_fun_paper ⋮ choice_fun_paper_branch_ty.
Proof.
  unfold choice_fun_paper, nondet_tm.
  eapply (EXT_Let ∅ Emp UBool _ _ _ ({[x]} ∪ {[y]}));
    [unfold choice_fun_paper_branch_ty; s4_wf; try exact choice_fun_paper_basic_type
    | exact bool_gen_program_under_type | ].
  intros b Hb. cbn.
  change (∅; Emp ,, b ∷ UBool ⊢ₓ
    (if avar b then ret (ƛ x : 𝔹 => ret (vnat 0)) else ret (ƛ y : 𝔹 => envir_x_program))
    ⋮ choice_fun_paper_branch_ty).
  eapply EXT_CtxSub with (Γ2 := b ∷ UBool);
    [unfold choice_fun_paper_branch_ty; s4_wf | |
     apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
  eapply EXT_CtxSub with (Γ2 := bool_split_ctx b);
    [unfold choice_fun_paper_branch_ty; s4_wf | | apply bool_gen_program_obl_ctx_split; s4_fv].
  unfold bool_split_ctx, choice_fun_paper_branch_ty.
  eapply EXT_MatchBoth;
    [s4_wf | eapply EXT_Var; s4_wf | eapply EXT_Var; s4_wf | | ].
  - eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
    eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
  - eapply EXT_LamNamedErased; [reflexivity | s4_wf | ].
    eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | exact envir_x_program_extended_type | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
Qed.

Lemma choice_fun_paper_extended_type :
  ∅; Emp ⊢ₓ choice_fun_paper ⋮ (OBool → UNat).
Proof.
  eapply EXT_Sub; [s4_wf; try exact choice_fun_paper_basic_type
    | exact choice_fun_paper_branch_type | exact choice_fun_paper_obl_sub_sum_arrow].
Qed.

(** Precise boolean constant is a subtype of [{𝔹 | ⊤}] (via the proved
    over-lemmas of [ExtendedSubsumption]; closed). *)
Lemma s4_const_bool_sub_obool (Γ : ctx) (bv : bool) :
  wf_ctx_under ∅ Γ ->
  sub_type_under ∅ Γ (const_precise_ty (cbool bv)) OBool.
Proof.
  intros Hwf.
  change (extended_semantic_subtype ∅ Γ
    (({: TBool | mk_q_eq (vbvar 0) (vconst (cbool bv)) }) ⊓
     ([: TBool | mk_q_eq (vbvar 0) (vconst (cbool bv)) ]))
    ({: TBool | qual_top })).
  apply subtype_inter_over_under_to_over.
  - repeat split; try exact Hwf; try extended_wf_type.
  - apply subtype_over_closed_by_qualifier.
    + repeat split; try exact Hwf; try extended_wf_type.
    + unfold qual_dom, mk_q_eq. cbn [qual_vars qual_lvars lvar_value_keys].
      rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty. set_solver.
    + unfold qual_dom, qual_top. cbn [qual_vars qual_lvars]. rewrite lvars_fv_empty. set_solver.
    + unfold qualifier_entails, qual_top. intros. exact I.
Qed.

Ltac s4_open_closed :=
  apply (cty_open_above_lc_fresh 0);
  [ apply Nat.le_0_l
  | unfold UNat, ONat, under_ty, over_ty, qual_top, q_base_all, q_const_pred, vnu; cbn [cty_lc_at qual_vars qual_lvars lvar_value_keys];
    let k := fresh "k" in let Hk := fresh "Hk" in
    intros k Hk; apply lvars_bv_elem in Hk; set_solver
  | s4_fv ].

(** The common A-normalised prefix
      [let f := ef in let a := ret true in let y1 := f @ a in let y2 := f @ a in _]
    under an initial context [Γ0]; [f] is used entangled (T-Let) by both calls. *)
Ltac s4_drop_right_until Γt :=
  repeat lazymatch goal with
  | |- has_extended_context_type _ Γt _ _ => fail
  | |- has_extended_context_type _ (CtxComma ?G _) _ _ =>
      eapply EXT_CtxSub with (Γ2 := G);
      [s4_wf | | apply s4_ctx_sub_comma_drop_right; [s4_wf | s4_fv]]
  end.

Ltac s4_call_f_a Γ0 :=
  eapply s4_ext_appfun_closed with (τx := OBool);
  [ s4_open_closed | s4_wf | s4_fv
  | s4_drop_right_until (Γ0 ,, (f ∷ (OBool → UNat)));
    eapply EXT_CtxSub with (Γ2 := f ∷ (OBool → UNat));
    [s4_wf | eapply EXT_Var; s4_wf
    | apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]]
  | s4_drop_right_until (Γ0 ,, (f ∷ (OBool → UNat)) ,, (a ∷ OBool));
    eapply EXT_CtxSub with (Γ2 := a ∷ OBool);
    [s4_wf | eapply EXT_Var; s4_wf
    | apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]] ].

Ltac s4_double_call_prefix Γ0 Hf :=
  eapply EXT_LetNamed with (τ1 := OBool → UNat); [s4_wf | exact Hf | ];
  eapply EXT_LetNamed with (τ1 := OBool);
  [ s4_wf
  | eapply EXT_Sub with (τ1 := const_precise_ty (cbool true));
    [ s4_wf
    | eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]]
    | apply s4_const_bool_sub_obool; s4_wf ]
  | ];
  eapply EXT_LetNamed with (τ1 := UNat); [s4_wf | s4_call_f_a Γ0 | ];
  eapply EXT_LetNamed with (τ1 := UNat); [s4_wf | s4_call_f_a Γ0 | ].

(** ** z:[ν:nat|⊤] ⊢ let f = λx.z in let y1 = f a in let y2 = f a in y2
    : [ν:nat|⊤]   (A-normal form of [double_call_captured_z]; the original
    is not derivable, F2).  Fully proved (no admitted lemma; the
    subtyping [{ν=true} <: {𝔹|⊤}] is [s4_const_bool_sub_obool], proved via
    [ExtendedSubsumption]). *)
Lemma double_call_captured_z_anf_extended_type :
  ∅; z ∷ UNat ⊢ₓ double_call_captured_z_anf ⋮ UNat.
Proof.
  unfold double_call_captured_z_anf.
  s4_double_call_prefix (z ∷ UNat) captured_z_fun_extended_type.
  eapply EXT_CtxSub with (Γ2 := y2 ∷ UNat);
    [s4_wf | eapply EXT_Var; s4_wf
    | apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
Qed.

Lemma s4_bool_if_on_ubool (b : atom) (c1 c2 : bool) :
  ∅; b ∷ UBool ⊢ₓ (if avar b then ret (vbool c1) else ret (vbool c2)) ⋮
    (const_precise_ty (cbool c1) ⊕ const_precise_ty (cbool c2)).
Proof.
  eapply EXT_CtxSub with (Γ2 := bool_split_ctx b);
    [s4_wf | | apply bool_gen_program_obl_ctx_split; s4_fv].
  unfold bool_split_ctx.
  eapply EXT_MatchBoth;
    [s4_wf | eapply EXT_Var; s4_wf | eapply EXT_Var; s4_wf | | ].
  - eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
  - eapply EXT_CtxSub with (Γ2 := Emp);
      [s4_wf | eapply EXT_Const; s4_wf | apply s4_ctx_sub_to_emp; [s4_wf | s4_fv]].
Qed.

Definition bool_closure_result_ty : context_ty :=
  (const_precise_ty (cbool true) ⊕ const_precise_ty (cbool false)) ⊕
  (const_precise_ty (cbool false) ⊕ const_precise_ty (cbool true)).

Definition bool_closure_ctx : ctx := Emp ,, (x ∷ UBool).

(** ** let x = gen_bool () in λy. y == x   (closure capturing a generated
    value; not in the paper text, used here to exercise finding F5)

    Derivable type: [y:[ν:bool|⊤] -∗ ((true ⊕ false) ⊕ (false ⊕ true))]
    (independent arrow).  Round 2: the demonic-argument wand
    [y:{ν:bool|⊤} -∗ [ν:bool|⊤]] is now derived too, with T-CtxCase
    ([bool_gen_closure_program_obool_wand_type] below); the entangled
    [y:{ν:bool|⊤} → [ν:bool|⊤]] and [y:[ν:bool|⊤] → [ν:bool|⊤]] are
    semantically false (finding F5 (b)).

    [bool_gen_closure_program_obl_split_y] (ADMITTED, believed true):
    [(∅ ,, x ∷ UBool) ∗ y ∷ UBool ≤_X
       ((∅,,x∷UBool) ∗ y∷{ν=true}⊓[ν=true]) ⊕ ((∅,,x∷UBool) ∗ y∷{ν=false}⊓[ν=false])].
    Informal argument: a world of the star context is (above) a product
    [m1 × m2] with [m1|x = {t,f}] and [m2|y = {t,f}], so its projection on
    [{x,y}] contains all four combinations.  Take [r' := r ↾ {x,y}] (so
    [r ↾ X ⊑ r'] since [X ⊆ {x,y}]); it is the sum of
    [{x↦t,f} × {y↦t}] and [{x↦t,f} × {y↦f}], each a product of a world
    satisfying [∅ ,, x ∷ UBool] with one satisfying the precise [y]
    binding.  (With the entangled [,] instead of [∗] this fails, F5 (b).) *)
Lemma bool_gen_closure_program_obl_split_y (X : aset) :
  X ⊆ {[x]} ∪ {[y]} ->
  ctx_sub_under ∅ X
    (bool_closure_ctx ∗ (y ∷ UBool))
    ((bool_closure_ctx ∗ (y ∷ bool_precise_ty true)) ⊕
     (bool_closure_ctx ∗ (y ∷ bool_precise_ty false))).
Admitted.

Lemma bool_gen_closure_program_wand_type :
  ∅; Emp ⊢ₓ bool_gen_closure_program ⋮ (UBool -∗ bool_closure_result_ty).
Proof.
  unfold bool_gen_closure_program.
  eapply EXT_LetNamed with (τ1 := UBool);
    [unfold bool_closure_result_ty; s4_wf | exact bool_gen_program_under_type | ].
  eapply EXT_LamDNamedErased; [reflexivity | unfold bool_closure_result_ty; s4_wf | ].
  fold bool_closure_ctx.
  eapply EXT_CtxSub;
    [unfold bool_closure_result_ty, bool_closure_ctx; s4_wf | |
     apply bool_gen_closure_program_obl_split_y;
     unfold bool_closure_result_ty, bool_closure_ctx; s4_fv].
  unfold bool_equality_body, bool_closure_result_ty.
  eapply EXT_MatchBoth;
    [unfold bool_closure_ctx; s4_wf | | | | ].
  - eapply EXT_CtxSub with (Γ2 := y ∷ bool_precise_ty true);
      [unfold bool_closure_ctx; s4_wf | eapply EXT_Var; s4_wf
      | apply s4_ctx_sub_star_drop_left; [unfold bool_closure_ctx; s4_wf | s4_fv]].
  - eapply EXT_CtxSub with (Γ2 := y ∷ bool_precise_ty false);
      [unfold bool_closure_ctx; s4_wf | eapply EXT_Var; s4_wf
      | apply s4_ctx_sub_star_drop_left; [unfold bool_closure_ctx; s4_wf | s4_fv]].
  - eapply EXT_CtxSub with (Γ2 := bool_closure_ctx);
      [unfold bool_closure_ctx; s4_wf | |
       apply s4_ctx_sub_star_drop_right; [unfold bool_closure_ctx; s4_wf | unfold bool_closure_ctx; s4_fv]].
    unfold bool_closure_ctx.
    eapply EXT_CtxSub with (Γ2 := x ∷ UBool);
      [s4_wf | apply s4_bool_if_on_ubool
      | apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
  - eapply EXT_CtxSub with (Γ2 := bool_closure_ctx);
      [unfold bool_closure_ctx; s4_wf | |
       apply s4_ctx_sub_star_drop_right; [unfold bool_closure_ctx; s4_wf | unfold bool_closure_ctx; s4_fv]].
    unfold bool_closure_ctx.
    eapply EXT_CtxSub with (Γ2 := x ∷ UBool);
      [s4_wf | apply s4_bool_if_on_ubool
      | apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]].
Qed.

(** ** λy. y == x at the DEMONIC argument type (round 2, finding F5 (a)
    revisited with T-CtxCase).

    Target: [∅ ⊢ let x = gen_bool () in λy. y == x : y:{ν:bool|⊤} -∗ [ν:bool|⊤]].
    Semantically: the wand's argument world is INDEPENDENT of the closure
    (product), so whatever non-empty set of booleans [y] ranges over, [y == x]
    with [x ∈ {true,false}] reaches both booleans.

    Derivation: T-Let ([x : U[bool]]), T-LamD, then T-CtxCase on the
    demonic [y], nested twice:
      Γ = (∅,,x:U[bool]) ∗ y:{bool|⊤}
        ≤case  (… ∗ y:{ν=true}⊓[ν=true])          — y is always true
            |  (… ∗ y:[ν:bool | ν=false])          — false is reachable
      (… ∗ y:[ν:bool|ν=false])
        ≤case  (… ∗ y:{ν=false}⊓[ν=false])        — y is always false
            |  (… ∗ y:true-precise) ⊕ (… ∗ y:false-precise)  — both
    and T-MatchTrueOnly / T-MatchFalseOnly / T-MatchBoth in the three
    leaves.  Each inner [if x then b else ¬b] is typed by the proved split of
    [s4_bool_if_on_ubool] and T-Sub into [U[bool]].

    The ENTANGLED versions [y:{bool|⊤} → [bool|⊤]] and [y:[bool|⊤] → [bool|⊤]]
    are SEMANTICALLY FALSE (not merely underivable): the result of the
    program ranges over the two closures [f_t = λy.y==true] and
    [f_f = λy.y==false], and the arrow's argument extension may correlate
    [y] with [f]: the capability {[f↦f_t, y↦true], [f↦f_f, y↦false]}
    satisfies both [y:{bool|⊤}] and [y:[bool|⊤]], but every application
    [f y] returns [true], so [[ν:bool|⊤]] fails (F5 (b)). *)

Definition bool_closure_obool_ctx : ctx := bool_closure_ctx ∗ (y ∷ OBool).
Definition bool_closure_true_ctx : ctx := bool_closure_ctx ∗ (y ∷ bool_precise_ty true).
Definition bool_closure_false_ctx : ctx := bool_closure_ctx ∗ (y ∷ bool_precise_ty false).
Definition bool_reach_false_ty : context_ty := [: TBool | q_false].
Definition bool_closure_rest_ctx : ctx := bool_closure_ctx ∗ (y ∷ bool_reach_false_ty).
Definition bool_closure_both_ctx : ctx := bool_closure_true_ctx ⊕ bool_closure_false_ctx.

(** ADMITTED, believed true.  [{ν=b}⊓[ν=b] ⊕ {ν=¬b}⊓[ν=¬b] <: [ν:bool|⊤]]
    under any well-formed [Γ].  Let [m ⊨ ⟦τ1 ⊕ τ2⟧ e] and let [m_ν] be any
    result extension of [m].  The lifted sum denotation gives non-empty
    [m1], [m2] with [m1 + m2 ⊑ m_ν], [ν = b] on every store of [m1] and
    [ν = ¬b] on every store of [m2]; hence the [ν]-projection of [m_ν]
    contains both booleans, and (guard: [e] has basic type [𝔹]) it is
    exactly [{true,false}], the exact atom of [q_base_all 𝔹].  So [m_ν]
    itself witnesses [FUnder (FAtom (q_base_all 𝔹))] ([FFibVars ∅]).  The
    guard of [U[bool]] (basic typing, totality of [e]) is the guard of the
    sum type.  (FALSE if one summand could be empty — it cannot: the
    capability semiring has no zero.) *)
Lemma bool_gen_closure_program_obl_sum_sub_ubool (Γ : ctx) (bv : bool) :
  wf_ctx_under ∅ Γ ->
  sub_type_under ∅ Γ
    (const_precise_ty (cbool bv) ⊕ const_precise_ty (cbool (negb bv))) UBool.
Admitted.

(** ADMITTED, believed true.  [[ν:bool|⊤] ⊕ [ν:bool|⊤] <: [ν:bool|⊤]]:
    as above, the [ν]-projection of a result extension [m_ν] contains the
    [ν]-projection of the (non-empty) part [m1], which is already
    [{true,false}]; guards coincide. *)
Lemma bool_gen_closure_program_obl_plus_sub_ubool (Γ : ctx) :
  wf_ctx_under ∅ Γ ->
  sub_type_under ∅ Γ (UBool ⊕ UBool) UBool.
Admitted.

(** ADMITTED, believed true (T-CtxCase premise).  Let
    [r ⊨ (∅,,x:U[bool]) ∗ y:{bool|⊤}], i.e. [m1 × m2 ⊑ r] with
    [m1 ⊨ ∅,,x:U[bool]], [m2 ⊨ y:{bool|⊤}], so the [y]-projection of [r] is
    the (non-empty, boolean) [y]-projection [Y] of [m2].  Take [r' := r].
    If [Y = {true}] then [m2 ⊨ y:{ν=true}⊓[ν=true]] (every store has
    [y = true], and [true] is reached), so [r ⊨ … ∗ y:true-precise].
    Otherwise [false ∈ Y], so [m2 ⊨ y:[ν:bool|ν=false]] (the sub-world of
    [m2] filtered by [y = false] has [y]-projection exactly [{false}]), so
    [r ⊨ … ∗ y:[ν:bool|ν=false]]. *)
Lemma bool_gen_closure_program_obl_case_true_or_rest (X : aset) :
  X ⊆ {[x]} ∪ {[y]} ->
  ctx_case_under ∅ X bool_closure_obool_ctx bool_closure_true_ctx bool_closure_rest_ctx.
Admitted.

(** ADMITTED, believed true (T-CtxCase premise).  Let
    [r ⊨ (∅,,x:U[bool]) ∗ y:[ν:bool|ν=false]] with [m1 × m2 ⊑ r]; the
    [y]-projection [Y] of [r] (= that of [m2]) contains [false].  If
    [Y = {false}], [r ⊨ … ∗ y:false-precise] as in the previous
    obligation.  Otherwise [Y = {true,false}]; take [r' := r ↾ {x,y}] (so
    [r ↾ X ⊑ r'] since [X ⊆ {x,y}]); [r' = (m1↾x) × (m2↾y)] is the sum of
    [(m1↾x) × {y↦true}] and [(m1↾x) × {y↦false}], each a product of a
    world of [∅,,x:U[bool]] with a world of the corresponding precise
    [y]-binding; hence [r' ⊨ (… ∗ y:true-precise) ⊕ (… ∗ y:false-precise)].
    (Same argument as [bool_gen_closure_program_obl_split_y].) *)
Lemma bool_gen_closure_program_obl_case_false_or_both (X : aset) :
  X ⊆ {[x]} ∪ {[y]} ->
  ctx_case_under ∅ X bool_closure_rest_ctx bool_closure_false_ctx bool_closure_both_ctx.
Admitted.

Ltac s4_cl_unfold :=
  unfold bool_closure_obool_ctx, bool_closure_true_ctx, bool_closure_false_ctx,
    bool_closure_rest_ctx, bool_closure_both_ctx, bool_reach_false_ty,
    bool_closure_ctx in *.

(** Inner match on the captured [x] under [bool_closure_ctx ∗ Γy]:
    T-CtxSub down to [x ∷ U[bool]], T-Match (both, via the proved split
    of [s4_bool_if_on_ubool]), T-Sub into [U[bool]]. *)
Ltac s4_closure_inner :=
  eapply EXT_CtxSub with (Γ2 := bool_closure_ctx);
    [ s4_cl_unfold; s4_wf | |
      apply s4_ctx_sub_star_drop_right; [s4_cl_unfold; s4_wf | s4_cl_unfold; s4_fv]];
  unfold bool_closure_ctx;
  eapply EXT_CtxSub with (Γ2 := x ∷ UBool);
    [s4_wf | | apply s4_ctx_sub_comma_drop_left_closed; [s4_wf | s4_wf | s4_fv | s4_fv]];
  first
  [ eapply EXT_Sub with (τ1 := const_precise_ty (cbool true) ⊕ const_precise_ty (cbool (negb true)));
    [s4_wf | apply s4_bool_if_on_ubool | apply bool_gen_closure_program_obl_sum_sub_ubool; s4_wf]
  | eapply EXT_Sub with (τ1 := const_precise_ty (cbool false) ⊕ const_precise_ty (cbool (negb false)));
    [s4_wf | apply s4_bool_if_on_ubool | apply bool_gen_closure_program_obl_sum_sub_ubool; s4_wf] ].

Ltac s4_closure_y_precise :=
  first
  [ eapply EXT_CtxSub with (Γ2 := y ∷ bool_precise_ty true);
    [s4_cl_unfold; s4_wf | eapply EXT_Var; s4_wf
    | apply s4_ctx_sub_star_drop_left; [s4_cl_unfold; s4_wf | s4_fv]]
  | eapply EXT_CtxSub with (Γ2 := y ∷ bool_precise_ty false);
    [s4_cl_unfold; s4_wf | eapply EXT_Var; s4_wf
    | apply s4_ctx_sub_star_drop_left; [s4_cl_unfold; s4_wf | s4_fv]] ].

Lemma bool_gen_closure_program_body_true :
  ∅; bool_closure_true_ctx ⊢ₓ bool_equality_body ⋮ UBool.
Proof.
  unfold bool_equality_body.
  eapply EXT_MatchTrueOnly; [s4_cl_unfold; s4_wf | unfold bool_closure_true_ctx; s4_closure_y_precise | ].
  unfold bool_closure_true_ctx. s4_closure_inner.
Qed.

Lemma bool_gen_closure_program_body_false :
  ∅; bool_closure_false_ctx ⊢ₓ bool_equality_body ⋮ UBool.
Proof.
  unfold bool_equality_body.
  eapply EXT_MatchFalseOnly; [s4_cl_unfold; s4_wf | unfold bool_closure_false_ctx; s4_closure_y_precise | ].
  unfold bool_closure_false_ctx. s4_closure_inner.
Qed.

Lemma bool_gen_closure_program_body_both :
  ∅; bool_closure_both_ctx ⊢ₓ bool_equality_body ⋮ UBool.
Proof.
  eapply EXT_Sub with (τ1 := UBool ⊕ UBool);
    [s4_cl_unfold; s4_wf | |
     apply bool_gen_closure_program_obl_plus_sub_ubool; s4_cl_unfold; s4_wf].
  unfold bool_equality_body, bool_closure_both_ctx.
  eapply EXT_MatchBoth;
    [s4_cl_unfold; s4_wf | unfold bool_closure_true_ctx; s4_closure_y_precise
    | unfold bool_closure_false_ctx; s4_closure_y_precise | | ].
  - unfold bool_closure_true_ctx. s4_closure_inner.
  - unfold bool_closure_false_ctx. s4_closure_inner.
Qed.

Lemma bool_gen_closure_program_body_rest :
  ∅; bool_closure_rest_ctx ⊢ₓ bool_equality_body ⋮ UBool.
Proof.
  eapply EXT_CtxCase with (Γa := bool_closure_false_ctx) (Γb := bool_closure_both_ctx);
    [s4_cl_unfold; s4_wf | exact bool_gen_closure_program_body_false
    | exact bool_gen_closure_program_body_both
    | apply bool_gen_closure_program_obl_case_false_or_both; s4_fv].
Qed.

Lemma bool_gen_closure_program_obool_wand_type :
  ∅; Emp ⊢ₓ bool_gen_closure_program ⋮ (OBool -∗ UBool).
Proof.
  unfold bool_gen_closure_program.
  eapply EXT_LetNamed with (τ1 := UBool);
    [s4_wf | exact bool_gen_program_under_type | ].
  eapply EXT_LamDNamedErased; [reflexivity | s4_wf | ].
  fold bool_closure_ctx. fold bool_closure_obool_ctx.
  eapply EXT_CtxCase with (Γa := bool_closure_true_ctx) (Γb := bool_closure_rest_ctx);
    [s4_cl_unfold; s4_wf | exact bool_gen_closure_program_body_true
    | exact bool_gen_closure_program_body_rest
    | apply bool_gen_closure_program_obl_case_true_or_rest; s4_fv].
Qed.

Lemma s4_no_type_app_const Σ Γ v c τ :
  ~ (Σ; Γ ⊢ₓ tapp v (vconst c) ⋮ τ).
Proof.
  intros H. remember (tapp v (vconst c)) as e eqn:He.
  induction H; try discriminate; eauto.
  all: unfold case_app in He; inversion He.
Qed.

Lemma s4_no_type_let_app_const Σ Γ v c e2 τ :
  ~ (Σ; Γ ⊢ₓ tlete (tapp v (vconst c)) e2 ⋮ τ).
Proof.
  intros H. remember (tlete (tapp v (vconst c)) e2) as e eqn:He.
  induction H; try discriminate; eauto.
  all: try (unfold let_named in He; inversion He; subst;
            eapply s4_no_type_app_const; eassumption).
Qed.

Lemma s4_close_value_const_inv x k w c :
  close_value x k w = vconst c -> w = vconst c.
Proof. destruct w; cbn; try (destruct (decide _)); congruence. Qed.

Lemma s4_no_type_let_let_app_const Σ Γ e1 v c e2 τ :
  ~ (Σ; Γ ⊢ₓ tlete e1 (tlete (tapp v (vconst c)) e2) ⋮ τ).
Proof.
  intros H. remember (tlete e1 (tlete (tapp v (vconst c)) e2)) as e eqn:He.
  induction H; try discriminate; eauto.
  all: unfold let_named in He; inversion He; subst.
  1-2: (destruct e3; cbn in H4; try discriminate;
    injection H4 as Ha Hb; destruct e3_1; cbn in Ha; try discriminate;
    injection Ha as Hv Hc; apply s4_close_value_const_inv in Hc; subst;
    eapply s4_no_type_let_app_const; eassumption).
  all: destruct (exist_fresh L) as [y0 Hy0]; specialize (H1 y0 Hy0); simpl in H1;
    eapply s4_no_type_let_app_const; exact H1.
Qed.

Lemma double_call_captured_z_not_derivable Γ τ :
  ~ (∅; Γ ⊢ₓ double_call_captured_z ⋮ τ).
Proof. apply s4_no_type_let_let_app_const. Qed.

Lemma nonpersistent_choice_use_not_derivable Γ τ :
  ~ (∅; Γ ⊢ₓ nonpersistent_choice_use ⋮ τ).
Proof. apply s4_no_type_let_let_app_const. Qed.

Lemma e_ND_program_not_derivable Γ τ :
  ~ (∅; Γ ⊢ₓ e_ND_program ⋮ τ).
Proof. apply s4_no_type_let_let_app_const. Qed.

(** ** (e_ND), p. 19 (✗): where the derivation gets stuck.

    The whole A-normalised derivation goes through structurally with T-Let;
    the only remaining premise is the subtyping below, under the context in
    which [y1] and [y2] are bound with the entangled [,].  That premise is
    semantically FALSE: the world in which [f] is [λx.z], i.e.
    [y1 = y2 = z] with [z] ranging over all of ℕ, satisfies the context,
    but [y1 - y2] only reaches [0], so [[ν:nat|⊤]] fails.  This is the
    paper's ✗.  We therefore only state the reduction (fully proved). *)

Definition e_ND_final_ctx (Γ0 : ctx) : ctx :=
  Γ0 ,, (f ∷ (OBool → UNat)) ,, (a ∷ OBool) ,, (y1 ∷ UNat) ,, (y2 ∷ UNat).

Lemma e_ND_anf_program_reduces_to_obl :
  sub_type_under ∅ (e_ND_final_ctx (z ∷ UNat))
    (binop_precise_ty bop_minus (avar y1) (avar y2)) UNat ->
  ∅; z ∷ UNat ⊢ₓ e_ND_anf_program ⋮ UNat.
Proof.
  intros Hobl. unfold e_ND_anf_program.
  s4_double_call_prefix (z ∷ UNat) captured_z_fun_extended_type.
  eapply EXT_Sub; [s4_wf | eapply EXT_BinOp; s4_wf | exact Hobl].
Qed.

(** ** Generator version of (e_ND) via the ENTANGLED T-Let only.

    If the second call is also bound with T-Let, the derivation reduces to
    the subtyping below under the context
    [.. ,, y1 ∷ [ν:nat|⊤] ,, y2 ∷ [ν:nat|⊤]]; that premise is FALSE (the
    world with [y1 = y2] satisfies the context but [y1 - y2] reaches only
    [0]).  This is not a failure of the system: the derivation that uses
    T-LetI ([EXT_LetDNamed]) for the second call succeeds, see
    [e_ND_gen_program_extended_type] at the end of the file. *)

Lemma e_ND_gen_program_reduces_to_obl :
  sub_type_under ∅ (e_ND_final_ctx Emp)
    (binop_precise_ty bop_minus (avar y1) (avar y2)) UNat ->
  ∅; Emp ⊢ₓ e_ND_gen_program ⋮ UNat.
Proof.
  intros Hobl. unfold e_ND_gen_program.
  s4_double_call_prefix Emp nat_gen_fun_extended_type.
  eapply EXT_Sub; [s4_wf | eapply EXT_BinOp; s4_wf | exact Hobl].
Qed.


(** ** Generator (e_ND) IS derivable with T-LetI (corrects the earlier
    version of finding F4; see F4 in the findings block).

    Derivation (A-normal form [e_ND_gen_program]):
      let f  = λx.gen_nat ()   : □({𝔹|⊤} → [ν:nat|⊤])        (T-Let, T-PersI)
      let a  = true            : {ν=true}⊓[ν=true]            (T-Let, precise)
      let y1 = f a             : [ν:nat|⊤]                    (T-Let, T-AppFun)
      CtxSub  Γa ,, y1:[nat|⊤]  ≤  Γa ∗ y1:[nat|⊤]            (proved, Qed)
      let y2 = f a             : [ν:nat|⊤]                    (T-LetI = EXT_LetDNamed)
      y1 - y2 under y1:[nat|⊤] ∗ y2:[nat|⊤]  : [ν:nat|⊤]      (T-BinOp, T-Sub)
    where Γa = ∅ ,, f:□(..) ,, a:{ν=true}.  No duplicated binding
    [f:□τ ∗ f:□τ] is needed: [Γa] is the left factor [Γ1] of T-LetI, which
    types the second call [f a], and the right factor only contains [y1].
    The □ on [f] is what makes the CtxSub valid: a world of [f:□τ] has a
    singleton projection on [f] ([Context.ctx_bind_persist_singleton_projection]),
    and the precise type of [a] fixes [a = true], so every world of
    [Γa ,, y1:..] is the product of the singleton world on {f,a} with itself
    ([ResourceInterface.res_product_singleton_projection_eq]).  For the ✗
    examples ([λx.z], [choice_fun]) [f] has no □ type, its projection need
    not be a singleton, and the CtxSub fails — consistently with the paper. *)

Fixpoint s4_closed_binds (Γ : ctx) : Prop :=
  match Γ with
  | CtxEmpty => True
  | CtxBind _ τ => fv_cty τ = ∅
  | CtxComma Γ1 Γ2 | CtxStar Γ1 Γ2 => s4_closed_binds Γ1 /\ s4_closed_binds Γ2
  | CtxSum _ _ => False
  end.

Lemma s4_closed_binds_fv Γ : s4_closed_binds Γ -> ctx_fv Γ = ∅.
Proof.
  induction Γ; cbn [s4_closed_binds ctx_fv]; intros H; try contradiction.
  - reflexivity.
  - exact H.
  - destruct H as [H1 H2]. rewrite IHΓ1, IHΓ2 by assumption. set_solver.
  - destruct H as [H1 H2]. rewrite IHΓ1, IHΓ2 by assumption. set_solver.
Qed.

Ltac s4_dom_in_union_r :=
  match goal with
  | Hk : ?k ∈ dom ?m2 |- ?k ∈ dom (?m1 ∪ ?m2) =>
      apply elem_of_dom in Hk as [T HT]; apply elem_of_dom;
      destruct (m1 !! k) as [T' | ] eqn:E;
      [exists T'; apply lookup_union_Some_l; exact E
      | exists T; apply lookup_union_Some_raw; right; split; assumption]
  end.
Ltac s4_dom_in_union_l :=
  match goal with
  | Hk : ?k ∈ dom ?m1 |- ?k ∈ dom (?m1 ∪ ?m2) =>
      apply elem_of_dom in Hk as [T HT]; apply elem_of_dom;
      exists T; apply lookup_union_Some_l; exact HT
  end.
Ltac s4_dom_union_tac Hi1 Hi2 :=
  cbn [erase_ctx]; intros k Hk;
  apply elem_of_union in Hk as [Hk|Hk]; [exact Hk | ];
  apply elem_of_union in Hk as [Hk|Hk];
  [apply Hi1 in Hk; s4_dom_in_union_l | apply Hi2 in Hk; s4_dom_in_union_r].

Lemma s4_ctx_denote_fv_closed Γ :
  s4_closed_binds Γ ->
  forall Σ, formula_fv (ctx_denote_under Σ Γ) ⊆ dom (erase_ctx Γ).
Proof.
  induction Γ; intros Hcl Σ; pose proof (s4_closed_binds_fv _ Hcl) as Hfv;
    cbn [ctx_denote_under]; rewrite Hfv, s4_store_restrict_to_empty_ty;
    rewrite formula_fv_and, formula_fv_basic_world_formula, lvars_fv_atom_env_to_lty_env_dom;
    rewrite (left_id_L ∅ union); cbn [s4_closed_binds] in Hcl; try contradiction.
  - rewrite (formula_fv_true (V:=value)). set_solver.
  - unfold ty_denote.
    match goal with |- context [ty_denote_gas ?g ?S τ ?e] =>
      pose proof (ty_denote_gas_fv_subset g S τ e) as H end.
    cbn [fv_tm fv_value] in H. rewrite Hcl in H.
    cbn [erase_ctx]. intros k Hk. apply elem_of_union in Hk as [Hk|Hk]; [exact Hk| ].
    apply H in Hk. apply elem_of_dom. exists (erase_ty τ).
    apply lookup_singleton_Some. split; [set_solver|reflexivity].
  - destruct Hcl as [H1 H2].
    rewrite formula_fv_and.
    pose proof (IHΓ1 H1 ∅) as Hi1. pose proof (IHΓ2 H2 (∅ ∪ erase_ctx Γ1)) as Hi2.
    s4_dom_union_tac Hi1 Hi2.
  - destruct Hcl as [H1 H2].
    rewrite formula_fv_star.
    pose proof (IHΓ1 H1 ∅) as Hi1. pose proof (IHΓ2 H2 ∅) as Hi2.
    s4_dom_union_tac Hi1 Hi2.
Qed.

Lemma s4_restrict_const (r : WfWorld (V := value)) X σ0 :
  (r : World) σ0 -> X ⊆ world_dom (r : World) ->
  (forall σ1, (r : World) σ1 -> storeA_restrict σ1 X = storeA_restrict σ0 X) ->
  res_restrict r X =
    (exist _ (singleton_world (storeA_restrict σ0 X))
       (wf_singleton_world (storeA_restrict σ0 X)) : WfWorld).
Proof.
  intros Hσ0 HX Hagree.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom. cbn. rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom r σ0 Hσ0). reflexivity.
  - intros σ. split.
    + intros [σ1 [Hσ1 <-]]. cbn. apply Hagree. exact Hσ1.
    + cbn. intros ->. exists σ0. split; [exact Hσ0 | reflexivity].
Qed.

Lemma s4_restrict_singleton_store (r : WfWorld (V := value)) X σ σ0 :
  res_restrict r X = (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) ->
  (r : World) σ0 -> storeA_restrict σ0 X = σ.
Proof.
  intros Hr Hσ0.
  assert (H : (res_restrict r X : World) (storeA_restrict σ0 X)).
  { cbn [raw_world raw_worldA world_stores resA_restrict]. exists σ0. split; [exact Hσ0|reflexivity]. }
  rewrite Hr in H. exact H.
Qed.

Lemma s4_comma_right_closed Σ Γ1 Γ2 (m : WfWorld (V := value)) :
  ctx_fv Γ2 = ∅ -> m ⊨ ctx_denote_under Σ (Γ1 ,, Γ2) -> m ⊨ ctx_denote_under ∅ Γ2.
Proof.
  intros Hfv Hr. cbn [ctx_denote_under] in Hr.
  apply res_models_and_iff in Hr as [_ Hr].
  apply res_models_and_iff in Hr as [_ Hr].
  rewrite s4_ctx_denote_under_closed in Hr by exact Hfv. exact Hr.
Qed.

Lemma s4_restrict_dom_eq (r : WfWorld (V := value)) σ0 D :
  (r : World) σ0 -> D ⊆ world_dom (r : World) ->
  dom (storeA_restrict σ0 D : gmap atom value) = D.
Proof.
  intros Hσ0 HD. rewrite storeA_restrict_dom.
  rewrite (wfworld_store_dom r σ0 Hσ0). set_solver.
Qed.

Definition e_ND_PF : context_ty := □ (OBool → UNat).
Definition e_ND_Ga : ctx := Emp ,, (f ∷ e_ND_PF) ,, (a ∷ const_precise_ty (cbool true)).

(** T-PersE as a subtyping [□τ <: τ] (ADMITTED, believed true).
    Informal argument: let [m ⊨ ⟦□τ⟧ e] (τ = {𝔹|⊤} → [ν:nat|⊤]).  The
    guard of [□τ] coincides with the guard of [τ] ([relevant_env_persist_eq],
    [erase_ty (□τ) = erase_ty τ]).  For the body, take any result extension
    [m_y] of [m] by [y = e]; the □-body gives [m_y ⊨ FPersist ⟦τ⟧(ret y)],
    hence ([res_models_persist_elim]) [m_y ⊨ ⟦τ⟧(ret y)].  Instantiating its
    own result quantifier with the (functional) extension [ν' := y] and
    transporting the arrow body back along the alias [ν' = y] (the arrow
    analogue of [TypePersistBase.ty_denote_gas_over_ret_fvar_self_body])
    gives exactly the arrow body of [⟦τ⟧ e] at [y].  The missing piece is
    only that arrow-level alias transport lemma, which is not in the
    library. *)
Lemma e_ND_gen_program_obl_persist_elim :
  sub_type_under ∅ (f ∷ e_ND_PF) e_ND_PF (OBool → UNat).
Admitted.

Lemma e_ND_gen_program_obl_comma_to_star X :
  X ⊆ {[f]} ∪ {[a]} ∪ {[y1]} ->
  ctx_sub_under ∅ X (e_ND_Ga ,, (y1 ∷ UNat)) (e_ND_Ga ∗ (y1 ∷ UNat)).
Proof.
  intros HX.
  assert (Hwf1 : wf_ctx_under ∅ (e_ND_Ga ,, (y1 ∷ UNat))) by (unfold e_ND_Ga, e_ND_PF; s4_wf).
  assert (Hwf2 : wf_ctx_under ∅ (e_ND_Ga ∗ (y1 ∷ UNat))) by (unfold e_ND_Ga, e_ND_PF; s4_wf).
  assert (HwfG : wf_ctx_under ∅ e_ND_Ga) by (unfold e_ND_Ga, e_ND_PF; s4_wf).
  assert (Hwff : wf_ctx_under ∅ (f ∷ e_ND_PF)) by (unfold e_ND_PF; s4_wf).
  split; [exact Hwf1| ]. split; [exact Hwf2| ]. split.
  - intros k _. reflexivity.
  - intros r Hr. exists r. split; [apply res_restrict_le| ].
    pose proof (ctx_denote_under_comma_left _ _ _ _ Hr) as HG.
    pose proof (s4_comma_right_closed ∅ e_ND_Ga (y1 ∷ UNat) r ltac:(s4_fv) Hr) as Hy.
    unfold e_ND_Ga in HG.
    pose proof (s4_comma_right_closed ∅ Emp (f ∷ e_ND_PF) r ltac:(unfold e_ND_PF; s4_fv)
      (ctx_denote_under_comma_left _ _ _ _ HG)) as Hf.
    pose proof (s4_comma_right_closed ∅ (Emp ,, (f ∷ e_ND_PF)) (a ∷ const_precise_ty (cbool true)) r
      ltac:(s4_fv) HG) as Ha.
    fold e_ND_Ga in HG.
    destruct (ctx_bind_persist_singleton_projection ∅ f (OBool → UNat) r Hwff Hf)
      as [σf [Hdf Hrf]].
    assert (Hτfv : fv_cty (OBool → UNat) = ∅) by s4_fv.
    rewrite Hτfv, (left_id_L ∅ union) in Hdf, Hrf.
    apply ctx_denote_under_bind_inv in Ha.
    assert (Halook : forall σ0, (r : World) σ0 -> σ0 !! a = Some (vconst (cbool true))).
    { intros σ0 Hσ0.
      unfold ty_denote, const_precise_ty, precise_ty, over_ty, under_ty in Ha.
      cbn [cty_depth ty_denote_gas] in Ha.
      apply res_models_and_iff in Ha as [_ Ha].
      apply res_models_and_iff in Ha as [Hov _].
      eapply ty_denote_over_ret_fvar_const_lookup with (gas := 0%nat); eauto.
      apply atom_store_to_lvar_store_closed. }
    destruct (world_wf r) as [[σ0 Hσ0] _].
    set (D := {[f]} ∪ {[a]} : aset).
    assert (HDdom : D ⊆ world_dom (r : World)).
    { pose proof (f_equal (fun w : WfWorld => world_dom (w : World)) Hrf) as Hd.
      cbv beta in Hd. rewrite res_restrict_dom in Hd.
      change (world_dom (r : World) ∩ {[f]} = dom (σf : Store (V := value))) in Hd.
      rewrite Hdf in Hd.
      pose proof (Halook σ0 Hσ0) as Ha0. apply elem_of_dom_2 in Ha0.
      rewrite (wfworld_store_dom r σ0 Hσ0) in Ha0.
      unfold D. intros k Hk. apply elem_of_union in Hk as [Hk|Hk].
      - apply elem_of_singleton in Hk. subst k.
        assert (Hf' : f ∈ world_dom (r : World) ∩ {[f]}) by (rewrite Hd; set_solver).
        set_solver.
      - apply elem_of_singleton in Hk. subst k. exact Ha0. }
    set (σ := storeA_restrict σ0 D).
    assert (Hsing : res_restrict r D =
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld)).
    { apply s4_restrict_const; [exact Hσ0 | exact HDdom | ].
      intros σ1 Hσ1. apply map_eq. intros k.
      etransitivity; [exact (storeA_restrict_lookup σ1 D k) | ].
      etransitivity; [ | symmetry; exact (storeA_restrict_lookup σ0 D k)].
      destruct (decide (k ∈ D)) as [Hk|Hk]; [ |reflexivity].
      unfold D in Hk. apply elem_of_union in Hk as [Hk|Hk]; apply elem_of_singleton in Hk; subst k.
      - pose proof (s4_restrict_singleton_store r {[f]} σf σ1 Hrf Hσ1) as E1.
        pose proof (s4_restrict_singleton_store r {[f]} σf σ0 Hrf Hσ0) as E0.
        rewrite <- E0 in E1.
        pose proof (f_equal (fun s : gmap atom value => s !! f) E1) as E. cbv beta in E.
        rewrite (storeA_restrict_lookup σ1 {[f]} f), (storeA_restrict_lookup σ0 {[f]} f) in E.
        rewrite decide_True in E by set_solver. exact E.
      - transitivity (Some (vconst (cbool true)));
          [exact (Halook σ1 Hσ1) | symmetry; exact (Halook σ0 Hσ0)]. }
    assert (Hdomσ : dom (σ : gmap atom value) = D).
    { unfold σ. apply (s4_restrict_dom_eq r); assumption. }
    pose proof (singleton_projection_compat r D σ Hdomσ Hsing) as Hc.
    pose proof (res_product_singleton_projection_eq r D σ Hc Hdomσ Hsing) as Hprod.
    assert (Hcl : s4_closed_binds e_ND_Ga).
    { unfold e_ND_Ga, e_ND_PF. cbn [s4_closed_binds]. repeat split; s4_fv. }
    assert (Hdome_ND_Ga : dom (erase_ctx e_ND_Ga) ⊆ D).
    { unfold e_ND_Ga, D. cbn [erase_ctx]. intros k Hk. apply elem_of_dom in Hk as [T HT].
      apply lookup_union_Some_raw in HT as [HT|[_ HT]].
      - apply lookup_union_Some_raw in HT as [HT|[_ HT]].
        + change ((∅ : gmap atom ty) !! k = Some T) in HT.
          rewrite lookup_empty in HT. discriminate.
        + change (({[f := erase_ty e_ND_PF]} : gmap atom ty) !! k = Some T) in HT.
          apply (proj1 (lookup_singleton_Some f k _ T)) in HT as [<- _]. set_solver.
      - change (({[a := erase_ty (const_precise_ty (cbool true))]} : gmap atom ty) !! k = Some T) in HT.
        apply (proj1 (lookup_singleton_Some a k _ T)) in HT as [<- _]. set_solver. }
    assert (Hfve_ND_Ga : formula_fv (ctx_denote_under ∅ e_ND_Ga) ⊆ D).
    { etransitivity; [apply s4_ctx_denote_fv_closed; exact Hcl | exact Hdome_ND_Ga]. }
    assert (HG1 : (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld)
                     ⊨ ctx_denote_under ∅ e_ND_Ga).
    { rewrite <- Hsing. apply (proj1 (res_models_minimal_on D r _ Hfve_ND_Ga)). exact HG. }
    pose proof (ctx_denote_under_star_intro_product ∅ e_ND_Ga (y1 ∷ UNat)
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) r Hc
      HwfG HG1 Hy) as Hstar.
    rewrite Hprod in Hstar. exact Hstar.
Qed.


(** Final subtyping under the SEPARATED context (ADMITTED, believed true).
    Informal argument: let [r ⊨ y1:[nat|⊤] ∗ y2:[nat|⊤]], so
    [m1 × m2 ⊑ r] with [m1 ⊨ y1:[nat|⊤]], [m2 ⊨ y2:[nat|⊤]].  World
    compatibility of [m1], [m2] forces disjoint (non-constant) domains, so
    [r↾{y1,y2} = (m1↾y1) × (m2↾y2) = ℕ × ℕ] (each factor is exactly ℕ: the
    guard gives naturals, the angelic exact atom [q_nat_any] gives every
    natural).  For any extension [m ⊒ r] satisfying the precise type of
    [y1 ∸ y2] and its result extension [m_ν], the [FFibVars {y1,y2}] over/under
    parts fix the fibre over [(n1,n2)] to be non-empty with [ν = n1 ∸ n2];
    taking [n2 = 0] every [n1] is reached, so the [ν]-projection of [m_ν] is
    exactly ℕ, i.e. [m_ν] itself witnesses [FUnder (FAtom q_nat_any)].  The
    guards (basic typing, totality of [e]) carry over from the source type.
    It is FALSE under the entangled [y1:[nat|⊤] ,, y2:[nat|⊤]] (world with
    [y1 = y2]), which is why T-LetI is needed. *)
Lemma e_ND_gen_program_obl_minus_sub :
  sub_type_under ∅ ((y1 ∷ UNat) ∗ (y2 ∷ UNat))
    (binop_precise_ty bop_minus (avar y1) (avar y2)) UNat.
Admitted.

Ltac s4_e_ND_call_f_a :=
  eapply s4_ext_appfun_closed with (τx := OBool);
  [ s4_open_closed | unfold e_ND_Ga, e_ND_PF; s4_wf | s4_fv
  | unfold e_ND_Ga;
    eapply EXT_CtxSub with (Γ2 := Emp ,, (f ∷ e_ND_PF));
    [unfold e_ND_PF; s4_wf | | apply s4_ctx_sub_comma_drop_right; [unfold e_ND_PF; s4_wf | s4_fv]];
    eapply EXT_CtxSub with (Γ2 := f ∷ e_ND_PF);
    [unfold e_ND_PF; s4_wf | |
     apply s4_ctx_sub_comma_drop_left_closed;
       [unfold e_ND_PF; s4_wf | unfold e_ND_PF; s4_wf | unfold e_ND_PF; s4_fv | unfold e_ND_PF; s4_fv]];
    eapply EXT_Sub with (τ1 := e_ND_PF);
    [unfold e_ND_PF; s4_wf | eapply EXT_Var; unfold e_ND_PF; s4_wf
    | exact e_ND_gen_program_obl_persist_elim]
  | unfold e_ND_Ga;
    eapply EXT_CtxSub with (Γ2 := a ∷ const_precise_ty (cbool true));
    [unfold e_ND_PF; s4_wf | |
     apply s4_ctx_sub_comma_drop_left_closed; [unfold e_ND_PF; s4_wf | s4_wf | s4_fv | s4_fv]];
    eapply EXT_Sub with (τ1 := const_precise_ty (cbool true));
    [s4_wf | eapply EXT_Var; s4_wf | apply s4_const_bool_sub_obool; s4_wf] ].

(** ** let f = λx.gen_nat() in let a = true in let y1 = f a in
       let y2 = f a in y1 - y2 : [ν:nat|⊤]    (p. 19-20, intended ✓) *)
Lemma e_ND_gen_program_extended_type :
  ∅; Emp ⊢ₓ e_ND_gen_program ⋮ UNat.
Proof.
  unfold e_ND_gen_program.
  eapply EXT_LetNamed with (τ1 := e_ND_PF);
    [unfold e_ND_PF; s4_wf | exact nat_gen_fun_persistent_type | ].
  eapply EXT_LetNamed with (τ1 := const_precise_ty (cbool true));
  [ unfold e_ND_PF; s4_wf
  | eapply EXT_CtxSub with (Γ2 := Emp);
      [unfold e_ND_PF; s4_wf | eapply EXT_Const; s4_wf
      | apply s4_ctx_sub_to_emp; [unfold e_ND_PF; s4_wf | s4_fv]]
  | ].
  fold e_ND_Ga.
  eapply EXT_LetNamed with (τ1 := UNat);
    [unfold e_ND_Ga, e_ND_PF; s4_wf | s4_e_ND_call_f_a | ].
  eapply EXT_CtxSub with (Γ2 := e_ND_Ga ∗ (y1 ∷ UNat));
    [unfold e_ND_Ga, e_ND_PF; s4_wf | |
     apply e_ND_gen_program_obl_comma_to_star; unfold e_ND_Ga, e_ND_PF; s4_fv].
  eapply EXT_LetDNamed with (τ1 := UNat);
    [unfold e_ND_Ga, e_ND_PF; s4_wf | s4_e_ND_call_f_a | ].
  eapply EXT_Sub; [s4_wf | eapply EXT_BinOp; s4_wf | exact e_ND_gen_program_obl_minus_sub].
Qed.
