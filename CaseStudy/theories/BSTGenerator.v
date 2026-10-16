(** * BST generator case-study program *)

From ContextLogic Require Import FormulaConnectivesHigher.
From Denotation Require Import Context TypeEquivCore TypeEquiv.
From ContextTyping Require Import Typing PrimOpConcreteContext.
From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section BSTGeneratorExample.

Definition r : atom := 20%positive.
Definition lo : atom := 21%positive.
Definition range_arg : atom := 22%positive.
Definition rec : atom := 23%positive.
Definition isz : atom := 24%positive.
Definition rp : atom := 25%positive.
Definition left_size : atom := 26%positive.
Definition right_size : atom := 27%positive.
Definition new_lo : atom := 28%positive.
Definition left_tree : atom := 29%positive.
Definition right_tree : atom := 30%positive.

Fixpoint tree_mem (n : nat) (t : tree) : Prop :=
  match t with
  | tr_leaf => False
  | tr_node r l rr => n = r \/ tree_mem n l \/ tree_mem n rr
  end.

Fixpoint bst_between (lo hi : nat) (t : tree) : Prop :=
  match t with
  | tr_leaf => True
  | tr_node r l rr =>
      lo <= r < hi /\
      bst_between lo r l /\
      bst_between r hi rr
  end.

Definition bst_spec (lo hi : nat) (t : tree) : Prop :=
  bst_between lo hi t.

Definition q_tree_bst_range (lo hi t : value) : type_qualifier :=
  tqual (lvar_value_keys lo ∪ lvar_value_keys hi ∪ lvar_value_keys t)
    (fun σ =>
       exists nlo nhi tr,
         denote_lvar_value (lso_store σ) lo = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) hi = Some (vconst (cnat nhi)) /\
         denote_lvar_value (lso_store σ) t = Some (vconst (ctree tr)) /\
         bst_spec nlo nhi tr).

Definition q_mem_tree_iff_range (lo hi t : value) : type_qualifier :=
  tqual (lvar_value_keys lo ∪ lvar_value_keys hi ∪ lvar_value_keys t)
    (fun σ =>
       exists nlo nhi tr,
         denote_lvar_value (lso_store σ) lo = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) hi = Some (vconst (cnat nhi)) /\
         denote_lvar_value (lso_store σ) t = Some (vconst (ctree tr)) /\
         forall n, tree_mem n tr <-> nlo <= n < nhi).

Definition OBstBetween : context_ty :=
  over_ty TTree (q_tree_bst_range arg1 arg0 ν).

Definition UBstBetween : context_ty :=
  under_ty TTree (q_tree_bst_range arg1 arg0 ν).

Definition bst_range_pred := bst_between.
Definition bst_generator_spec := bst_spec.

Definition range_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → O[ ℕ ].

(** Outline of the paper type:
    [r -> lo -> range -> □(tree satisfying the generated BST spec)]. *)
Definition bst_gen_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → range_ty → □ OBstBetween.

(** A readable recursive program.  Arithmetic and comparisons are core binary
    operations, and the paper's angelic choice [Leaf ⊕ body] is encoded by
    a nondeterministic boolean hidden behind [⊕ₙ]. *)
Definition bst_gen_program : tm :=
  ret (μ rec, r : ℕ ~> ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree =>
    ret (ƛ lo : ℕ =>
      ret (ƛ range_arg : ℕ →ᵦ ℕ →ᵦ ℕ =>
        let isz := r ⟨ ≤ ⟩ vnat 0 in
        if isz then
          ret leaf_value
        else
          ret leaf_value ⊕ₙ
            (
            let rp := range_arg @@ (vnat 1, r) in
            let left_size := rp ⟨ - ⟩ vnat 1 in
            let right_size := r ⟨ - ⟩ rp in
            let new_lo := lo ⟨ + ⟩ rp in
            let left_tree := rec @@@ (left_size, lo, range_arg) in
            let right_tree := rec @@@ (right_size, new_lo, range_arg) in
            [| new_lo, left_tree, right_tree |]
	            )))).

Definition bst_gen_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree.

Lemma bst_gen_program_basic_type :
  ∅ ⊢ₑ bst_gen_program ⋮ bst_gen_basic_ty.
Proof.
  unfold bst_gen_program, bst_gen_basic_ty.
  repeat progress basic_type_surface_norm.
  eapply TT_Ret.
  eapply basic_typing_fixfun_named; [basic_type_fresh|basic_type_fresh|idtac].
  eapply TT_Ret.
  eapply basic_typing_lam_named; [basic_type_fresh|idtac].
  eapply TT_Ret.
  eapply basic_typing_lam_named; [basic_type_fresh|idtac].
  eapply basic_typing_let_named; [basic_type_fresh|basic_type|idtac].
  eapply TT_Match; [basic_type|basic_type|idtac].
  eapply basic_typing_nondet_tm; basic_type.
Qed.

Lemma bst_between_leaf lo hi :
  bst_between lo hi tr_leaf.
Proof. cbn. exact I. Qed.

Lemma tree_mem_node_root n l r :
  tree_mem n (tr_node n l r).
Proof. cbn. left. reflexivity. Qed.

Lemma range_ty_wf :
  basic_context_ty ∅ range_ty.
Proof.
  unfold range_ty, ONat, over_ty, qual_top, basic_context_ty.
  cbn [wf_context_ty_at qual_vars qual_lvars].
  repeat split; intros [k|x] Hx; cbn [lvar_wf_at] in *; set_solver.
Qed.

Lemma basic_type_leaf_ret Γ :
  Γ ⊢ₑ Ret leaf_value ⋮ Tree.
Proof.
  unfold Ret, leaf_value.
  constructor. constructor.
Qed.

Lemma basic_type_node_const Γ n l r :
  Γ ⊢ₑ node_tm (vnat n) (vconst (ctree l)) (vconst (ctree r)) ⋮
    Tree.
Proof.
  unfold node_tm, vnat.
  econstructor; constructor.
Qed.


(* ================================================================== *)
(** * Typing the BST generator (paper §6, Fig. 7)                      *)
(* ================================================================== *)

(** Paper claim (Fig. 7):

      bst_gen : □(r:{nat|⊤} → lo:{nat|⊤} →
                  range:□(x:{nat|⊤} → y:{nat| x < ν} → [nat | x < ν < y]) →
                  [nat tree | bst(ν) ∧ ∀x. mem(ν,x) ⟺ lo < x ≤ lo + r])

    Translation.  [nat] is [ℕ]; [bst]/[mem] (uninterpreted method predicates
    in the paper) are interpreted by [is_bst]/[tree_mem]; a refinement
    [φ(r, lo, ν)] of the result is the qualifier
    [q_tree_spec (vbvar 3) (vbvar 2) ν P] (below [r → lo → range →] the
    result qualifier sees [r = vbvar 3], [lo = vbvar 2]).  The program is
    [bst_gen_program] (unchanged) and its A-normal form
    [bst_gen_program_anf], which only let-binds the constant [1] passed to
    [range] (T-AppFun/[EXT_AppFun] only accept variables as arguments).  The
    Rocq program matches Fig. 7 line by line: [range (1, r)], left size
    [r' - 1] with lower bound [lo], right size [r - r'] with lower bound
    [lo + r'], root [lo + r'], [Leaf ⊕ ...] as [⊕ₙ] (a [boolGen] match).

    Types:
    - [bst_gen_paper_ty]: Fig. 7 verbatim (strict range, [⟺]).  VACUOUSLY
      TRUE: its range parameter type is uninhabited (F1); derived
      vacuously for the original program ([bst_gen_paper_typing_vacuous])
      and the A-normal one ([bst_gen_anf_paper_typing_vacuous]).
    - [bst_gen_must_ty]: round-1 repair of the off-by-one ([x ≤ ν],
      [[x ≤ ν ≤ y]]), "keys within (lo, lo+r]" ([⟹]).  Still FALSE (F7).
    - [bst_gen_must_fixed_ty] (round 2): as [bst_gen_must_ty] but the range
      result is also demonically bounded ([{x≤ν≤y} ⊓ [x≤ν≤y]]).
    - [bst_gen_may_ty]: the safety counterpart (demonic result
      [{tree | bst ∧ keys ⊆ (lo, lo+r]}], same range parameter).

    FINDINGS (round 2; details next to the corresponding lemmas):

    (F1) [CORRECTED in the round-2 fix] The paper's strict range type
         [□(x:{ℕ|⊤} → y:{ℕ | x < ν} → [ℕ | x < ν < y])] is UNINHABITED:
         the argument extension [x = 1, y = 2] is valid, and then
         [[ℕ | 1 < ν < 2]] is an angelic type over an EMPTY set, which no
         non-empty capability satisfies (atoms are exact; paper Ex. 4.5).
         Hence [bst_gen_paper_ty] is VACUOUSLY TRUE (not false, as round 1
         and the first round-2 report claimed), and it is even derivable,
         because the T-Fix body context is genuinely unsatisfiable:
         [bst_gen_paper_typing_vacuous] (original program) and
         [bst_gen_anf_paper_typing_vacuous], modulo the single obligation
         [bst_paper_obl_range_strict_uninhabited].  Such a type says nothing
         about [bst_gen].  The off-by-one remains a defect of the
         SPECIFICATION: under the informal reading "[range x y] returns
         exactly the [v] with [x < v < y]" the roots [lo + 1], [lo + r] are
         never produced ([bst_counterexample_unreachable], a statement about
         a set-of-results model whose generator does NOT inhabit the strict
         type).  The intended [≤] repair is [bst_gen_must_ty], which is
         false by F7.

    (F2) [round 1: blocked; NOW RESOLVED] Variables at dependent types
         (recursive calls with argument [ν ≺ r], curried partial
         applications) are typed with [EXT_VarComma] after T-CtxSub to a
         comma prefix ([bst_var_at], [bst_ctx_sub_prefix], both Qed).  The
         round-1 hypothesis [ext_var_ctx_rule] is gone.

    (F3) [round 1: blocked; NOW handled by T-CtxCase] The match [if r <= 0]
         is typed by a three-way capability case split ([bst_inner_skeleton]):
         all [isz] true / all false / mixed.

    (F4) [round 1: "coverage composition unsound"; NOW RESOLVED for the
         recursive case] The coverage of [Node (lo+r') left right] needs
         every combination of the two recursive results.  The comma context
         loses it (round-1 counterexample stands for the coarse types), and
         the Section-4 comma→star pattern does not apply here (the left
         factor would have to have a singleton projection; [r], [lo], [r']
         vary; and [left]'s type depends on [ls], [lo], ill-formed under [∗]).
         Instead the derivation types each call at a FINER angelic type
         whose qualifier additionally depends (as a dummy) on the variables
         the later steps need: [rp] per [(r, lo)]-fibre, [left] per
         [(ls, lo, r, rp)]-fibre, [right] per [(rs, nlo, r, lo, rp, left)]-
         fibre.  These finer types come from T-Sub on the FUNCTION variables
         ([bst_must_obl_g_fine], [bst_must_obl_rec_fine_left/right]); they
         are valid because an arrow denotation quantifies over ALL argument
         extensions, which can isolate any group of closure values
         ("isolation" argument).  The [Leaf ⊕ ...] choice is typed with
         T-LetI ([EXT_LetD], [boolGen] in its own [∗] factor), which makes
         [b] independent of [(r, lo)] and validates the merge
         [bst_must_obl_leaf_node_merge].  Result:
         [bst_must_else_branch_typing] — the whole recursive case of the
         must type, for all worlds with [r ≥ 1], derived (Qed structure,
         named obligations).

    (F6) [NEW, blocks both readings] The T-Fix premise is semantically FALSE
         for [bst_gen], in the may and in the must reading.  The recursive
         binder [rec : {ν ≺ r} → ...] is checked on whole worlds: in a world
         with some row [r = 0] no argument extension satisfies the demonic
         [{ν < r}] on the [r = 0]-fibre ([FFibVars], exact atoms need a
         non-empty world, fibre extensions are total —
         [extA_rel_nonempty]), so [rec ∷ RECTY] holds VACUOUSLY for any
         closure.  Counterexample world for the body judgment
         [Γ3 ⊢ bst_inner lo : τ]: rows [{r↦0, rec↦g, lo↦0, range↦ρ}] and
         [{r↦2, rec↦g, lo↦0, range↦ρ}] with [g = λa lo rg. Node 100 Leaf Leaf]
         and [ρ] a precise [x..y] generator.  It satisfies [Γ3]; in the
         [r = 2] row the else branch returns [Node k (Node 100 ..) ..], which
         is not a BST within [(0, 2]] (may fails) and the BSTs within
         [(0, 2]] are not all reachable (must fails).  By soundness of the
         extended rules, the T-Fix premise of [bst_gen] is NOT DERIVABLE for
         any useful result type, and no other rule helps: [EXT_FixNamed] /
         [EXT_Fix] have exactly this premise, T-CtxCase cannot separate the
         mixed worlds ([r] is in the projection set), and
         [EXT_FixUnrollNamed] only unfolds finitely often (every unfolding
         again needs the recursive closure at a type with a non-singleton
         argument domain, whose minimal element recreates the mixed
         worlds).  The same holds for every recursive function whose body
         relies on the recursive result.  In our derivation this is isolated
         as the single hypothesis [bst_isz_mixed_case_hyp] (the mixed half of
         the [r <= 0] case split), which is FALSE; every other step is
         derived.  A sound repair would be a T-Fix whose argument binder has
         a singleton projection (e.g. [r ∷ □{b|φ}]): then CtxCase only has
         the all-true/all-false cases, both of which are derived here.

    (F7) [NEW] With the paper's under-approximate range parameter
         ([[x ≤ ν ≤ y]] only) the must type is FALSE: totality.  See the
         comment before [bst_gen_must_fixed_ty] and the machine-checked call
         graph [bst_bad_range_self_call].

    What IS derived (Qed structure; semantic side conditions are named
    [bst_gen_obl_*] / [bst_must_obl_*] / [bst_paper_obl_*] lemmas, Admitted
    with an informal argument unless marked proved):
    - the verbatim Fig. 7 type, vacuously: [bst_gen_paper_typing_vacuous]
      (original program), [bst_gen_anf_paper_typing_vacuous] (only
      [bst_paper_obl_range_strict_uninhabited]);
    - outer layers for every variant: [bst_outer], [bst_gen_anf_must_outer],
      [bst_gen_anf_paper_outer] (no Admitted dependency);
    - may: [bst_range_call_typing], [bst_left_call_typing],
      [bst_right_call_typing], [bst_else_body_typing],
      [bst_else_branch_typing] (unconditional now);
      [bst_gen_anf_may_typing_modulo] (only the false F6 hypothesis);
    - must: [bst_must_range_call_typing], [bst_must_left_call_typing],
      [bst_must_right_call_typing], [bst_must_else_body_typing],
      [bst_must_else_branch_typing];
      [bst_gen_anf_must_fixed_typing_modulo] (only the false F6
      hypothesis). *)

(** ** Paper-faithful specifications (Fig. 7) *)

Fixpoint is_bst (t : tree) : Prop :=
  match t with
  | tr_leaf => True
  | tr_node k l rr =>
      (forall n, tree_mem n l -> n < k) /\
      (forall n, tree_mem n rr -> k < n) /\
      is_bst l /\ is_bst rr
  end.

Definition bst_keys_within (r lo : nat) (t : tree) : Prop :=
  is_bst t /\ forall n, tree_mem n t -> lo < n <= lo + r.

Definition bst_keys_exact (r lo : nat) (t : tree) : Prop :=
  is_bst t /\ forall n, tree_mem n t <-> lo < n <= lo + r.

Definition q_nat2 (a b : value) (P : nat -> nat -> Prop) : type_qualifier :=
  tqual (lvar_value_keys a ∪ lvar_value_keys b)
    (fun σ =>
       exists na nb,
         denote_lvar_value (lso_store σ) a = Some (vconst (cnat na)) /\
         denote_lvar_value (lso_store σ) b = Some (vconst (cnat nb)) /\
         P na nb).

Definition q_nat3 (a b c : value) (P : nat -> nat -> nat -> Prop) : type_qualifier :=
  tqual (lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c)
    (fun σ =>
       exists na nb nc,
         denote_lvar_value (lso_store σ) a = Some (vconst (cnat na)) /\
         denote_lvar_value (lso_store σ) b = Some (vconst (cnat nb)) /\
         denote_lvar_value (lso_store σ) c = Some (vconst (cnat nc)) /\
         P na nb nc).

Definition q_tree_spec (rv lov tv : value) (P : nat -> nat -> tree -> Prop)
    : type_qualifier :=
  tqual (lvar_value_keys rv ∪ lvar_value_keys lov ∪ lvar_value_keys tv)
    (fun σ =>
       exists nr nlo t,
         denote_lvar_value (lso_store σ) rv = Some (vconst (cnat nr)) /\
         denote_lvar_value (lso_store σ) lov = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) tv = Some (vconst (ctree t)) /\
         P nr nlo t).

(** range types.  Inside [x:_ → y:_ → τ]: in [y]'s qualifier [x = vbvar 1];
    in the result qualifier [y = vbvar 1], [x = vbvar 2]. *)
Definition range_strict_paper_ty : context_ty :=
  □ (O[ ℕ ] →
     {: TNat | q_nat2 (vbvar 1) ν (fun x v => x < v) } →
     [: TNat | q_nat3 (vbvar 2) ν (vbvar 1) (fun x v y => x < v < y) ]).

Definition range_le_under_ty : context_ty :=
  □ (O[ ℕ ] →
     {: TNat | q_nat2 (vbvar 1) ν (fun x v => x <= v) } →
     [: TNat | q_nat3 (vbvar 2) ν (vbvar 1) (fun x v y => x <= v <= y) ]).

Definition range_le_inner_ty : context_ty :=
  O[ ℕ ] →
  {: TNat | q_nat2 (vbvar 1) ν (fun x v => x <= v) } →
  precise_ty TNat (q_nat3 (vbvar 2) ν (vbvar 1) (fun x v y => x <= v <= y)).

Definition range_le_precise_ty : context_ty := □ range_le_inner_ty.

(** Result types.  Below [r → lo → range →] the result qualifier sees
    [r = vbvar 3] and [lo = vbvar 2].  [ang = true] is the angelic/must
    reading [[...]], [ang = false] the demonic/may reading [{...}]. *)
Definition bst_res_ty (ang : bool) (q : type_qualifier) : context_ty :=
  match ang with true => CTUnder TTree q | false => CTOver TTree q end.

Definition bst_body_ty (R : context_ty) (ang : bool)
    (P : nat -> nat -> tree -> Prop) : context_ty :=
  O[ ℕ ] → R → bst_res_ty ang (q_tree_spec (vbvar 3) (vbvar 2) ν P).

Definition bst_full_ty (R : context_ty) (ang : bool)
    (P : nat -> nat -> tree -> Prop) : context_ty :=
  □ (O[ ℕ ] → bst_body_ty R ang P).

(** Fig. 7 verbatim: strict range and [mem(ν,x) ⟺ lo < x ≤ lo + r]. *)
Definition bst_gen_paper_ty : context_ty :=
  bst_full_ty range_strict_paper_ty true bst_keys_exact.

(** Fig. 7 with the range off-by-one repaired ([x ≤ ν ≤ y]) and the prose
    reading "every BST whose keys lie within (lo, lo+r]" ([⟹]). *)
Definition bst_gen_must_ty : context_ty :=
  bst_full_ty range_le_under_ty true bst_keys_within.

(** Safety (may) counterpart: every produced tree is a BST whose keys lie in
    (lo, lo+r]; range is a precise generator of [x, y]. *)
Definition bst_gen_may_ty : context_ty :=
  bst_full_ty range_le_precise_ty false bst_keys_within.

(** ** A-normal variant of the program *)

Definition one_x : atom := 31%positive.

(** The body is split into named continuations only for readability of the
    derivation; [bst_inner lo_a] unfolds to the program text of Fig. 7. *)
Definition bst_node_k : tm := [| new_lo, left_tree, right_tree |].

Definition bst_right_k : tm :=
  let right_tree := rec @@@ (right_size, new_lo, range_arg) in bst_node_k.

Definition bst_left_k (lo_a : atom) : tm :=
  let left_tree := rec @@@ (left_size, lo_a, range_arg) in bst_right_k.

Definition bst_nlo_k (lo_a : atom) : tm :=
  let new_lo := lo_a ⟨ + ⟩ rp in bst_left_k lo_a.

Definition bst_rs_k (lo_a : atom) : tm :=
  let right_size := r ⟨ - ⟩ rp in bst_nlo_k lo_a.

Definition bst_ls_k (lo_a : atom) : tm :=
  let left_size := rp ⟨ - ⟩ vnat 1 in bst_rs_k lo_a.

Definition bst_rp_k (lo_a : atom) : tm :=
  let rp := range_arg @@ (one_x, r) in bst_ls_k lo_a.

Definition bst_else_body (lo_a : atom) : tm :=
  let one_x := ret (vnat 1) in bst_rp_k lo_a.

Definition bst_inner (lo_a : atom) : tm :=
  let isz := r ⟨ ≤ ⟩ vnat 0 in
  if isz then ret leaf_value
  else ret leaf_value ⊕ₙ bst_else_body lo_a.

Definition bst_range_lam (lo_a : atom) : tm :=
  ret (ƛ range_arg : ℕ →ᵦ ℕ →ᵦ ℕ => bst_inner lo_a).

Definition bst_gen_program_anf : tm :=
  ret (μ rec, r : ℕ ~> ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree =>
    ret (ƛ lo : ℕ => bst_range_lam lo)).


(** ** Normalising opened qualifiers into named form *)

Definition simple_value (v : value) : Prop :=
  match v with
  | vconst _ | vfvar _ | vbvar _ => True
  | _ => False
  end.

Lemma bst_lstore_swap_lookup a b (σ : gmap logic_var value) w :
  (lstore_swap a b σ : gmap logic_var value) !! w = σ !! swap a b w.
Proof.
  exact (storeA_swap_lookup_inv a b σ w).
Qed.

Lemma bst_denote_open_swap k x (σ : gmap logic_var value) v :
  simple_value v ->
  LVFree x ∉ lvar_value_keys v ->
  denote_lvar_value (lstore_swap (LVBound k) (LVFree x) σ) v =
  denote_lvar_value σ (open_value k (vfvar x) v).
Proof.
  intros Hs Hx.
  destruct v as [c|z|j|? ?|? ?]; cbn [simple_value] in Hs; try contradiction;
    cbn [denote_lvar_value open_value lvar_value_keys] in *.
  - reflexivity.
  - rewrite bst_lstore_swap_lookup.
    rewrite swap_fresh by set_solver; reflexivity.
  - rewrite bst_lstore_swap_lookup.
    destruct (decide (k = j)) as [->|Hne].
    + rewrite swap_l. reflexivity.
    + rewrite swap_fresh by congruence; reflexivity.
Qed.

Lemma bst_keys_open_swap k x v :
  simple_value v ->
  LVFree x ∉ lvar_value_keys v ->
  set_swap (LVBound k) (LVFree x) (lvar_value_keys v) =
  lvar_value_keys (open_value k (vfvar x) v).
Proof.
  intros Hs Hx.
  destruct v as [c|z|j|? ?|? ?]; cbn [simple_value] in Hs; try contradiction;
    cbn [open_value lvar_value_keys] in *.
  - apply set_swap_empty.
  - apply set_eq. intros u. rewrite elem_of_set_swap.
    rewrite !elem_of_singleton.
    destruct (decide (u = LVBound k)) as [->|Hk].
    + rewrite swap_l. split; intros Heq; [inversion Heq; subst; set_solver|congruence].
    + destruct (decide (u = LVFree x)) as [->|Hxu].
      * rewrite swap_r. set_solver.
      * rewrite swap_fresh by congruence. reflexivity.
  - destruct (decide (k = j)) as [->|Hne]; cbn [lvar_value_keys].
    + apply set_eq. intros u. rewrite elem_of_set_swap, !elem_of_singleton.
      split.
      * intros Hu. destruct (decide (u = LVFree x)) as [->|Hxu]; [reflexivity| ].
        destruct (decide (u = LVBound j)) as [->|Hju].
        -- rewrite swap_l in Hu. congruence.
        -- rewrite swap_fresh in Hu by congruence. congruence.
      * intros ->. apply swap_r.
    + apply set_eq. intros u. rewrite elem_of_set_swap, !elem_of_singleton.
      split.
      * intros Hu. destruct (decide (u = LVFree x)) as [->|Hxu].
        -- rewrite swap_r in Hu. congruence.
        -- destruct (decide (u = LVBound k)) as [->|Hku].
           ++ rewrite swap_l in Hu. congruence.
           ++ rewrite swap_fresh in Hu by congruence. exact Hu.
      * intros ->. apply swap_fresh; congruence.
Qed.

Lemma bst_set_swap_union {A} `{Countable A} (a b : A) (X Y : gset A) :
  set_swap a b (X ∪ Y) = set_swap a b X ∪ set_swap a b Y.
Proof.
  apply set_eq. intros u. rewrite elem_of_union, !elem_of_set_swap, elem_of_union.
  reflexivity.
Qed.

Ltac bst_qual_open_solve :=
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom];
  [ rewrite ?bst_set_swap_union;
    rewrite ?bst_keys_open_swap by (cbn [simple_value]; auto; set_solver);
    reflexivity
  | intros s1 s2 Hs;
    unfold lstore_on_open_back; cbn [lso_store storeAO_store];
    rewrite ?bst_denote_open_swap by (cbn [simple_value]; auto; set_solver);
    rewrite Hs; reflexivity ].

Lemma bst_q_nat2_open k x a b P :
  simple_value a -> simple_value b ->
  LVFree x ∉ lvar_value_keys a ∪ lvar_value_keys b ->
  qual_open_atom k x (q_nat2 a b P) =
  q_nat2 (open_value k (vfvar x) a) (open_value k (vfvar x) b) P.
Proof.
  intros Ha Hb Hx. unfold q_nat2.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - rewrite bst_set_swap_union.
    rewrite !bst_keys_open_swap by (auto; set_solver). reflexivity.
  - intros s1 s2 Hs. unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !bst_denote_open_swap by (auto; set_solver).
    rewrite Hs. reflexivity.
Qed.

Lemma bst_q_nat3_open k x a b c P :
  simple_value a -> simple_value b -> simple_value c ->
  LVFree x ∉ lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c ->
  qual_open_atom k x (q_nat3 a b c P) =
  q_nat3 (open_value k (vfvar x) a) (open_value k (vfvar x) b)
    (open_value k (vfvar x) c) P.
Proof.
  intros Ha Hb Hc Hx. unfold q_nat3.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - rewrite !bst_set_swap_union.
    rewrite !bst_keys_open_swap by (auto; set_solver). reflexivity.
  - intros s1 s2 Hs. unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !bst_denote_open_swap by (auto; set_solver).
    rewrite Hs. reflexivity.
Qed.

Lemma bst_q_tree_spec_open k x a b c P :
  simple_value a -> simple_value b -> simple_value c ->
  LVFree x ∉ lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c ->
  qual_open_atom k x (q_tree_spec a b c P) =
  q_tree_spec (open_value k (vfvar x) a) (open_value k (vfvar x) b)
    (open_value k (vfvar x) c) P.
Proof.
  intros Ha Hb Hc Hx. unfold q_tree_spec.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - rewrite !bst_set_swap_union.
    rewrite !bst_keys_open_swap by (auto; set_solver). reflexivity.
  - intros s1 s2 Hs. unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !bst_denote_open_swap by (auto; set_solver).
    rewrite Hs. reflexivity.
Qed.

Lemma bst_qual_top_open k x :
  qual_open_atom k x (qual_top : type_qualifier) = qual_top.
Proof.
  unfold qual_top.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - apply set_swap_empty.
  - intros. reflexivity.
Qed.

(** ** Opening the [lo] binder of the program *)

Definition bst_fun_basic_ty : ty := ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree.

Definition bst_fixed_atoms : aset :=
  {[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
  {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪ {[right_tree]}.

Definition bst_env3 (lo_a : atom) : gmap atom ty :=
  <[lo_a := TBase TNat]> (<[rec := TBase TNat →ₜ bst_fun_basic_ty]>
    (<[r := TBase TNat]> ∅)).

Ltac bst_atoms_unfold :=
  unfold bst_fixed_atoms, r, lo, range_arg, rec, isz, one_x, rp, left_size,
    right_size, new_lo, left_tree, right_tree in *.

Definition bst_fresh (y : atom) : Prop :=
  y <> r /\ y <> rec /\ y <> lo /\ y <> range_arg /\ y <> isz /\ y <> one_x /\
  y <> rp /\ y <> left_size /\ y <> right_size /\ y <> new_lo /\
  y <> left_tree /\ y <> right_tree.

Lemma bst_fresh_of_notin y : y ∉ bst_fixed_atoms -> bst_fresh y.
Proof. unfold bst_fixed_atoms, bst_fresh. intros H. repeat split; set_solver. Qed.

Ltac bst_fresh_hyps :=
  repeat match goal with
  | H : ?y ∉ bst_fixed_atoms |- _ =>
      let F := fresh "Hfr" in
      pose proof (bst_fresh_of_notin y H) as F; clear H;
      unfold bst_fresh in F;
      repeat match type of F with
             | _ /\ _ => let F1 := fresh "Hne" in destruct F as [F1 F]
             end
  end.

Ltac bst_neq :=
  solve [ congruence
        | unfold r, lo, range_arg, rec, isz, one_x, rp, left_size,
            right_size, new_lo, left_tree, right_tree in *; congruence ].

Lemma bst_subst_shift_mutual x y :
  (forall v k, value_subst x (vfvar y) (value_shift k v) =
               value_shift k (value_subst x (vfvar y) v)) *
  (forall e k, tm_subst x (vfvar y) (tm_shift k e) =
               tm_shift k (tm_subst x (vfvar y) e)).
Proof.
  apply value_tm_mutind; intros; cbn [value_subst tm_subst value_shift tm_shift];
    try reflexivity; try (f_equal; eauto; fail);
    try (match goal with |- context [decide ?P] => destruct (decide P) end; reflexivity);
    try (match goal with |- context [bool_decide ?P] => destruct (bool_decide P) end; reflexivity);
    try (rewrite ?H, ?H0, ?H1; reflexivity).
Qed.

Lemma bst_subst_let_named x y z e1 e2 :
  z <> x -> z <> y ->
  tm_subst x (vfvar y) (let_named z e1 e2) =
  let_named z (tm_subst x (vfvar y) e1) (tm_subst x (vfvar y) e2).
Proof.
  intros Hzx Hzy. unfold let_named. cbn [tm_subst].
  rewrite subst_close_tm; [reflexivity| cbn [fv_value]; set_solver | congruence].
Qed.

Lemma bst_subst_lam_named x y z T e :
  z <> x -> z <> y ->
  value_subst x (vfvar y) (lam_named z T e) =
  lam_named z T (tm_subst x (vfvar y) e).
Proof.
  intros Hzx Hzy. unfold lam_named. cbn [value_subst].
  rewrite subst_close_tm; [reflexivity| cbn [fv_value]; set_solver | congruence].
Qed.

Lemma bst_subst_nondet x y e1 e2 :
  tm_subst x (vfvar y) (nondet_tm e1 e2) =
  nondet_tm (tm_subst x (vfvar y) e1) (tm_subst x (vfvar y) e2).
Proof.
  unfold nondet_tm. cbn [tm_subst value_subst].
  rewrite !(snd (bst_subst_shift_mutual x y)). reflexivity.
Qed.

Lemma bst_subst_call2 x y f a b :
  tm_subst x (vfvar y) (call2_tm f a b) =
  call2_tm (value_subst x (vfvar y) f) (value_subst x (vfvar y) a)
    (value_subst x (vfvar y) b).
Proof.
  unfold call2_tm, tapp_tm, case_app. cbn [tm_subst value_subst].
  rewrite !(fst (bst_subst_shift_mutual x y)). reflexivity.
Qed.

Lemma bst_subst_call3 x y f a b c :
  tm_subst x (vfvar y) (call3_tm f a b c) =
  call3_tm (value_subst x (vfvar y) f) (value_subst x (vfvar y) a)
    (value_subst x (vfvar y) b) (value_subst x (vfvar y) c).
Proof.
  unfold call3_tm. unfold tapp_tm at 1. cbn [tm_subst value_subst].
  rewrite bst_subst_call2.
  rewrite !(fst (bst_subst_shift_mutual x y)). reflexivity.
Qed.

Lemma bst_open_close_subst x y e :
  open_tm 0 (vfvar x) e = e ->
  open_tm 0 (vfvar y) (close_tm x 0 e) = tm_subst x (vfvar y) e.
Proof.
  intros Hopen.
  rewrite <- (subst_intro_tm x (vfvar y) 0 (close_tm x 0 e)).
  - rewrite open_close_var_tm_aux by exact Hopen. reflexivity.
  - apply close_rm_fv_tm.
  - constructor.
Qed.

Lemma bst_open_close_lo y :
  y ∉ bst_fixed_atoms ->
  open_tm 0 (vfvar y) (close_tm lo 0 (bst_range_lam lo)) = bst_range_lam y.
Proof.
  intros Hy. bst_fresh_hyps.
  rewrite bst_open_close_subst by reflexivity.
  unfold bst_range_lam, bst_inner, bst_else_body, bst_rp_k, bst_ls_k, bst_rs_k,
    bst_nlo_k, bst_left_k, bst_right_k, bst_node_k, Ret.
  cbn [tm_subst].
  rewrite bst_subst_lam_named by bst_neq.
  rewrite bst_subst_let_named by bst_neq.
  unfold if_named. cbn [tm_subst].
  rewrite bst_subst_nondet.
  rewrite !bst_subst_let_named by bst_neq.
  rewrite !bst_subst_call2, !bst_subst_call3.
  unfold node_tm, avar, vnat, leaf_value. cbn [tm_subst value_subst].
  repeat match goal with
    | |- context [decide (?a = ?b)] =>
        destruct (decide (a = b)); try (exfalso; bst_neq); try congruence
    end.
Qed.

(** ** Contexts of the derivation *)

Definition bst_RECTY (R : context_ty) (ang : bool) P : context_ty :=
  fix_rec_call_ty TNat r {: TNat | qual_top} (bst_body_ty R ang P).

Definition bst_Γrec (R : context_ty) (ang : bool) P : ctx :=
  (Emp ,, (r ∷ {: TNat | qual_top})) ,, (rec ∷ bst_RECTY R ang P).

Definition bst_Γ3 (R : context_ty) (ang : bool) P (y : atom) : ctx :=
  (bst_Γrec R ang P ,, (y ∷ O[ ℕ ])) ,, (range_arg ∷ R).

Definition bst_RES (ang : bool) P (y : atom) : context_ty :=
  bst_res_ty ang (q_tree_spec (vfvar r) (vfvar y) ν P).


(** ** Contexts of the may (safety) derivation *)

Definition bst_P : nat -> nat -> tree -> Prop := bst_keys_within.
Definition bst_Rp : context_ty := range_le_precise_ty.

Definition bst_τisz : context_ty := binop_precise_ty bop_le (vfvar r) (vnat 0).

Definition bst_Γ4 (y : atom) : ctx :=
  bst_Γ3 bst_Rp false bst_P y ,, (isz ∷ bst_τisz).
Definition bst_Γt (y : atom) : ctx :=
  bst_Γ3 bst_Rp false bst_P y ,, (isz ∷ (bst_τisz ⊓ bool_precise_ty true)).
Definition bst_Γf (y : atom) : ctx :=
  bst_Γ3 bst_Rp false bst_P y ,, (isz ∷ (bst_τisz ⊓ bool_precise_ty false)).

Definition bst_τbg : context_ty := primop_precise_ty op_boolGen (vbool false).

Definition bst_Γb (y b : atom) : ctx := bst_Γf y ,, (b ∷ bst_τbg).
Definition bst_Γbt (y b : atom) : ctx := bst_Γf y ,, (b ∷ bool_precise_ty true).
Definition bst_Γbf (y b : atom) : ctx := bst_Γf y ,, (b ∷ bool_precise_ty false).

Definition bst_Γone (y b : atom) : ctx :=
  bst_Γbf y b ,, (one_x ∷ const_precise_ty (cnat 1)).

Definition bst_τrp : context_ty :=
  precise_ty TNat (q_nat3 (vnat 1) ν (vfvar r) (fun x v y => x <= v <= y)).

Definition bst_Γrp (y b : atom) : ctx := bst_Γone y b ,, (rp ∷ bst_τrp).
Definition bst_Γls (y b : atom) : ctx :=
  bst_Γrp y b ,, (left_size ∷ binop_precise_ty bop_minus (vfvar rp) (vnat 1)).
Definition bst_Γrs (y b : atom) : ctx :=
  bst_Γls y b ,, (right_size ∷ binop_precise_ty bop_minus (vfvar r) (vfvar rp)).
Definition bst_Γnlo (y b : atom) : ctx :=
  bst_Γrs y b ,, (new_lo ∷ binop_precise_ty bop_plus (vfvar y) (vfvar rp)).

Definition bst_τleft (y : atom) : context_ty :=
  bst_res_ty false (q_tree_spec (vfvar left_size) (vfvar y) ν bst_P).
Definition bst_τright : context_ty :=
  bst_res_ty false (q_tree_spec (vfvar right_size) (vfvar new_lo) ν bst_P).

Definition bst_Γleft (y b : atom) : ctx := bst_Γnlo y b ,, (left_tree ∷ bst_τleft y).
Definition bst_Γright (y b : atom) : ctx := bst_Γleft y b ,, (right_tree ∷ bst_τright).

Fixpoint comma_binds (Γ : ctx) (x : atom) (τ : context_ty) : Prop :=
  match Γ with
  | CtxBind y τ' => y = x /\ τ' = τ
  | CtxComma Γ1 Γ2 => comma_binds Γ1 x τ \/ comma_binds Γ2 x τ
  | _ => False
  end.

Definition bst_le2 : nat -> nat -> Prop := fun x v => x <= v.
Definition bst_le3 : nat -> nat -> nat -> Prop := fun x v y => x <= v <= y.

Definition bst_range_tail : context_ty :=
  {: TNat | q_nat2 (vbvar 1) ν (fun x v => x <= v) } →
  precise_ty TNat (q_nat3 (vbvar 2) ν (vbvar 1) (fun x v y => x <= v <= y)).

Definition bst_Tg : context_ty :=
  {: TNat | q_nat2 (vfvar one_x) ν (fun x v => x <= v) } →
  precise_ty TNat (q_nat3 (vfvar one_x) ν (vbvar 1) (fun x v y => x <= v <= y)).

Definition bst_Tg_closed : context_ty :=
  {: TNat | q_nat2 (vnat 1) ν (fun x v => x <= v) } →
  precise_ty TNat (q_nat3 (vnat 1) ν (vbvar 1) (fun x v y => x <= v <= y)).

Definition bst_r_pos_ty : context_ty :=
  {: TNat | q_nat2 (vnat 1) ν (fun x v => x <= v) }.


Definition bst_lt_r_ty : context_ty :=
  O[ ℕ ] ⊓ {: TNat | mk_q_lt_base TNat (vbvar 0) (vfvar r) }.

Definition bst_T1 (s : atom) : context_ty :=
  O[ ℕ ] → bst_Rp → bst_res_ty false (q_tree_spec (vfvar s) (vbvar 2) ν bst_P).
Definition bst_T2 (s l : atom) : context_ty :=
  bst_Rp → bst_res_ty false (q_tree_spec (vfvar s) (vfvar l) ν bst_P).


(** ** Local automation for well-formedness side goals *)

Lemma bst_erase_dom_subset Γ : dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ.
  - cbn. rewrite dom_empty_L. set_solver.
  - assert (Hd : dom (erase_ctx (CtxBind x τ)) = {[x]})
      by (apply (dom_singleton_L (M := gmap atom) (D := gset atom))).
    rewrite Hd. cbn [ctx_dom]. set_solver.
  - assert (Hd : dom (erase_ctx (CtxComma Γ1 Γ2)) =
              dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2))
      by (apply (dom_union_L (M := gmap atom) (D := gset atom))).
    rewrite Hd. cbn [ctx_dom]. set_solver.
  - assert (Hd : dom (erase_ctx (CtxStar Γ1 Γ2)) =
              dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2))
      by (apply (dom_union_L (M := gmap atom) (D := gset atom))).
    rewrite Hd. cbn [ctx_dom]. set_solver.
  - cbn [erase_ctx ctx_dom]. set_solver.
Qed.

Lemma bst_erase_comma Γ x τ :
  x ∉ ctx_dom Γ ->
  erase_ctx (Γ ,, (x ∷ τ)) = <[x := erase_ty τ]> (erase_ctx Γ).
Proof.
  intros Hx. apply erase_ctx_comma_bind_fresh.
  pose proof (bst_erase_dom_subset Γ). set_solver.
Qed.

Lemma bst_erase_sum Γ1 Γ2 : erase_ctx (Γ1 ⊕ Γ2) = erase_ctx Γ1.
Proof. reflexivity. Qed.

Ltac bst_unfold_tys :=
  unfold bst_range_tail, bst_Tg, bst_Tg_closed, bst_r_pos_ty,
    bst_lt_r_ty, bst_T1, bst_T2, bst_τleft, bst_τright, bst_τrp, bst_τbg,
    bst_τisz, bst_Rp, bst_P, bst_full_ty, bst_body_ty, bst_RES, bst_RECTY,
    range_le_precise_ty, range_le_inner_ty, range_le_under_ty,
    range_strict_paper_ty;
  unfold const_precise_ty, bool_precise_ty, binop_precise_ty,
    primop_precise_ty, tree_node_precise_ty, fix_rec_call_ty;
  unfold precise_ty, over_ty, under_ty, bst_res_ty;
  unfold binop_result_qual, primop_result_qual, tree_node_result_qual,
    bool_qual, mk_q_eq, mk_q_lt_base, q_nat2, q_nat3, q_tree_spec,
    qual_top, ONat, OTree, OBool, vnu.

Ltac bst_in_set :=
  lazymatch goal with
  | |- _ ∈ _ ∪ _ =>
      first [ apply elem_of_union_l; bst_in_set
            | apply elem_of_union_r; bst_in_set ]
  | |- _ ∈ {[_]} => apply elem_of_singleton; reflexivity
  end.

Ltac bst_lvars_wf :=
  let k := fresh "k" in let x := fresh "x" in let Hx := fresh "Hx" in
  intros [k|x] Hx; cbn [lvar_wf_at];
  cbn [qual_vars qual_lvars lvar_value_keys] in Hx;
  set_unfold in Hx;
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
  repeat match goal with
         | H : LVBound _ = LVBound _ |- _ => inversion H; subst; clear H
         | H : LVFree _ = LVFree _ |- _ => inversion H; subst; clear H
         end;
  try (apply Nat.ltb_lt; reflexivity);
  try discriminate; try contradiction;
  try (clear; lia);
  try solve [bst_in_set].

Lemma bst_res_ty_erase ang q : erase_ty (bst_res_ty ang q) = TBase TTree.
Proof. destruct ang; reflexivity. Qed.

Ltac bst_ty_wf :=
  bst_unfold_tys;
  repeat match goal with |- context [match ?b with true => _ | false => _ end] =>
    destruct b end;
  cbn [wf_context_ty_at basic_context_ty qual_vars qual_lvars lvar_value_keys
       erase_ty prim_op_type bin_op_type base_ty_of_const];
  repeat split; try reflexivity;
  try match goal with
      | H : forall d D, wf_context_ty_at d D ?R |- wf_context_ty_at _ _ ?R =>
          apply H
      | H : erase_ty ?R = _ |- context [erase_ty ?R] => rewrite H; reflexivity
      end;
  try bst_lvars_wf.

Ltac bst_lookup_none :=
  lazymatch goal with
  | |- @lookup _ _ _ _ ?x (@insert _ _ _ _ ?y ?T ?m) = None =>
      transitivity (m !! x);
      [apply map_lookup_insert_ne; bst_neq | bst_lookup_none]
  | |- _ => reflexivity
  end.

Ltac bst_notin_dom :=
  apply not_elem_of_dom; bst_lookup_none.

Ltac bst_fresh_dom := first [ solve [bst_notin_dom] | basic_type_fresh ].

Ltac bst_basic_go :=
  lazymatch goal with
  | |- _ ⊢ₑ tret (fixfun_named _ _ _ _ _) ⋮ _ =>
      eapply TT_Ret; eapply basic_typing_fixfun_named;
      [bst_fresh_dom | bst_fresh_dom | bst_basic_go]
  | |- _ ⊢ₑ tret (lam_named _ _ _) ⋮ _ =>
      eapply TT_Ret; eapply basic_typing_lam_named;
      [bst_fresh_dom | bst_basic_go]
  | |- _ ⊢ₑ tret (vlam ?T (close_tm ?x 0 ?e)) ⋮ _ =>
      change (vlam T (close_tm x 0 e)) with (lam_named x T e); bst_basic_go
  | |- ?Γ ⊢ₑ tlete (tprim op_boolGen (vbool false))
              (tmatch (vbvar 0) (tm_shift 0 ?e1) (tm_shift 0 ?e2)) ⋮ ?T =>
      change (Γ ⊢ₑ nondet_tm e1 e2 ⋮ T);
      eapply basic_typing_nondet_tm; [bst_basic_go | bst_basic_go]
  | |- ?Γ ⊢ₑ tlete ?ef (tapp (vbvar 0) ?vx) ⋮ ?T =>
      change (Γ ⊢ₑ tapp_tm ef vx ⋮ T);
      eapply basic_typing_tapp_tm; [bst_basic_go | bst_basic_go]
  | |- _ ⊢ᵥ value_shift _ _ ⋮ _ =>
      cbn [value_shift avar]; bst_basic_go
  | |- _ ⊢ₑ tapp_tm _ _ ⋮ _ =>
      eapply basic_typing_tapp_tm; [bst_basic_go | bst_basic_go]
  | |- _ ⊢ₑ call2_tm _ _ _ ⋮ _ => unfold call2_tm; bst_basic_go
  | |- _ ⊢ₑ call3_tm _ _ _ _ ⋮ _ => unfold call3_tm; bst_basic_go
  | |- _ ⊢ₑ let_named _ _ _ ⋮ _ =>
      eapply basic_typing_let_named;
      [bst_fresh_dom | bst_basic_go | bst_basic_go]
  | |- _ ⊢ₑ nondet_tm _ _ ⋮ _ =>
      eapply basic_typing_nondet_tm; [bst_basic_go | bst_basic_go]
  | |- _ ⊢ₑ if_named _ _ _ ⋮ _ =>
      unfold if_named; eapply TT_Match; [basic_type | bst_basic_go | bst_basic_go]
  | |- _ ⊢ₑ tmatch _ _ _ ⋮ _ =>
      eapply TT_Match; [basic_type | bst_basic_go | bst_basic_go]
  | |- _ => basic_type
  end.

Ltac bst_basic :=
  unfold bst_gen_program_anf, bst_range_lam, bst_inner, bst_else_body,
    bst_rp_k, bst_ls_k, bst_rs_k, bst_nlo_k, bst_left_k, bst_right_k,
    bst_node_k, bst_env3, bst_fun_basic_ty, Ret;
  bst_basic_go.

Lemma bst_program_anf_basic :
  ∅ ⊢ₑ bst_gen_program_anf ⋮ (ℕ →ᵦ bst_fun_basic_ty).
Proof. bst_basic. Qed.

Ltac bst_unfold_ctxs :=
  unfold bst_Γright, bst_Γleft, bst_Γnlo, bst_Γrs, bst_Γls, bst_Γrp, bst_Γone,
    bst_Γbf, bst_Γbt, bst_Γb, bst_Γf, bst_Γt, bst_Γ4, bst_Γ3, bst_Γrec in *.

Ltac bst_notin_set :=
  lazymatch goal with
  | |- _ ∉ _ ∪ _ => apply not_elem_of_union; split; bst_notin_set
  | |- _ ∉ ∅ => apply not_elem_of_empty
  | |- _ ∉ {[_]} => apply not_elem_of_singleton; bst_neq
  end.

Ltac bst_unfold_atoms_goal :=
  unfold r, lo, range_arg, rec, isz, one_x, rp, left_size, right_size,
    new_lo, left_tree, right_tree.

Ltac bst_disj :=
  lazymatch goal with
  | |- ∅ ## _ => apply disjoint_empty_l
  | |- _ ## ∅ => apply disjoint_empty_r
  | |- _ ## {[_]} => apply disjoint_singleton_r; bst_notin_set
  | |- {[_]} ## _ => apply disjoint_singleton_l; bst_notin_set
  | |- _ ∪ _ ## _ => apply disjoint_union_l; split; bst_disj
  | |- _ ## _ ∪ _ => apply disjoint_union_r; split; bst_disj
  end.

Ltac bst_dom_fresh :=
  cbn [ctx_dom];
  first [ solve [bst_notin_set] | solve [bst_disj] ].

Ltac bst_clear_big :=
  repeat match goal with
  | H : context [has_extended_context_type] |- _ => clear H
  | H : context [context_typing_wf] |- _ => clear H
  | H : persistent_formula _ |- _ => clear H
  end.

Lemma bst_RES_erase ang P y : erase_ty (bst_RES ang P y) = TBase TTree.
Proof. destruct ang; reflexivity. Qed.

Lemma bst_body_ty_Rp_erase ang P :
  erase_ty (bst_body_ty bst_Rp ang P) = (ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree).
Proof. destruct ang; reflexivity. Qed.

Ltac bst_erase_norm :=
  rewrite ?bst_RES_erase;
  rewrite ?bst_erase_sum;
  repeat (rewrite bst_erase_comma by bst_dom_fresh);
  unfold bst_RECTY;
  cbn [erase_ctx erase_ty fix_rec_call_ty over_ty under_ty precise_ty];
  rewrite ?bst_res_ty_erase, ?bst_RES_erase, ?bst_body_ty_Rp_erase.



Ltac bst_ctx_wf :=
  unfold wf_ctx_under; rewrite ?dom_empty_L;
  bst_unfold_ctxs;
  cbn [basic_ctx ctx_dom];
  repeat split; try bst_dom_fresh; try bst_ty_wf; try reflexivity;
  try (bst_unfold_tys; cbn [erase_ctx erase_ty bin_op_type prim_op_type base_ty_of_const];
       reflexivity).

Ltac bst_wf_with basic_tac :=
  bst_clear_big;
  unfold context_typing_wf;
  lazymatch goal with
  | |- wf_ctx_under ?Σ ?Γ /\ _ =>
      let Hbctx := fresh "Hbctx" in
      assert (Hbctx : wf_ctx_under Σ Γ) by bst_ctx_wf;
      split; [exact Hbctx | split];
      [ unfold wf_ctx_under in Hbctx; rewrite ?dom_empty_L in Hbctx;
        rewrite (basic_ctx_erase_dom _ _ Hbctx); bst_unfold_ctxs;
        cbn [ctx_dom]; bst_ty_wf
      | clear Hbctx; bst_unfold_ctxs; bst_erase_norm; basic_tac ]
  end.

Ltac bst_split_notin H :=
  lazymatch type of H with
  | _ ∉ _ ∪ _ =>
      let H1 := fresh "Hn" in
      apply not_elem_of_union in H as [H1 H];
      bst_split_notin H1; bst_split_notin H
  | _ ∉ {[_]} => apply not_elem_of_singleton in H
  | _ => idtac
  end.

Ltac bst_open_norm :=
  unfold bst_range_tail, bst_Tg, bst_Tg_closed, bst_r_pos_ty, bst_lt_r_ty,
    bst_T1, bst_T2, bst_τleft, bst_τright, bst_τrp, bst_Rp, bst_P, precise_ty, over_ty, under_ty;
  cbn [cty_open bst_res_ty];
  rewrite ?bst_qual_top_open;
  rewrite ?bst_q_nat2_open, ?bst_q_nat3_open, ?bst_q_tree_spec_open
    by (cbn [simple_value lvar_value_keys];
        first [exact I | solve [bst_notin_set] | set_solver]);
  cbn [open_value];
  reflexivity.

Ltac bst_cb :=
  lazymatch goal with
  | |- _ \/ _ => first [left; bst_cb | right; bst_cb]
  | |- _ /\ _ => split; reflexivity
  end.

Ltac bst_comma_binds := bst_unfold_ctxs; cbn [comma_binds]; bst_cb.

Ltac bst_lookup_some :=
  lazymatch goal with
  | |- @lookup _ _ _ _ ?x (@insert _ _ _ _ ?y ?T ?m) = Some _ =>
      first [ apply map_lookup_insert
            | transitivity (m !! x);
              [apply map_lookup_insert_ne; bst_neq | bst_lookup_some] ]
  end.

Ltac bst_lookup :=
  bst_unfold_ctxs; bst_erase_norm; bst_lookup_some.

Ltac bst_ctx_ty_wf :=
  bst_clear_big;
  lazymatch goal with
  | |- wf_context_ty_at _ (dom (erase_ctx ?Γ)) _ =>
      let H := fresh "Hbctx" in
      assert (H : wf_ctx_under ∅ Γ) by bst_ctx_wf;
      unfold wf_ctx_under in H; rewrite ?dom_empty_L in H;
      rewrite (basic_ctx_erase_dom _ _ H); clear H;
      bst_unfold_ctxs; cbn [ctx_dom]; bst_ty_wf
  end.

Ltac bst_erase_eq :=
  bst_unfold_ctxs; bst_unfold_tys;
  cbn [erase_ctx erase_ty bin_op_type prim_op_type base_ty_of_const];
  reflexivity.
Section Outer.
  Variable R : context_ty.
  Variable ang : bool.
  Variable P : nat -> nat -> tree -> Prop.
  Hypothesis HRer : erase_ty R = (ℕ →ᵦ ℕ →ᵦ ℕ).
  Hypothesis HRopen : forall k x, cty_open k x R = R.
  Hypothesis HRwf : forall d D, wf_context_ty_at d D R.

  Lemma bst_body_ty_wf d D : wf_context_ty_at (S d) D (bst_body_ty R ang P).
  Proof.
    unfold bst_body_ty. cbn [wf_context_ty_at]. split; [ | split].
    - bst_ty_wf.
    - apply HRwf.
    - destruct ang; bst_ty_wf.
  Qed.

  Lemma bst_body_ty_erase :
    erase_ty (bst_body_ty R ang P) = bst_fun_basic_ty.
  Proof.
    unfold bst_body_ty, bst_fun_basic_ty. cbn [erase_ty]. rewrite HRer.
    destruct ang; reflexivity.
  Qed.

  Lemma bst_body_open x :
    cty_open 0 x (bst_body_ty R ang P) =
    (O[ ℕ ] → R → bst_res_ty ang (q_tree_spec (vfvar x) (vbvar 2) ν P)).
  Proof.
    unfold bst_body_ty. cbn [cty_open]. rewrite HRopen.
    unfold over_ty. cbn [cty_open]. rewrite bst_qual_top_open.
    destruct ang; cbn [bst_res_ty cty_open];
      rewrite bst_q_tree_spec_open by (cbn; auto; set_solver);
      reflexivity.
  Qed.

  Lemma bst_res_open x y :
    x <> y ->
    cty_open 0 y (R → bst_res_ty ang (q_tree_spec (vfvar x) (vbvar 2) ν P)) =
    (R → bst_res_ty ang (q_tree_spec (vfvar x) (vfvar y) ν P)).
  Proof.
    intros Hxy. cbn [cty_open]. rewrite HRopen.
    destruct ang; cbn [bst_res_ty cty_open];
      rewrite bst_q_tree_spec_open by (cbn; auto; set_solver);
      reflexivity.
  Qed.

  Lemma bst_outer_wf_top :
    ∅; Emp ⊢wf bst_gen_program_anf ⋮ bst_full_ty R ang P.
  Proof.
    unfold context_typing_wf. split; [ | split].
    - unfold wf_ctx_under. cbn. exact I.
    - unfold bst_full_ty. cbn [wf_context_ty_at]. split; [bst_ty_wf | ].
      apply bst_body_ty_wf.
    - unfold bst_full_ty. cbn [erase_ctx erase_ty]. rewrite bst_body_ty_erase.
      apply bst_program_anf_basic.
  Qed.

  Ltac bst_outer_basic :=
    rewrite ?bst_body_ty_erase, ?HRer; bst_basic.

  Lemma bst_outer
    (Hpers : persistent_formula (ctx_denote_under ∅ Emp)) :
    (forall y, y ∉ bst_fixed_atoms ->
       ∅; bst_Γ3 R ang P y ⊢ₓ bst_inner y ⋮ bst_RES ang P y) ->
    ∅; Emp ⊢ₓ bst_gen_program_anf ⋮ bst_full_ty R ang P.
  Proof.
    intros Hbody.
    pose proof bst_outer_wf_top as Hwf0.
    unfold bst_gen_program_anf, bst_full_ty in *.
    eapply EXT_PersistIntro; [exact Hwf0 | exact Hpers | ].
    refine (EXT_FixNamed ∅ Emp qual_top (bst_body_ty R ang P) rec r TNat
      bst_fun_basic_ty _ _ _ _).
    - apply bst_body_ty_erase.
    - unfold context_typing_wf. split; [ | split].
      + bst_ctx_wf.
      + cbn [wf_context_ty_at]. split; [bst_ty_wf | apply bst_body_ty_wf].
      + cbn [erase_ctx erase_ty]. rewrite bst_body_ty_erase.
        exact bst_program_anf_basic.
    - rewrite bst_body_open.
      eapply EXT_LamNamedErased;
        [unfold fix_rec_call_ty; cbn [erase_ty]; rewrite bst_body_ty_erase;
         reflexivity | | ].
      { bst_wf_with bst_outer_basic. }
      refine (EXT_Lam ∅ (bst_Γrec R ang P) O[ ℕ ]
        (R → bst_res_ty ang (q_tree_spec (vfvar r) (vbvar 2) ν P))
        (close_tm lo 0 (bst_range_lam lo)) bst_fixed_atoms _ _).
      { bst_wf_with bst_outer_basic. }
      intros y Hy.
      pose proof (bst_fresh_of_notin y Hy) as Hfr.
      change (close_tm lo 0 (bst_range_lam lo) ^^ y) with
        (open_tm 0 (vfvar y) (close_tm lo 0 (bst_range_lam lo))).
      rewrite (bst_open_close_lo y Hy).
      change ((R → bst_res_ty ang (q_tree_spec r (vbvar 2) ν P)) ^^ y) with
        (cty_open 0 y (R → bst_res_ty ang (q_tree_spec r (vbvar 2) ν P))).
      rewrite bst_res_open by (destruct Hfr; congruence).
      unfold bst_fresh in Hfr. destruct_and! Hfr.
      unfold bst_range_lam.
      eapply EXT_LamNamedErased; [rewrite HRer; reflexivity | | ].
      { bst_wf_with bst_outer_basic. }
      apply Hbody. exact Hy.
  Qed.
End Outer.

Lemma bst_fv_closed_ty_at d τ :
  wf_context_ty_at d ∅ τ -> fv_cty τ = ∅.
Proof.
  intros Hwf. pose proof (wf_context_ty_at_fv_subset d ∅ τ Hwf). set_solver.
Qed.

Lemma bst_fv_closed_ty τ :
  wf_context_ty_at 0 ∅ τ -> fv_cty τ = ∅.
Proof. apply bst_fv_closed_ty_at. Qed.

Lemma bst_comma_binds_denote Γ x τ :
  comma_binds Γ x τ ->
  wf_context_ty_at 0 ∅ τ ->
  forall (Σ : gmap atom ty) m,
    m ⊨ ctx_denote_under Σ Γ -> m ⊨ ctx_denote_under ∅ (x ∷ τ).
Proof.
  intros Hb Hτ. induction Γ as [ | y τ' | Γ1 IH1 Γ2 IH2 | Γ1 _ Γ2 _ | Γ1 _ Γ2 _ ];
    intros Σ m Hm; cbn [comma_binds] in Hb; try contradiction.
  - destruct Hb as [-> ->].
    rewrite ctx_denote_under_minimal in Hm.
    cbn [ctx_fv] in Hm. rewrite (bst_fv_closed_ty τ Hτ) in Hm.
    rewrite storeA_restrict_empty_set in Hm.
    exact Hm.
  - destruct Hb as [Hb|Hb].
    + eapply IH1; [exact Hb | ]. eapply ctx_denote_under_comma_left. exact Hm.
    + cbn [ctx_denote_under] in Hm.
      rewrite res_models_and_iff in Hm. destruct Hm as [_ Hm].
      rewrite res_models_and_iff in Hm. destruct Hm as [_ Hm].
      eapply IH2; [exact Hb | exact Hm].
Qed.

Lemma bst_ctx_bind_closed_fv x τ :
  wf_context_ty_at 0 ∅ τ ->
  formula_fv (ctx_denote_under ∅ (x ∷ τ)) ⊆ {[x]}.
Proof.
  intros Hτ.
  cbn [ctx_denote_under ctx_fv]. rewrite (bst_fv_closed_ty τ Hτ).
  rewrite !storeA_restrict_empty_set.
  rewrite !formula_fv_and, formula_fv_basic_world_formula.
  rewrite lvars_fv_atom_env_to_lty_env_dom.
  unfold ty_denote.
  pose proof (formula_fv_ty_denote_gas_subset_relevant (cty_depth τ)
    (atom_env_to_lty_env (<[x:=erase_ty τ]> (∅ : gmap atom ty))) τ (tret (vfvar x)))
    as Hsub.
  rewrite (bst_fv_closed_ty τ Hτ) in Hsub. cbn [fv_tm fv_value] in Hsub.
  intros a Ha. apply elem_of_union in Ha as [Ha|Ha].
  - assert (Hd : dom ((∅ : gmap atom ty) ∪ erase_ctx (x ∷ τ)) =
              dom (∅ : gmap atom ty) ∪ dom (erase_ctx (x ∷ τ)))
      by (apply (dom_union_L (M := gmap atom) (D := gset atom))).
    assert (Hd2 : dom (erase_ctx (x ∷ τ)) = {[x]})
      by (apply (dom_singleton_L (M := gmap atom) (D := gset atom))).
    change (a ∈ dom ((∅ : gmap atom ty) ∪ erase_ctx (x ∷ τ))) in Ha.
    rewrite Hd, Hd2, dom_empty_L in Ha. set_solver.
  - pose proof (Hsub a Ha). set_solver.
Qed.

(** ** Semantic side conditions

    [ctx_sub_under] and [sub_type_under] bundle syntactic well-formedness
    with a semantic implication.  The syntactic halves are discharged by
    tactics; the semantic halves are the named obligations below. *)

Definition bst_ctx_sub_sem (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  forall m, m ⊨ ctx_denote_under ∅ Γ1 ->
    exists m', res_restrict m X ⊑ m' /\ m' ⊨ ctx_denote_under ∅ Γ2.

Definition bst_sub_sem (Γ : ctx) (τ1 τ2 : context_ty) : Prop :=
  forall e, erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ1 ->
    ctx_denote_under ∅ Γ ⊫
      FImpl (ty_denote (erase_ctx Γ) τ1 e) (ty_denote (erase_ctx Γ) τ2 e).

Lemma bst_ctx_sub_intro X Γ1 Γ2 :
  wf_ctx_under ∅ Γ1 -> wf_ctx_under ∅ Γ2 ->
  ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2) ->
  bst_ctx_sub_sem X Γ1 Γ2 ->
  ctx_sub_under ∅ X Γ1 Γ2.
Proof.
  intros H1 H2 H3 H4. split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]].
Qed.

Lemma bst_sub_intro Γ τ1 τ2 :
  wf_ctx_under ∅ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  bst_sub_sem Γ τ1 τ2 ->
  sub_type_under ∅ Γ τ1 τ2.
Proof.
  intros H1 H2 H3 H4 H5.
  split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | exact H5]]]].
Qed.

Lemma bst_gen_obl_persist_emp :
  persistent_formula (ctx_denote_under ∅ Emp).
Proof.
  apply persistent_formula_of_singleton_projection.
  intros m Hm.
  assert (Hfv : formula_fv (ctx_denote_under ∅ Emp) = ∅).
  { cbn [ctx_denote_under]. rewrite formula_fv_and, (formula_fv_true (V := value)),
      formula_fv_basic_world_formula.
    assert (E : store_restrict (∅ : gmap atom ty) (ctx_fv Emp) ∪ erase_ctx Emp = ∅)
      by reflexivity.
    rewrite E.
    assert (E2 : dom (atom_store_to_lvar_store (∅ : gmap atom ty)) = (∅ : lvset))
      by reflexivity.
    rewrite E2, lvars_fv_empty. set_solver. }
  rewrite Hfv. exists ∅. split.
  - reflexivity.
  - apply wfworld_ext. apply world_ext.
    + cbn. change (dom (∅ : gmap atom value)) with (∅ : aset). set_solver.
    + intros τ. cbn. split.
      * intros [σ0 [_ <-]]. apply storeA_restrict_empty_set.
      * intros ->. destruct (world_wf m) as [[σ0 Hσ0] _].
        exists σ0. split; [exact Hσ0 | apply storeA_restrict_empty_set].
Qed.

(** Any capability can be weakened to the empty context. *)
Lemma bst_gen_obl_ctx_emp Γ :
  bst_ctx_sub_sem ∅ Γ Emp.
Proof.
  intros m _. exists (res_restrict m ∅). split; [reflexivity | ].
  cbn [ctx_denote_under].
  assert (E : store_restrict (∅ : gmap atom ty) (ctx_fv Emp) ∪ erase_ctx Emp = ∅)
    by reflexivity.
  rewrite E.
  apply res_models_and_intro_from_models.
  - change (atom_env_to_lty_env (∅ : gmap atom ty)) with (∅ : lty_env).
    apply basic_world_formula_empty.
  - apply res_models_true.
Qed.

(** *** Generic semantic obligations (instantiated below) *)

(** Projection of a comma-spine context onto one of its bindings whose type
    is closed.  Informal argument: [ctx_denote_under] of a comma spine is a
    conjunction ([FAnd]) whose conjunct for [x] is
    [ty_denote (<[x:=⌊τ⌋]> Σ') τ (ret x)].  Because [τ] is closed this
    formula only mentions [x] (its guard is relativised to the relevant
    environment [{x}]), so by minimality ([res_models_minimal_on]) it holds of
    [res_restrict m {x}], which together with the basic-typing part of the
    singleton context is exactly [ctx_denote_under ∅ (x ∷ τ)].  This is the
    semantic content of T-Var + T-CtxSub (paper Example 3.2, T-Weakening). *)
Lemma bst_gen_obl_ctx_proj Γ x τ :
  comma_binds Γ x τ ->
  wf_ctx_under ∅ Γ ->
  wf_context_ty_at 0 ∅ τ ->
  bst_ctx_sub_sem ({[x]}) Γ (x ∷ τ).
Proof.
  intros Hb _ Hτ m Hm.
  exists (res_restrict m {[x]}). split; [reflexivity | ].
  apply (proj1 (res_models_minimal_on {[x]} m _ (bst_ctx_bind_closed_fv x τ Hτ))).
  exact (bst_comma_binds_denote Γ x τ Hb Hτ ∅ m Hm).
Qed.

(** Weakening a binding to the trivial demonic type [{b | ⊤}]:
    [{b | ⊤}] constrains nothing beyond its guard (basic typing of the value
    of [x] at [b], totality of [ret x], and well-formedness), all of which
    follow from the basic-world conjunct of [ctx_denote_under ∅ Γ] since
    [⌊Γ⌋ !! x = Some b] ([over_top_denotation_gas]). *)
Lemma bst_gen_obl_ctx_top Γ x b :
  wf_ctx_under ∅ Γ ->
  erase_ctx Γ !! x = Some (TBase b) ->
  bst_ctx_sub_sem ({[x]}) Γ (x ∷ over_ty b qual_top).
Proof.
  intros _ Hlook m Hm.
  assert (Hτ : wf_context_ty_at 0 ∅ (over_ty b qual_top)).
  { cbn. intros [k|a] Ha; cbn in *; set_solver. }
  exists (res_restrict m {[x]}). split; [reflexivity | ].
  apply (proj1 (res_models_minimal_on {[x]} m _ (bst_ctx_bind_closed_fv x _ Hτ))).
  set (Δ := <[x := TBase b]> (∅ : gmap atom ty)).
  assert (Hw : m ⊨ basic_world_formula (atom_env_to_lty_env Δ)).
  { pose proof (ctx_denote_under_basic_world ∅ Γ m Hm) as Hw0.
    eapply basic_world_formula_subenv; [ | exact Hw0].
    intros v T Hv. destruct v as [k|a].
    - rewrite atom_store_to_lvar_store_lookup_bound_none in Hv. discriminate.
    - rewrite atom_store_to_lvar_store_lookup_free in Hv |- *.
      assert (Hv' : (Δ : gmap atom ty) !! a = Some T) by exact Hv.
      subst Δ.
      destruct (decide (a = x)) as [->|Hne].
      + assert (E : (<[x := TBase b]> (∅ : gmap atom ty)) !! x = Some (TBase b))
          by (apply map_lookup_insert).
        rewrite E in Hv'. inversion Hv'; subst.
        assert (G : (ctx_erasure_under ∅ Γ : gmap atom ty) !! x = Some (TBase b)).
        { unfold ctx_erasure_under.
          apply map_lookup_union_Some_raw. right. split; [ | exact Hlook].
          apply storeA_restrict_lookup_none_l. apply lookup_empty. }
        exact G.
      + assert (E : (<[x := TBase b]> (∅ : gmap atom ty)) !! a = None).
        { transitivity ((∅ : gmap atom ty) !! a).
          - apply map_lookup_insert_ne. exact Hne.
          - apply lookup_empty. }
        rewrite E in Hv'. discriminate. }
  apply ctx_bind_from_base_denotation.
  - rewrite dom_empty_L. exact Hτ.
  - rewrite dom_empty_L. set_solver.
  - apply over_top_denotation_gas.
    apply (ty_denote_gas_guard_formula 0).
    apply ty_denote_gas_zero_tret_of_static_guard.
    pose proof (proj1 (basic_world_formula_models_iff _ m) Hw) as [Hlc [Hscope _]].
    unfold ty_static_guard_formula.
    apply res_models_and_intro_from_models; [ | apply res_models_and_intro_from_models].
    + apply context_ty_wf_formula_models_iff.
      split; [exact Hlc | split; [exact Hscope | ]].
      split.
      * cbn [context_ty_lvars context_ty_lvars_at over_ty qual_vars qual_lvars qual_top].
        rewrite lvars_at_depth_empty. set_solver.
      * exact I.
    + exact Hw.
    + apply expr_basic_typing_formula_models_iff.
      split; [exact Hlc | split; [exact Hscope | ]].
      apply basic_tm_has_ltype_of_atom_env_typing.
      constructor. constructor. apply map_lookup_insert.
Qed.

(** [□τ <: τ] (paper §5.1: "T-PersE is derivable from T-Sub and the fact
    Γ ⊢ □τ <: τ always holds").  Informal argument: [⟦□τ⟧ e] states that
    for the (single) result [x] of [e], [□ ⟦τ⟧ x], i.e. some singleton
    [{σ} ⊑ r] satisfies [⟦τ⟧ x]; by Kripke monotonicity of [⊑] and the fact
    that [r] restricted to [FV(⟦τ⟧ x)] is that singleton, [r ⊨ ⟦τ⟧ x]; the
    result-binding prefix is shared by both denotations.  Missing library
    piece (why this is not proved here): a "result prefix" lemma
    [⟦τ⟧ e ⇔ ∀ν. (e ⇓ ν per fibre over dom Σ) ⇒ ⟦τ⟧ (ret ν)] for EVERY type
    constructor (for [⊓]/[∪]/[⊕], which have no result binder, by
    induction), and, for [∪], the observation that [FPersist] forces [e] to
    be single-valued on each fibre; the two [FForall] bodies also have
    different free variables, so their fibre extensions must be translated
    between the two [ext_in] sets. *)
Lemma bst_gen_obl_persist_elim Γ τ :
  bst_sub_sem Γ (□ τ) τ.
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** Merging the two summands of a demonic sum.  Informal argument: the
    result capability is split as [r1 + r2] with both parts satisfying
    [{b | q}] at [ret ν]; [{b|q}] is the [FOver] of the exact atom fibred
    over [FV(q)∖{ν}], i.e. "every environment of every fibre satisfies [q]",
    which is preserved by union of capabilities over the same domain (a
    fibre of [r1 ∪ r2] is the union of the corresponding fibres). *)
Lemma bst_gen_obl_sum_over_merge Γ b q :
  bst_sub_sem Γ (({: b | q}) ⊕ ({: b | q})) ({: b | q}).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** [Leaf] satisfies the safety specification for any [r, lo].  Informal
    argument: the source type forces every result to be [Leaf]; [Leaf] is a
    BST without members, so [bst_keys_within n m Leaf] holds for all
    naturals [n, m]; the values of [rv], [lv] are naturals in every
    environment because of the basic-world conjunct of [⟦Γ⟧]. *)
Lemma bst_gen_obl_leaf_spec Γ rv lv :
  erase_ctx Γ !! rv = Some (TBase TNat) ->
  erase_ctx Γ !! lv = Some (TBase TNat) ->
  bst_sub_sem Γ (const_precise_ty (ctree tr_leaf))
    ({: TTree | q_tree_spec (vfvar rv) (vfvar lv) ν bst_keys_within }).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** ** Derived structural helpers (all proved from the [EXT_*] rules) *)



Lemma bst_const_typing Γ c τ :
  wf_ctx_under ∅ Γ ->
  ∅; Γ ⊢wf ret (vconst c) ⋮ τ ->
  wf_context_ty_at 0 ∅ (const_precise_ty c) ->
  erase_ty (const_precise_ty c) = erase_ty τ ->
  bst_sub_sem Γ (const_precise_ty c) τ ->
  ∅; Γ ⊢ₓ ret (vconst c) ⋮ τ.
Proof.
  intros HΓ Hwf Hcwf Her Hsem.
  pose proof (proj1 (proj2 Hwf)) as Hτwf.
  eapply EXT_Sub; [exact Hwf | | ].
  - eapply EXT_CtxSub.
    + split; [exact HΓ | split ].
      * eapply wf_context_ty_at_mono_env; [ | exact Hcwf]. set_solver.
      * rewrite Her. exact (proj2 (proj2 Hwf)).
    + eapply EXT_Const. split; [cbn; exact I | split].
      * cbn [erase_ctx]. rewrite dom_empty_L. exact Hcwf.
      * cbn [erase_ctx]. destruct c; constructor; constructor.
    + replace (fv_tm (ret (vconst c)) ∪ fv_cty (const_precise_ty c)) with (∅ : aset).
      2:{ rewrite (bst_fv_closed_ty _ Hcwf). cbn. set_solver. }
      apply bst_ctx_sub_intro; [exact HΓ | cbn; exact I | | apply bst_gen_obl_ctx_emp].
      intros a Ha. exfalso. set_solver.
  - apply bst_sub_intro; [exact HΓ | | exact Hτwf | exact Her | exact Hsem].
    eapply wf_context_ty_at_mono_env; [ | exact Hcwf]. set_solver.
Qed.

(** T-AppFun with the opened result type given up to equality. *)
Lemma bst_appfun Γ τx τ v1 (x : atom) τr :
  cty_open 0 x τ = τr ->
  ∅; Γ ⊢wf v1 @ x ⋮ τr ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  ∅; Γ ⊢ₓ ret v1 ⋮ (τx → τ) ->
  ∅; Γ ⊢ₓ ret (avar x) ⋮ τx ->
  ∅; Γ ⊢ₓ v1 @ x ⋮ τr.
Proof. intros <- Hwf Hx Hf Harg. eapply EXT_AppFun; eassumption. Qed.

(** Retrieving a variable whose binding type is closed: T-CtxSub to the
    singleton binding followed by T-Var. *)
Lemma bst_var_closed Γ x τ :
  ∅; Γ ⊢wf ret (avar x) ⋮ τ ->
  wf_context_ty_at 0 ∅ τ ->
  erase_ctx Γ !! x = Some (erase_ty τ) ->
  bst_ctx_sub_sem ({[x]}) Γ (x ∷ τ) ->
  ∅; Γ ⊢ₓ ret (avar x) ⋮ τ.
Proof.
  intros Hwf Hτ Hlook Hsem.
  eapply EXT_CtxSub; [exact Hwf | | ].
  - eapply EXT_Var. split; [ | split].
    + unfold wf_ctx_under. cbn. split; [set_solver | exact Hτ].
    + eapply wf_context_ty_at_mono_env; [ | exact Hτ]. set_solver.
    + cbn [erase_ctx]. constructor. constructor.
      apply map_lookup_singleton.
  - apply bst_ctx_sub_intro.
    + exact (proj1 Hwf).
    + unfold wf_ctx_under. cbn. split; [set_solver | exact Hτ].
    + intros a Ha. rewrite (bst_fv_closed_ty _ Hτ) in Ha.
      cbn [fv_tm fv_value avar] in Ha.
      assert (a = x) as -> by set_solver.
      rewrite Hlook. cbn [erase_ctx].
      symmetry. apply map_lookup_singleton.
    + replace (fv_tm (ret (avar x)) ∪ fv_cty τ) with ({[x]} : aset); [exact Hsem | ].
      rewrite (bst_fv_closed_ty _ Hτ). cbn. set_solver.
Qed.

Lemma bst_var_top Γ x b :
  ∅; Γ ⊢wf ret (avar x) ⋮ over_ty b qual_top ->
  erase_ctx Γ !! x = Some (TBase b) ->
  ∅; Γ ⊢ₓ ret (avar x) ⋮ over_ty b qual_top.
Proof.
  intros Hwf Hlook.
  apply bst_var_closed; [exact Hwf | | exact Hlook | ].
  - cbn. intros [k|a] Ha; cbn in *; set_solver.
  - apply bst_gen_obl_ctx_top; [exact (proj1 Hwf) | exact Hlook].
Qed.

Lemma bst_var_proj Γ x τ :
  ∅; Γ ⊢wf ret (avar x) ⋮ τ ->
  comma_binds Γ x τ ->
  wf_context_ty_at 0 ∅ τ ->
  erase_ctx Γ !! x = Some (erase_ty τ) ->
  ∅; Γ ⊢ₓ ret (avar x) ⋮ τ.
Proof.
  intros Hwf Hb Hτ Hlook.
  apply bst_var_closed; [exact Hwf | exact Hτ | exact Hlook | ].
  apply bst_gen_obl_ctx_proj; [exact Hb | exact (proj1 Hwf) | exact Hτ].
Qed.

Lemma bst_sub Γ e τ1 τ2 :
  ∅; Γ ⊢wf e ⋮ τ2 ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ->
  erase_ty τ1 = erase_ty τ2 ->
  bst_sub_sem Γ τ1 τ2 ->
  ∅; Γ ⊢ₓ e ⋮ τ1 ->
  ∅; Γ ⊢ₓ e ⋮ τ2.
Proof.
  intros Hwf Hτ1 Her Hsem He.
  eapply EXT_Sub; [exact Hwf | exact He | ].
  apply bst_sub_intro; [exact (proj1 Hwf) | exact Hτ1 | exact (proj1 (proj2 Hwf)) |
    exact Her | exact Hsem].
Qed.

(** A constant at its own precise type, in any context (T-CtxSub to [Emp]
    followed by T-Const). *)
Lemma bst_const_exact Γ c :
  ∅; Γ ⊢wf ret (vconst c) ⋮ const_precise_ty c ->
  wf_context_ty_at 0 ∅ (const_precise_ty c) ->
  ∅; Γ ⊢ₓ ret (vconst c) ⋮ const_precise_ty c.
Proof.
  intros Hwf Hcwf.
  eapply EXT_CtxSub; [exact Hwf | | ].
  - eapply EXT_Const. split; [cbn; exact I | split].
    + cbn [erase_ctx]. rewrite dom_empty_L. exact Hcwf.
    + cbn [erase_ctx]. destruct c; constructor; constructor.
  - replace (fv_tm (ret (vconst c)) ∪ fv_cty (const_precise_ty c)) with (∅ : aset).
    2:{ rewrite (bst_fv_closed_ty _ Hcwf). cbn. set_solver. }
    apply bst_ctx_sub_intro; [exact (proj1 Hwf) | cbn; exact I | | apply bst_gen_obl_ctx_emp].
    intros a Ha. exfalso. set_solver.
Qed.

(** ** The outer layers for the must and the verbatim paper types

    T-PersistI, T-Fix, T-Lam (dependent, cofinite) and T-LamNamed go through
    for every variant; what remains is the body judgment. *)

Lemma range_le_under_wf d D : wf_context_ty_at d D range_le_under_ty.
Proof. bst_ty_wf. Qed.

Lemma range_le_under_open k x : cty_open k x range_le_under_ty = range_le_under_ty.
Proof.
  apply (cty_open_above_lc_fresh 0); [lia | | ].
  - apply (wf_context_ty_at_lc 0 ∅). apply range_le_under_wf.
  - rewrite (bst_fv_closed_ty _ (range_le_under_wf 0 ∅)). set_solver.
Qed.

Lemma range_strict_paper_wf d D : wf_context_ty_at d D range_strict_paper_ty.
Proof. bst_ty_wf. Qed.

Lemma range_strict_paper_open k x :
  cty_open k x range_strict_paper_ty = range_strict_paper_ty.
Proof.
  apply (cty_open_above_lc_fresh 0); [lia | | ].
  - apply (wf_context_ty_at_lc 0 ∅). apply range_strict_paper_wf.
  - rewrite (bst_fv_closed_ty _ (range_strict_paper_wf 0 ∅)). set_solver.
Qed.

Lemma bst_gen_anf_must_outer :
  (forall y, y ∉ bst_fixed_atoms ->
     ∅; bst_Γ3 range_le_under_ty true bst_keys_within y ⊢ₓ bst_inner y ⋮
       bst_RES true bst_keys_within y) ->
  ∅; Emp ⊢ₓ bst_gen_program_anf ⋮ bst_gen_must_ty.
Proof.
  intros Hbody. unfold bst_gen_must_ty.
  apply bst_outer; [reflexivity | exact range_le_under_open |
    exact range_le_under_wf | exact bst_gen_obl_persist_emp | exact Hbody].
Qed.

Lemma bst_gen_anf_paper_outer :
  (forall y, y ∉ bst_fixed_atoms ->
     ∅; bst_Γ3 range_strict_paper_ty true bst_keys_exact y ⊢ₓ bst_inner y ⋮
       bst_RES true bst_keys_exact y) ->
  ∅; Emp ⊢ₓ bst_gen_program_anf ⋮ bst_gen_paper_ty.
Proof.
  intros Hbody. unfold bst_gen_paper_ty.
  apply bst_outer; [reflexivity | exact range_strict_paper_open |
    exact range_strict_paper_wf | exact bst_gen_obl_persist_emp | exact Hbody].
Qed.

(** ** The generator call [range (one, r)] in the else-branch (Fig. 7, l.5) *)

(** [g] is the partial application [range one].  Its type mentions the
    let-bound [one]; since [one = 1] in every environment (precise constant
    type), [g]'s values also inhabit the closed type with [1] substituted
    for [one] (fibres over [one] are the whole capability).  *)
Lemma bst_gen_obl_g_close y b g :
  bst_ctx_sub_sem ({[g]}) (bst_Γone y b ,, (g ∷ bst_Tg)) (g ∷ bst_Tg_closed).
Proof.
  (* Semantic: [one ∷ {ν = 1} ⊓ [ν = 1]] makes every environment map [one]
     to [1]; the qualifiers of [bst_Tg] and [bst_Tg_closed] then agree on
     every environment, and the fibre over [one] is the whole capability,
     so the denotations of [g ∷ bst_Tg] and [g ∷ bst_Tg_closed] coincide
     after projecting away [one]. *)
Admitted.

(** In the false branch of [r <= 0] every environment has [r >= 1]. *)
Lemma bst_gen_obl_r_pos y b g :
  bst_ctx_sub_sem ({[r]}) (bst_Γone y b ,, (g ∷ bst_Tg)) (r ∷ bst_r_pos_ty).
Proof.
  (* Semantic: [isz ∷ {ν = (r <= 0)} ⊓ [..] ⊓ {ν = false} ⊓ [ν = false]]
     forces [r <= 0 = false], i.e. [1 <= r], in every environment; the
     projection of the capability on [r] therefore satisfies the demonic
     (row-wise) qualifier [1 <= ν]. *)
Admitted.

Lemma bst_range_call_typing y b :
  y ∉ bst_fixed_atoms -> b ∉ bst_fixed_atoms ∪ {[y]} ->
  ∅; bst_Γone y b ⊢ₓ range_arg @@ (one_x, r) ⋮ bst_τrp.
Proof.
  intros Hy Hb. unfold bst_fixed_atoms in *.
  bst_split_notin Hy. bst_split_notin Hb.
  unfold call2_tm, tapp_tm.
  refine (EXT_Let ∅ (bst_Γone y b) bst_Tg bst_τrp
    (case_app range_arg one_x) (tapp (vbvar 0) (value_shift 0 (avar r)))
    ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
     {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
     {[right_tree]} ∪ {[y]} ∪ {[b]}) _ _ _).
  - bst_wf_with bst_basic.
  - eapply (bst_appfun _ O[ ℕ ] bst_range_tail (avar range_arg) one_x bst_Tg).
    + bst_open_norm.
    + bst_wf_with bst_basic.
    + rewrite (bst_fv_closed_ty_at 1 bst_range_tail) by bst_ty_wf.
      rewrite (bst_fv_closed_ty O[ ℕ ]) by bst_ty_wf.
      cbn [fv_value avar]. bst_notin_set.
    + eapply (bst_sub _ _ bst_Rp).
      * bst_wf_with bst_basic.
      * bst_ty_wf.
      * reflexivity.
      * apply bst_gen_obl_persist_elim.
      * apply bst_var_proj; [bst_wf_with bst_basic | bst_comma_binds | bst_ty_wf |
          bst_lookup].
    + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
  - intros g Hg. bst_split_notin Hg.
    change ((tapp (vbvar 0) (value_shift 0 (avar r))) ^^ g) with
      (case_app (avar g) (avar r)).
    eapply (bst_appfun _ bst_r_pos_ty
      (precise_ty TNat (q_nat3 (vnat 1) ν (vbvar 1) (fun x v y => x <= v <= y)))
      (avar g) r bst_τrp).
    + bst_open_norm.
    + bst_wf_with bst_basic.
    + rewrite (bst_fv_closed_ty bst_r_pos_ty) by bst_ty_wf.
      rewrite (bst_fv_closed_ty_at 1
        (precise_ty TNat (q_nat3 (vnat 1) ν (vbvar 1) (fun x v y => x <= v <= y))))
        by bst_ty_wf.
      cbn [fv_value avar]. bst_notin_set.
    + apply bst_var_closed; [bst_wf_with bst_basic | bst_ty_wf | bst_lookup | ].
      apply bst_gen_obl_g_close.
    + apply bst_var_closed; [bst_wf_with bst_basic | bst_ty_wf | bst_lookup | ].
      apply bst_gen_obl_r_pos.
Qed.

(** ** Facts about the concrete range type *)

Lemma bst_Rp_wf d D : wf_context_ty_at d D bst_Rp.
Proof. bst_ty_wf. Qed.

Lemma bst_Rp_erase : erase_ty bst_Rp = (ℕ →ᵦ ℕ →ᵦ ℕ).
Proof. reflexivity. Qed.

Lemma bst_Rp_open k x : cty_open k x bst_Rp = bst_Rp.
Proof.
  apply (cty_open_above_lc_fresh 0).
  - lia.
  - apply (wf_context_ty_at_lc 0 ∅). apply bst_Rp_wf.
  - rewrite (bst_fv_closed_ty bst_Rp (bst_Rp_wf 0 ∅)). set_solver.
Qed.

Lemma bst_appfun_fresh (x : atom) v1 τx τ d1 d2 Dx D :
  x ∉ fv_value v1 ->
  wf_context_ty_at d1 Dx τx -> wf_context_ty_at d2 D τ ->
  x ∉ Dx -> x ∉ D ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ.
Proof.
  intros H1 H2 H3 H4 H5.
  pose proof (wf_context_ty_at_fv_subset _ _ _ H2).
  pose proof (wf_context_ty_at_fv_subset _ _ _ H3).
  set_solver.
Qed.

(** ** Variables at dependent types: T-VarComma + T-CtxSub (round 2)

    Round 1 (finding F2) had to assume a missing rule [ext_var_ctx_rule].
    The extended system now has [EXT_VarComma]
    ([Γ ,, x ∷ τ ⊢ ret x ⋮ τ], [τ] may mention [Γ]); together with
    T-CtxSub dropping the bindings to the right of [x] (a comma-spine
    prefix, [bst_ctx_sub_prefix], proved) this types every variable of the
    derivation at its own binding type.  No hypothesis is left. *)

Inductive comma_prefix (P : ctx) : ctx -> Prop :=
  | cp_refl : comma_prefix P P
  | cp_step Γ B : comma_prefix P Γ -> comma_prefix P (Γ ,, B).

Lemma comma_prefix_lookup P Γ a :
  comma_prefix P Γ -> a ∈ dom (erase_ctx P) ->
  erase_ctx Γ !! a = erase_ctx P !! a.
Proof.
  induction 1 as [ | Γ B Hp IH]; intros Ha; [reflexivity | ].
  cbn [erase_ctx]. pose proof (IH Ha) as E.
  apply elem_of_dom in Ha as [T HT].
  rewrite HT in E |- *. apply lookup_union_Some_l. exact E.
Qed.

Lemma comma_prefix_models P Γ (m : WfWorld) :
  comma_prefix P Γ -> m ⊨ ctx_denote_under ∅ Γ -> m ⊨ ctx_denote_under ∅ P.
Proof.
  induction 1 as [ | Γ B Hp IH]; intros Hm; [exact Hm | ].
  apply IH. eapply ctx_denote_under_comma_left. exact Hm.
Qed.

(** [Γ ≤_X P] for a comma-spine prefix [P] of [Γ]. *)
Lemma bst_ctx_sub_prefix X P Γ :
  comma_prefix P Γ -> wf_ctx_under ∅ Γ -> wf_ctx_under ∅ P ->
  X ⊆ dom (erase_ctx P) ->
  ctx_sub_under ∅ X Γ P.
Proof.
  intros Hp HΓ HP HX.
  split; [exact HΓ | split; [exact HP | split]].
  - intros a Ha. apply comma_prefix_lookup; [exact Hp | set_solver].
  - intros m Hm. exists m. split; [apply res_restrict_le | ].
    exact (comma_prefix_models P Γ m Hp Hm).
Qed.

Lemma bst_dom_erase_comma_bind P x τ :
  x ∈ dom (erase_ctx (P ,, (x ∷ τ))).
Proof.
  cbn [erase_ctx]. apply elem_of_dom.
  destruct (erase_ctx P !! x) as [T| ] eqn:E.
  - exists T. apply lookup_union_Some_l. exact E.
  - exists (erase_ty τ). apply lookup_union_Some_raw. right. split; [exact E | ].
    apply map_lookup_singleton.
Qed.

(** The paper's T-Var under the basic context [Σ,⌊Γ⌋]: a variable at its
    own (possibly dependent) binding type, anywhere on the comma spine. *)
Lemma bst_var_at Γ P x τ :
  comma_prefix (P ,, (x ∷ τ)) Γ ->
  ∅; P ,, (x ∷ τ) ⊢wf ret (avar x) ⋮ τ ->
  ∅; Γ ⊢wf ret (avar x) ⋮ τ ->
  ∅; Γ ⊢ₓ ret (avar x) ⋮ τ.
Proof.
  intros Hp Hwf1 Hwf.
  eapply EXT_CtxSub; [exact Hwf | apply EXT_VarComma; exact Hwf1 | ].
  apply bst_ctx_sub_prefix; [exact Hp | exact (proj1 Hwf) | exact (proj1 Hwf1) | ].
  pose proof (wf_context_ty_at_fv_subset _ _ _ (proj1 (proj2 Hwf1))) as Hfv.
  pose proof (bst_dom_erase_comma_bind P x τ) as Hx.
  unfold Ret, avar. cbn [fv_tm fv_value]. set_solver.
Qed.

Ltac bst_prefix :=
  bst_unfold_ctxs;
  repeat first [ exact (cp_refl _) | apply cp_step ].

Ltac bst_var_dep :=
  eapply bst_var_at;
  [ bst_prefix | bst_wf_with bst_basic | bst_wf_with bst_basic ].

(** [left_size = rp - 1 < r]: every environment of [bst_Γnlo] has
    [1 <= rp <= r] (precise range result) and [1 <= r]. *)
Lemma bst_gen_obl_left_size_dec y b :
  bst_sub_sem (bst_Γnlo y b)
    (binop_precise_ty bop_minus (vfvar rp) (vnat 1)) bst_lt_r_ty.
Proof.
  (* Semantic: the source type pins every result of the term to [rp - 1]
     in each environment; [rp ∷ {1 ≤ ν ≤ r} ⊓ [..]] gives [1 ≤ rp ≤ r], so
     [rp - 1 < r]; [O[ℕ]] is trivial and the demonic [ν ≺ r] (measure on
     [nat] is the identity) is row-wise, hence holds in every [r]-fibre. *)
Admitted.

(** [right_size = r - rp < r] for [1 <= rp] and [1 <= r]. *)
Lemma bst_gen_obl_right_size_dec y b :
  bst_sub_sem (bst_Γleft y b)
    (binop_precise_ty bop_minus (vfvar r) (vfvar rp)) bst_lt_r_ty.
Proof.
  (* Semantic: as above with [r - rp < r] since [1 ≤ rp] and [1 ≤ r]. *)
Admitted.

Section CallTyping.

  Lemma bst_left_call_typing y b :
    y ∉ bst_fixed_atoms -> b ∉ bst_fixed_atoms ∪ {[y]} ->
    ∅; bst_Γnlo y b ⊢ₓ rec @@@ (left_size, y, range_arg) ⋮ bst_τleft y.
  Proof.
    intros Hy Hb. unfold bst_fixed_atoms in *.
    bst_split_notin Hy. bst_split_notin Hb.
    unfold call3_tm, tapp_tm at 1.
    refine (EXT_Let ∅ (bst_Γnlo y b) (bst_T2 left_size y) (bst_τleft y)
      (call2_tm rec left_size y) (tapp (vbvar 0) (value_shift 0 (avar range_arg)))
      ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
       {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
       {[right_tree]} ∪ {[y]} ∪ {[b]}) _ _ _).
    - bst_wf_with bst_basic.
    - unfold call2_tm, tapp_tm.
      refine (EXT_Let ∅ (bst_Γnlo y b) (bst_T1 left_size) (bst_T2 left_size y)
        (case_app rec left_size) (tapp (vbvar 0) (value_shift 0 (avar y)))
        ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
         {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
         {[right_tree]} ∪ {[y]} ∪ {[b]}) _ _ _).
      + bst_wf_with bst_basic.
      + eapply (bst_appfun _ bst_lt_r_ty (bst_body_ty bst_Rp false bst_P)
          (avar rec) left_size (bst_T1 left_size)).
        * unfold bst_T1. apply bst_body_open; auto using bst_Rp_erase, bst_Rp_open, bst_Rp_wf.
        * bst_wf_with bst_basic.
        * apply (bst_appfun_fresh _ _ _ _ 0 1 ({[r]}) ∅).
          -- cbn. bst_notin_set.
          -- bst_ty_wf.
          -- apply bst_body_ty_wf; auto using bst_Rp_erase, bst_Rp_open, bst_Rp_wf.
          -- bst_notin_set.
          -- bst_notin_set.
        * bst_var_dep.
        * eapply (bst_sub _ _ (binop_precise_ty bop_minus (vfvar rp) (vnat 1))).
          -- bst_wf_with bst_basic.
          -- bst_ctx_ty_wf.
          -- reflexivity.
          -- apply bst_gen_obl_left_size_dec.
          -- bst_var_dep.
      + intros g1 Hg1. bst_split_notin Hg1.
        change ((tapp (vbvar 0) (value_shift 0 (avar y))) ^^ g1) with
          (case_app (avar g1) (avar y)).
        eapply (bst_appfun _ O[ ℕ ]
          (bst_Rp → bst_res_ty false (q_tree_spec (vfvar left_size) (vbvar 2) ν bst_P))
          (avar g1) y (bst_T2 left_size y)).
        * unfold bst_T2.
          apply bst_res_open;
            first [exact bst_Rp_erase | exact bst_Rp_open | exact bst_Rp_wf | bst_neq].
        * bst_wf_with bst_basic.
        * apply (bst_appfun_fresh _ _ _ _ 0 1 ∅ ({[left_size]})).
          -- cbn. bst_notin_set.
          -- bst_ty_wf.
          -- bst_ty_wf.
          -- bst_notin_set.
          -- bst_notin_set.
        * bst_var_dep.
        * apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
    - intros g2 Hg2. bst_split_notin Hg2.
      change ((tapp (vbvar 0) (value_shift 0 (avar range_arg))) ^^ g2) with
        (case_app (avar g2) (avar range_arg)).
      eapply (bst_appfun _ bst_Rp
        (bst_res_ty false (q_tree_spec (vfvar left_size) (vfvar y) ν bst_P))
        (avar g2) range_arg (bst_τleft y)).
      + bst_open_norm.
      + bst_wf_with bst_basic.
      + apply (bst_appfun_fresh _ _ _ _ 0 0 ∅ ({[left_size]} ∪ {[y]})).
        * cbn. bst_notin_set.
        * apply bst_Rp_wf.
        * bst_ty_wf.
        * bst_notin_set.
        * bst_notin_set.
      + bst_var_dep.
      + apply bst_var_proj; [bst_wf_with bst_basic | bst_comma_binds | apply bst_Rp_wf |
          bst_lookup].
  Qed.

  Lemma bst_right_call_typing y b :
    y ∉ bst_fixed_atoms -> b ∉ bst_fixed_atoms ∪ {[y]} ->
    ∅; bst_Γleft y b ⊢ₓ rec @@@ (right_size, new_lo, range_arg) ⋮ bst_τright.
  Proof.
    intros Hy Hb. unfold bst_fixed_atoms in *.
    bst_split_notin Hy. bst_split_notin Hb.
    unfold call3_tm, tapp_tm at 1.
    refine (EXT_Let ∅ (bst_Γleft y b) (bst_T2 right_size new_lo) bst_τright
      (call2_tm rec right_size new_lo) (tapp (vbvar 0) (value_shift 0 (avar range_arg)))
      ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
       {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
       {[right_tree]} ∪ {[y]} ∪ {[b]}) _ _ _).
    - bst_wf_with bst_basic.
    - unfold call2_tm, tapp_tm.
      refine (EXT_Let ∅ (bst_Γleft y b) (bst_T1 right_size) (bst_T2 right_size new_lo)
        (case_app rec right_size) (tapp (vbvar 0) (value_shift 0 (avar new_lo)))
        ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
         {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
         {[right_tree]} ∪ {[y]} ∪ {[b]}) _ _ _).
      + bst_wf_with bst_basic.
      + eapply (bst_appfun _ bst_lt_r_ty (bst_body_ty bst_Rp false bst_P)
          (avar rec) right_size (bst_T1 right_size)).
        * unfold bst_T1. apply bst_body_open; auto using bst_Rp_erase, bst_Rp_open, bst_Rp_wf.
        * bst_wf_with bst_basic.
        * apply (bst_appfun_fresh _ _ _ _ 0 1 ({[r]}) ∅).
          -- cbn. bst_notin_set.
          -- bst_ty_wf.
          -- apply bst_body_ty_wf; auto using bst_Rp_erase, bst_Rp_open, bst_Rp_wf.
          -- bst_notin_set.
          -- bst_notin_set.
        * bst_var_dep.
        * eapply (bst_sub _ _ (binop_precise_ty bop_minus (vfvar r) (vfvar rp))).
          -- bst_wf_with bst_basic.
          -- bst_ctx_ty_wf.
          -- reflexivity.
          -- apply bst_gen_obl_right_size_dec.
          -- bst_var_dep.
      + intros g1 Hg1. bst_split_notin Hg1.
        change ((tapp (vbvar 0) (value_shift 0 (avar new_lo))) ^^ g1) with
          (case_app (avar g1) (avar new_lo)).
        eapply (bst_appfun _ O[ ℕ ]
          (bst_Rp → bst_res_ty false (q_tree_spec (vfvar right_size) (vbvar 2) ν bst_P))
          (avar g1) new_lo (bst_T2 right_size new_lo)).
        * unfold bst_T2.
          apply bst_res_open;
            first [exact bst_Rp_erase | exact bst_Rp_open | exact bst_Rp_wf | bst_neq].
        * bst_wf_with bst_basic.
        * apply (bst_appfun_fresh _ _ _ _ 0 1 ∅ ({[right_size]})).
          -- cbn. bst_notin_set.
          -- bst_ty_wf.
          -- bst_ty_wf.
          -- bst_notin_set.
          -- bst_notin_set.
        * bst_var_dep.
        * apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
    - intros g2 Hg2. bst_split_notin Hg2.
      change ((tapp (vbvar 0) (value_shift 0 (avar range_arg))) ^^ g2) with
        (case_app (avar g2) (avar range_arg)).
      eapply (bst_appfun _ bst_Rp
        (bst_res_ty false (q_tree_spec (vfvar right_size) (vfvar new_lo) ν bst_P))
        (avar g2) range_arg bst_τright).
      + bst_open_norm.
      + bst_wf_with bst_basic.
      + apply (bst_appfun_fresh _ _ _ _ 0 0 ∅ ({[right_size]} ∪ {[new_lo]})).
        * cbn. bst_notin_set.
        * apply bst_Rp_wf.
        * bst_ty_wf.
        * bst_notin_set.
        * bst_notin_set.
      + bst_var_dep.
      + apply bst_var_proj; [bst_wf_with bst_basic | bst_comma_binds | apply bst_Rp_wf |
          bst_lookup].
  Qed.
End CallTyping.

(** ** The false branch of [r <= 0] (may/safety reading) *)

(** The Node case (Fig. 7, l.8): with [1 <= rp <= r],
    [left ∈ BST(keys ⊆ (lo, lo+rp-1])] and
    [right ∈ BST(keys ⊆ (lo+rp, lo+r])] in every environment,
    [Node (lo+rp) left right] is a BST whose keys lie in [(lo, lo+r]]. *)
Lemma bst_gen_obl_node_spec y b :
  bst_sub_sem (bst_Γright y b)
    (tree_node_precise_ty (vfvar new_lo) (vfvar left_tree) (vfvar right_tree))
    (bst_RES false bst_P y).
Proof.
  (* Semantic (row-wise, hence valid for the demonic reading):
     in every environment of [bst_Γright y b] we have
       rp ∈ [1, r]  (precise result of [range one r] with [one = 1]),
       left_size = rp - 1, right_size = r - rp, new_lo = y + rp,
       bst_keys_within left_size y left_tree,
       bst_keys_within right_size new_lo right_tree;
     the source type pins the result to [Node new_lo left_tree right_tree].
     Then every key [k] of [left_tree] has [y < k <= y + rp - 1 < new_lo],
     every key of [right_tree] has [new_lo < k <= y + r], and
     [y < new_lo <= y + r]; so the node is a BST with keys in (y, y + r].
     The target is demonic ([FOver] of the exact atom fibred over [r, y]),
     i.e. a property of each environment separately, so it follows. *)
Admitted.

Section ElseBranch.

  Lemma bst_else_body_typing y b :
    y ∉ bst_fixed_atoms -> b ∉ bst_fixed_atoms ∪ {[y]} ->
    ∅; bst_Γbf y b ⊢ₓ bst_else_body y ⋮ bst_RES false bst_P y.
  Proof.
    intros Hy Hb.
    pose proof (bst_range_call_typing y b Hy Hb) as Hrange.
    pose proof (bst_left_call_typing y b Hy Hb) as Hleft.
    pose proof (bst_right_call_typing y b Hy Hb) as Hright.
    unfold bst_fixed_atoms in *.
    bst_split_notin Hy. bst_split_notin Hb.
    unfold bst_else_body.
    eapply (EXT_LetNamed ∅ _ one_x (const_precise_ty (cnat 1)));
      [bst_wf_with bst_basic |
       apply bst_const_exact; [bst_wf_with bst_basic | bst_ty_wf] | ].
    unfold bst_rp_k.
    eapply (EXT_LetNamed ∅ _ rp bst_τrp); [bst_wf_with bst_basic | exact Hrange | ].
    unfold bst_ls_k.
    eapply (EXT_LetNamed ∅ _ left_size (binop_precise_ty bop_minus (vfvar rp) (vnat 1)));
      [bst_wf_with bst_basic | apply EXT_BinOp; bst_wf_with bst_basic | ].
    unfold bst_rs_k.
    eapply (EXT_LetNamed ∅ _ right_size (binop_precise_ty bop_minus (vfvar r) (vfvar rp)));
      [bst_wf_with bst_basic | apply EXT_BinOp; bst_wf_with bst_basic | ].
    unfold bst_nlo_k.
    eapply (EXT_LetNamed ∅ _ new_lo (binop_precise_ty bop_plus (vfvar y) (vfvar rp)));
      [bst_wf_with bst_basic | apply EXT_BinOp; bst_wf_with bst_basic | ].
    unfold bst_left_k.
    eapply (EXT_LetNamed ∅ _ left_tree (bst_τleft y));
      [bst_wf_with bst_basic | exact Hleft | ].
    unfold bst_right_k.
    eapply (EXT_LetNamed ∅ _ right_tree bst_τright);
      [bst_wf_with bst_basic | exact Hright | ].
    unfold bst_node_k.
    clear Hrange Hleft Hright.
    eapply (bst_sub _ _
      (tree_node_precise_ty (vfvar new_lo) (vfvar left_tree) (vfvar right_tree))).
    - bst_wf_with bst_basic.
    - bst_ctx_ty_wf.
    - reflexivity.
    - apply bst_gen_obl_node_spec.
    - apply EXT_TreeNode.
      + bst_wf_with bst_basic.
      + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
      + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
      + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
  Qed.
End ElseBranch.

Lemma bst_else_body_lc y :
  y ∉ bst_fixed_atoms -> lc_tm (bst_else_body y).
Proof.
  intros Hy. unfold bst_fixed_atoms in *. bst_split_notin Hy.
  apply (typing_tm_lc
    (<[isz := TBase TBool]> (<[range_arg := (ℕ →ᵦ ℕ →ᵦ ℕ)]> (bst_env3 y)))
    _ (TBase TTree)).
  bst_basic.
Qed.

(** boolGen produces both booleans in every capability (precise type of
    [boolGen ·₁ false], fibred over no variable), so the capability of
    [bst_Γb y b] splits into its [b = true] and [b = false] parts. *)
Lemma bst_gen_obl_nondet_split y b X :
  bst_ctx_sub_sem X (bst_Γb y b) (bst_Γbt y b ⊕ bst_Γbf y b).
Proof.
  (* Semantic: given [m ⊨ ⟦bst_Γb y b⟧], let [m1]/[m2] be the sub-worlds of
     [m] (same domain) whose environments map [b] to [true]/[false].  The
     angelic half [[𝔹 | prim_step boolGen false ν]] of [b]'s precise type has
     no free variable besides [ν], so [m] contains both values: [m1], [m2]
     are non-empty and [m = m1 + m2].  Each part satisfies
     [b ∷ bool_precise_ty true/false] and still satisfies [bst_Γf y]: all of
     its bindings are (i) demonic base types (row-wise, closed under
     sub-worlds), (ii) the persistent [range] (its projection stays the same
     singleton), (iii) precise types whose qualifier is a function of their
     free variables ([isz = (r <= 0)], fibred over [r]: every surviving
     fibre keeps its unique value), or (iv) the arrow [rec : RECTY] whose
     result is demonic (row-wise in the extended worlds).  For (iv) in
     detail: an argument extension [F] of a part [m_i] is lifted to [m] by
     giving the rows of the other part (whose [(rec, r)]-projections may be
     missing from [m_i]) the argument [a = 0], which is valid because
     [r ≥ 1] in every row of [bst_Γf]; [rec ∷ RECTY] on [m] then yields the
     demonic result on the lifted world, and filtering back to [m_i]
     preserves it (a demonic, row-wise property).  Taking [m' = m]
     (⊒ [m|X]) gives the required witness. *)
Admitted.

Section ElseNondet.

  Lemma bst_else_branch_typing y :
    y ∉ bst_fixed_atoms ->
    ∅; bst_Γf y ⊢ₓ ret leaf_value ⊕ₙ bst_else_body y ⋮ bst_RES false bst_P y.
  Proof.
    intros Hy.
    pose proof (bst_else_body_lc y Hy) as Hlc.
    pose proof (bst_else_body_typing y) as Hbody.
    pose proof Hy as Hy'.
    unfold bst_fixed_atoms in Hy'. bst_split_notin Hy'.
    unfold nondet_tm.
    refine (EXT_Let ∅ (bst_Γf y) bst_τbg (bst_RES false bst_P y)
      (tprim op_boolGen (vbool false))
      (tmatch (vbvar 0) (tm_shift 0 (ret leaf_value)) (tm_shift 0 (bst_else_body y)))
      (bst_fixed_atoms ∪ {[y]}) _ _ _).
    - clear Hbody. bst_wf_with bst_basic.
    - apply EXT_AppOpValue. clear Hbody. bst_wf_with bst_basic.
    - intros b Hb.
      specialize (Hbody b Hy Hb).
      change ((tmatch (vbvar 0) (tm_shift 0 (ret leaf_value))
                 (tm_shift 0 (bst_else_body y))) ^^ b) with
        (tmatch (vfvar b) (open_tm 0 (vfvar b) (tm_shift 0 (ret leaf_value)))
           (open_tm 0 (vfvar b) (tm_shift 0 (bst_else_body y)))).
      rewrite !open_tm_shift0_lc by (exact Hlc || (constructor; constructor)).
      unfold bst_fixed_atoms in Hb. bst_split_notin Hb.
      eapply (bst_sub _ _ (bst_RES false bst_P y ⊕ bst_RES false bst_P y)).
      + clear Hbody. bst_wf_with bst_basic.
      + clear Hbody. bst_ctx_ty_wf.
      + reflexivity.
      + unfold bst_RES, bst_res_ty. apply bst_gen_obl_sum_over_merge.
      + eapply (EXT_CtxSub ∅ _ (bst_Γbt y b ⊕ bst_Γbf y b)).
        * clear Hbody. bst_wf_with bst_basic.
        * eapply (EXT_MatchBoth ∅ (bst_Γbt y b) (bst_Γbf y b) b).
          -- clear Hbody. bst_wf_with bst_basic.
          -- clear Hbody. apply bst_var_proj;
               [bst_wf_with bst_basic | bst_comma_binds | bst_ty_wf | bst_lookup].
          -- clear Hbody. apply bst_var_proj;
               [bst_wf_with bst_basic | bst_comma_binds | bst_ty_wf | bst_lookup].
          -- clear Hbody. apply bst_const_typing.
             ++ bst_ctx_wf.
             ++ bst_wf_with bst_basic.
             ++ bst_ty_wf.
             ++ reflexivity.
             ++ unfold bst_RES, bst_res_ty, bst_P.
                apply bst_gen_obl_leaf_spec; bst_lookup.
          -- exact Hbody.
        * clear Hbody. apply bst_ctx_sub_intro.
          -- bst_ctx_wf.
          -- bst_ctx_wf.
          -- assert (E : erase_ctx (bst_Γf y ,, (b ∷ bst_τbg)) =
                         erase_ctx (bst_Γbt y b ⊕ bst_Γbf y b)) by bst_erase_eq.
             intros a _. rewrite E. reflexivity.
          -- apply bst_gen_obl_nondet_split.
  Qed.
End ElseNondet.

(** ** The match on [isz = r <= 0] (round 2: T-CtxCase)

    Round 1 needed the (false) split [Γ4 ≤ Γt ⊕ Γf].  With [EXT_CtxCase]
    the match is typed by a three-way capability case split:
      every world of [Γ4] has either all [isz] true (→ [Γt],
      T-MatchTrueOnly) or some [isz] false (→ [Γsf]); a world of [Γsf]
      has either all [isz] false (→ [Γf], T-MatchFalseOnly) or is MIXED
      (→ [Γt ⊕ Γf], T-MatchBoth + merge).
    The first split ([bst_gen_obl_isz_case_split]) and the "all false"
    half of the second are sound.  The MIXED half ([bst_isz_mixed_case_hyp])
    is FALSE, and not because of the split: see finding F6 at the top of
    the file.  In a world with a row [r = 0] the recursive binder
    [rec : {ν ≺ r} → ...] is satisfied VACUOUSLY (no extension of the world
    can give the [r = 0] rows an argument [ν < 0]; fibre extensions must be
    total, [extA_rel_nonempty], and the demonic argument type is checked on
    every [r]-fibre).  So [rec] may be any closure there, and the [r > 0]
    rows of the very same world compute garbage.  The T-Fix body judgment
    [Γ3 ⊢ bst_inner y : τ] is therefore semantically false for every
    useful [τ] (may or must), and by soundness of the extended rules it is
    not derivable.  The mixed case is kept as an explicit hypothesis only to
    show that EVERY other step of the derivation goes through. *)

Definition bst_Γ4g (ang : bool) (y : atom) : ctx :=
  bst_Γ3 bst_Rp ang bst_P y ,, (isz ∷ bst_τisz).
Definition bst_Γtg (ang : bool) (y : atom) : ctx :=
  bst_Γ3 bst_Rp ang bst_P y ,, (isz ∷ (bst_τisz ⊓ bool_precise_ty true)).
Definition bst_Γfg (ang : bool) (y : atom) : ctx :=
  bst_Γ3 bst_Rp ang bst_P y ,, (isz ∷ (bst_τisz ⊓ bool_precise_ty false)).
(** "some environment has [isz = false]": angelic [[𝔹 | ν = false]]. *)
Definition bst_Γsfg (ang : bool) (y : atom) : ctx :=
  bst_Γ3 bst_Rp ang bst_P y ,, (isz ∷ (bst_τisz ⊓ [: TBool | bool_qual false])).

Ltac bst_unfold_ctxs ::=
  unfold bst_Γ4g, bst_Γtg, bst_Γfg, bst_Γsfg,
    bst_Γright, bst_Γleft, bst_Γnlo, bst_Γrs, bst_Γls, bst_Γrp, bst_Γone,
    bst_Γbf, bst_Γbt, bst_Γb, bst_Γf, bst_Γt, bst_Γ4, bst_Γ3, bst_Γrec in *.

Definition bst_ctx_case_sem (X : aset) (Γ Γa Γb : ctx) : Prop :=
  forall m, m ⊨ ctx_denote_under ∅ Γ ->
    exists m', res_restrict m X ⊑ m' /\
      (m' ⊨ ctx_denote_under ∅ Γa \/ m' ⊨ ctx_denote_under ∅ Γb).

Lemma bst_ctx_case_intro X Γ Γa Γb :
  wf_ctx_under ∅ Γ -> wf_ctx_under ∅ Γa -> wf_ctx_under ∅ Γb ->
  ty_env_agree_on X (erase_ctx Γ) (erase_ctx Γa) ->
  ty_env_agree_on X (erase_ctx Γ) (erase_ctx Γb) ->
  bst_ctx_case_sem X Γ Γa Γb ->
  ctx_case_under ∅ X Γ Γa Γb.
Proof.
  intros H1 H2 H3 H4 H5 H6. unfold ctx_case_under.
  repeat split; assumption.
Qed.

(** Every world of [Γ4] has all [isz] true or some [isz] false.  Informal
    argument: take [m' = m].  If every environment maps [isz] to [true]
    then [isz ∷ τisz ⊓ {ν = true} ⊓ [ν = true]] holds ([{ν = true}] is
    row-wise; [[ν = true]] has no free variable besides [ν] and only asks
    that [true] occurs, which holds as worlds are non-empty).  Otherwise
    some environment has [isz = false], which is exactly the angelic
    [[𝔹 | ν = false]] (again a global, unfibred requirement).  The prefix
    [Γ3] is untouched, so its conjunct is the same formula. *)
Lemma bst_gen_obl_isz_case_split ang y X :
  bst_ctx_case_sem X (bst_Γ4g ang y) (bst_Γtg ang y) (bst_Γsfg ang y).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** The MIXED case.  FALSE (finding F6): counterexample world with two
    environments [{r ↦ 0, rec ↦ g, y ↦ 0, range ↦ ρ, isz ↦ true}] and
    [{r ↦ 2, rec ↦ g, y ↦ 0, range ↦ ρ, isz ↦ false}], where
    [g = λa lo rg. Node 100 Leaf Leaf] and [ρ] is a precise [x..y] range
    generator.  It satisfies [Γsf]: [rec ∷ {ν≺r} → ...] holds vacuously
    because of the [r = 0] row.  Since [rec ∈ X] (the else branch calls
    it), every [m' ⊒ m|X] still contains [g] next to [r = 2]; its
    [isz = false] part, required by both [Γf] and the right summand of
    [Γt ⊕ Γf], would have to satisfy [rec ∷ {ν ≺ 2} → ...] on its own,
    and [g] does not (its result is not a BST with keys in (lo, lo+a]). *)
Definition bst_isz_mixed_case_hyp (ang : bool) : Prop :=
  forall y X,
    bst_ctx_case_sem X (bst_Γsfg ang y) (bst_Γtg ang y ⊕ bst_Γfg ang y) (bst_Γfg ang y).

Ltac bst_isz_var :=
  eapply EXT_Sub; [bst_wf_with bst_basic | bst_var_dep | ];
  apply extended_semantic_subtype_inter_right;
  unfold subtype_wf; split; [bst_ctx_wf | split; [ | split]];
  [bst_ctx_ty_wf | bst_ctx_ty_wf | reflexivity].

Ltac bst_case_intro :=
  apply bst_ctx_case_intro;
  [ bst_ctx_wf | bst_ctx_wf | bst_ctx_wf
  | intros ? _; bst_unfold_ctxs; unfold bst_Γ4g, bst_Γtg, bst_Γfg, bst_Γsfg;
    bst_unfold_ctxs; bst_unfold_tys;
    cbn [erase_ctx erase_ty bin_op_type prim_op_type base_ty_of_const];
    rewrite ?bst_res_ty_erase; reflexivity
  | intros ? _; bst_unfold_ctxs; unfold bst_Γ4g, bst_Γtg, bst_Γfg, bst_Γsfg;
    bst_unfold_ctxs; bst_unfold_tys;
    cbn [erase_ctx erase_ty bin_op_type prim_op_type base_ty_of_const];
    rewrite ?bst_res_ty_erase; reflexivity
  | ].

(** The match skeleton, generic in the reading ([ang]): the two branch
    typings, the merge of the two summands, and the (false) mixed case. *)
Lemma bst_inner_skeleton ang y :
  y ∉ bst_fixed_atoms ->
  (∅; bst_Γtg ang y ⊢ₓ ret leaf_value ⋮ bst_RES ang bst_P y) ->
  (∅; bst_Γfg ang y ⊢ₓ ret leaf_value ⊕ₙ bst_else_body y ⋮ bst_RES ang bst_P y) ->
  bst_sub_sem (bst_Γtg ang y ⊕ bst_Γfg ang y)
    (bst_RES ang bst_P y ⊕ bst_RES ang bst_P y) (bst_RES ang bst_P y) ->
  bst_isz_mixed_case_hyp ang ->
  ∅; bst_Γ3 bst_Rp ang bst_P y ⊢ₓ bst_inner y ⋮ bst_RES ang bst_P y.
Proof.
  intros Hy Hleaf Helse Hmerge Hmixed.
  unfold bst_fixed_atoms in Hy. bst_split_notin Hy.
  unfold bst_inner.
  eapply (EXT_LetNamed ∅ _ isz bst_τisz);
    [clear Hleaf Helse Hmerge Hmixed; bst_wf_with bst_basic |
     apply EXT_BinOp; clear Hleaf Helse Hmerge Hmixed; bst_wf_with bst_basic | ].
  change (bst_Γ3 bst_Rp ang bst_P y ,, (isz ∷ bst_τisz)) with (bst_Γ4g ang y).
  eapply (EXT_CtxCase ∅ _ (bst_Γtg ang y) (bst_Γsfg ang y)).
  - clear Hleaf Helse Hmerge Hmixed. unfold bst_Γ4g. bst_wf_with bst_basic.
  - (* all [isz] true *)
    eapply (EXT_MatchTrueOnly ∅ _ isz).
    + clear Hleaf Helse Hmerge Hmixed. unfold bst_Γtg. bst_wf_with bst_basic.
    + clear Hleaf Helse Hmerge Hmixed. unfold bst_Γtg. bst_isz_var.
    + exact Hleaf.
  - (* some [isz] false *)
    eapply (EXT_CtxCase ∅ _ (bst_Γtg ang y ⊕ bst_Γfg ang y) (bst_Γfg ang y)).
    + clear Hleaf Helse Hmerge Hmixed. unfold bst_Γsfg. bst_wf_with bst_basic.
    + (* mixed: T-MatchBoth and merge *)
      eapply (bst_sub _ _ (bst_RES ang bst_P y ⊕ bst_RES ang bst_P y)).
      * clear Hleaf Helse Hmerge Hmixed. unfold bst_Γtg, bst_Γfg. bst_wf_with bst_basic.
      * clear Hleaf Helse Hmerge Hmixed. unfold bst_Γtg, bst_Γfg. bst_ctx_ty_wf.
      * reflexivity.
      * exact Hmerge.
      * eapply (EXT_MatchBoth ∅ (bst_Γtg ang y) (bst_Γfg ang y) isz).
        -- clear Hleaf Helse Hmerge Hmixed. unfold bst_Γtg, bst_Γfg. bst_wf_with bst_basic.
        -- clear Hleaf Helse Hmerge Hmixed. unfold bst_Γtg. bst_isz_var.
        -- clear Hleaf Helse Hmerge Hmixed. unfold bst_Γfg. bst_isz_var.
        -- exact Hleaf.
        -- exact Helse.
    + (* all [isz] false *)
      eapply (EXT_MatchFalseOnly ∅ _ isz).
      * clear Hleaf Helse Hmerge Hmixed. unfold bst_Γfg. bst_wf_with bst_basic.
      * clear Hleaf Helse Hmerge Hmixed. unfold bst_Γfg. bst_isz_var.
      * exact Helse.
    + clear Hleaf Helse Hmerge. bst_case_intro. apply Hmixed.
  - clear Hleaf Helse Hmerge Hmixed. bst_case_intro. apply bst_gen_obl_isz_case_split.
Qed.

(** *** The may (safety) instance *)

Lemma bst_inner_may_typing_modulo_mixed y :
  bst_isz_mixed_case_hyp false ->
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γ3 bst_Rp false bst_P y ⊢ₓ bst_inner y ⋮ bst_RES false bst_P y.
Proof.
  intros Hmixed Hy.
  pose proof (bst_else_branch_typing y Hy) as Helse.
  pose proof Hy as Hy'. unfold bst_fixed_atoms in Hy'. bst_split_notin Hy'.
  apply bst_inner_skeleton; [exact Hy | | exact Helse | | exact Hmixed].
  - clear Helse. unfold bst_Γtg. apply bst_const_typing.
    + bst_ctx_wf.
    + bst_wf_with bst_basic.
    + bst_ty_wf.
    + reflexivity.
    + unfold bst_RES, bst_res_ty, bst_P.
      apply bst_gen_obl_leaf_spec; bst_lookup.
  - unfold bst_RES, bst_res_ty. apply bst_gen_obl_sum_over_merge.
Qed.

(** ** Main (conditional) theorem for the may/safety reading

    Everything is derived (Qed structure, named obligations) except the
    mixed case of the [r <= 0] test, which is FALSE (F6); hence this is a
    proof that the T-Fix body is blocked at exactly one step, not a typing.
    The fully derived fragments are [bst_else_branch_typing] (all worlds
    with [r ≥ 1]: the whole recursive case, including both recursive calls
    and [Leaf ⊕ ...]) and the [r = 0] / [r ≥ 1] halves of
    [bst_inner_skeleton]. *)
Theorem bst_gen_anf_may_typing_modulo :
  bst_isz_mixed_case_hyp false ->
  ∅; Emp ⊢ₓ bst_gen_program_anf ⋮ bst_gen_may_ty.
Proof.
  intros Hmixed.
  unfold bst_gen_may_ty.
  apply bst_outer.
  - exact bst_Rp_erase.
  - exact bst_Rp_open.
  - exact bst_Rp_wf.
  - exact bst_gen_obl_persist_emp.
  - intros y Hy. exact (bst_inner_may_typing_modulo_mixed y Hmixed Hy).
Qed.

(* ================================================================== *)
(** * Round 2: the must (coverage) reading                             *)
(* ================================================================== *)

(** ** (F7) The must type with an under-approximate range is FALSE

    Fig. 7 gives [range] only an angelic result [[x < ν < y]] (repaired:
    [[x ≤ ν ≤ y]]).  An under type only requires every value of [x..y] to
    be reachable; the generator may return MORE.  The extended semantics
    requires every typed term to be total ([expr_total_formula] in
    [ty_guard_formula]: all execution paths terminate), and so does the
    paper (p. 11).  Take [range_bad x y = range x y ⊕ ret (y + 1)]: it is
    a closed, total, persistent value and inhabits
    [□(x:{ℕ|⊤} → y:{ℕ|x≤ν} → [ℕ | x≤ν≤y])].  Then [bst_gen 1 lo range_bad]
    has an infinite execution: [r = 1 > 0], choose the [else] side of [⊕],
    [range_bad 1 1] returns [2], and the left call is
    [bst_gen (2 - 1) lo range_bad = bst_gen 1 lo range_bad] again.  So
    [bst_gen 1 lo range_bad] is not must-terminating, violates the totality
    guard of [[Tree | ...]], and [bst_gen] does not inhabit
    [bst_gen_must_ty].  ([bst_gen_paper_ty] is not affected: its strict
    range type is uninhabited, F1, so [range_bad] is not an argument of it.)
    The call graph is
    machine-checked below ([bst_bad_range_self_call]); with a range that is
    also demonically bounded ([{x ≤ ν ≤ y} ⊓ [x ≤ ν ≤ y]]) every call
    strictly decreases [r] ([bst_le_range_calls_decrease]).

    Corrected must target: [bst_gen_must_fixed_ty], i.e. Fig. 7 with the
    precise range [range_le_precise_ty] (the same parameter as the may
    type) and the "keys within (lo, lo+r]" reading. *)

Definition bst_gen_must_fixed_ty : context_ty :=
  bst_full_ty bst_Rp true bst_keys_within.

(** ** Qualifiers with extra (dummy) dependencies

    [q_..._d] has the same predicate as its counterpart but additionally
    lists dummy variables among its logic variables.  For an angelic type
    this makes coverage FINER: [[Tree | φ(ls, lo) ∧ (r, rp)]] requires every
    tree of [φ(ls, lo)] in every [(ls, lo, r, rp)]-fibre, not only in every
    [(ls, lo)]-fibre.  This is how the independence of the recursive calls
    (finding F4 of round 1) is recovered, see [bst_must_obl_rec_fine_left]. *)
Definition q_nat3d (a b c d : value) (P : nat -> nat -> nat -> Prop) : type_qualifier :=
  tqual (lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c ∪ lvar_value_keys d)
    (fun σ =>
       exists na nb nc,
         denote_lvar_value (lso_store σ) a = Some (vconst (cnat na)) /\
         denote_lvar_value (lso_store σ) b = Some (vconst (cnat nb)) /\
         denote_lvar_value (lso_store σ) c = Some (vconst (cnat nc)) /\
         P na nb nc).

Definition q_tree_spec_d2 (rv lov tv d1 d2 : value) (P : nat -> nat -> tree -> Prop)
    : type_qualifier :=
  tqual (lvar_value_keys rv ∪ lvar_value_keys lov ∪ lvar_value_keys tv ∪
         lvar_value_keys d1 ∪ lvar_value_keys d2)
    (fun σ =>
       exists nr nlo t,
         denote_lvar_value (lso_store σ) rv = Some (vconst (cnat nr)) /\
         denote_lvar_value (lso_store σ) lov = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) tv = Some (vconst (ctree t)) /\
         P nr nlo t).

Definition q_tree_spec_d4 (rv lov tv d1 d2 d3 d4 : value) (P : nat -> nat -> tree -> Prop)
    : type_qualifier :=
  tqual (lvar_value_keys rv ∪ lvar_value_keys lov ∪ lvar_value_keys tv ∪
         lvar_value_keys d1 ∪ lvar_value_keys d2 ∪ lvar_value_keys d3 ∪
         lvar_value_keys d4)
    (fun σ =>
       exists nr nlo t,
         denote_lvar_value (lso_store σ) rv = Some (vconst (cnat nr)) /\
         denote_lvar_value (lso_store σ) lov = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) tv = Some (vconst (ctree t)) /\
         P nr nlo t).

Lemma bst_q_nat3d_open k x a b c d P :
  simple_value a -> simple_value b -> simple_value c -> simple_value d ->
  LVFree x ∉ lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c ∪ lvar_value_keys d ->
  qual_open_atom k x (q_nat3d a b c d P) =
  q_nat3d (open_value k (vfvar x) a) (open_value k (vfvar x) b)
    (open_value k (vfvar x) c) (open_value k (vfvar x) d) P.
Proof.
  intros Ha Hb Hc Hd Hx. unfold q_nat3d.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - rewrite !bst_set_swap_union.
    rewrite !bst_keys_open_swap by (auto; set_solver). reflexivity.
  - intros s1 s2 Hs. unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !bst_denote_open_swap by (auto; set_solver).
    rewrite Hs. reflexivity.
Qed.

Lemma bst_q_tree_spec_d2_open k x a b c d1 d2 P :
  simple_value a -> simple_value b -> simple_value c ->
  simple_value d1 -> simple_value d2 ->
  LVFree x ∉ lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c ∪
    lvar_value_keys d1 ∪ lvar_value_keys d2 ->
  qual_open_atom k x (q_tree_spec_d2 a b c d1 d2 P) =
  q_tree_spec_d2 (open_value k (vfvar x) a) (open_value k (vfvar x) b)
    (open_value k (vfvar x) c) (open_value k (vfvar x) d1)
    (open_value k (vfvar x) d2) P.
Proof.
  intros Ha Hb Hc Hd1 Hd2 Hx. unfold q_tree_spec_d2.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - rewrite !bst_set_swap_union.
    rewrite !bst_keys_open_swap by (auto; set_solver). reflexivity.
  - intros s1 s2 Hs. unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !bst_denote_open_swap by (auto; set_solver).
    rewrite Hs. reflexivity.
Qed.

Lemma bst_q_tree_spec_d4_open k x a b c d1 d2 d3 d4 P :
  simple_value a -> simple_value b -> simple_value c ->
  simple_value d1 -> simple_value d2 -> simple_value d3 -> simple_value d4 ->
  LVFree x ∉ lvar_value_keys a ∪ lvar_value_keys b ∪ lvar_value_keys c ∪
    lvar_value_keys d1 ∪ lvar_value_keys d2 ∪ lvar_value_keys d3 ∪ lvar_value_keys d4 ->
  qual_open_atom k x (q_tree_spec_d4 a b c d1 d2 d3 d4 P) =
  q_tree_spec_d4 (open_value k (vfvar x) a) (open_value k (vfvar x) b)
    (open_value k (vfvar x) c) (open_value k (vfvar x) d1)
    (open_value k (vfvar x) d2) (open_value k (vfvar x) d3)
    (open_value k (vfvar x) d4) P.
Proof.
  intros Ha Hb Hc Hd1 Hd2 Hd3 Hd4 Hx. unfold q_tree_spec_d4.
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom].
  - rewrite !bst_set_swap_union.
    rewrite !bst_keys_open_swap by (auto; set_solver). reflexivity.
  - intros s1 s2 Hs. unfold lstore_on_open_back. cbn [lso_store storeAO_store].
    rewrite !bst_denote_open_swap by (auto; set_solver).
    rewrite Hs. reflexivity.
Qed.

(** ** Types and contexts of the must derivation (worlds with [r ≥ 1]) *)

Definition bst_node_cov (n m : nat) (t : tree) : Prop :=
  bst_keys_within n m t /\ t <> tr_leaf.
Definition bst_leaf_only (n m : nat) (t : tree) : Prop := t = tr_leaf.

Definition bst_τrp_m (lo_a : atom) : context_ty :=
  {: TNat | q_nat3 (vnat 1) ν (vfvar r) bst_le3 } ⊓
  [: TNat | q_nat3d (vnat 1) ν (vfvar r) (vfvar lo_a) bst_le3 ].

Definition bst_Tg_fine (lo_a : atom) : context_ty :=
  bst_r_pos_ty →
  ({: TNat | q_nat3 (vnat 1) ν (vbvar 1) bst_le3 } ⊓
   [: TNat | q_nat3d (vnat 1) ν (vbvar 1) (vfvar lo_a) bst_le3 ]).

Definition bst_body_d2 (d1 d2 : value) : context_ty :=
  O[ ℕ ] → bst_Rp → [: TTree | q_tree_spec_d2 (vbvar 3) (vbvar 2) ν d1 d2 bst_P ].
Definition bst_body_d4 (d1 d2 d3 d4 : value) : context_ty :=
  O[ ℕ ] → bst_Rp → [: TTree | q_tree_spec_d4 (vbvar 3) (vbvar 2) ν d1 d2 d3 d4 bst_P ].

Definition bst_RECTY_l : context_ty :=
  fix_rec_call_ty TNat r {: TNat | qual_top} (bst_body_d2 (vfvar r) (vfvar rp)).
Definition bst_RECTY_r (lo_a : atom) : context_ty :=
  fix_rec_call_ty TNat r {: TNat | qual_top}
    (bst_body_d4 (vfvar r) (vfvar lo_a) (vfvar rp) (vfvar left_tree)).

Definition bst_τleft_m (lo_a : atom) : context_ty :=
  [: TTree | q_tree_spec_d2 (vfvar left_size) (vfvar lo_a) ν (vfvar r) (vfvar rp) bst_P ].
Definition bst_τright_m (lo_a : atom) : context_ty :=
  [: TTree | q_tree_spec_d4 (vfvar right_size) (vfvar new_lo) ν
               (vfvar r) (vfvar lo_a) (vfvar rp) (vfvar left_tree) bst_P ].
Definition bst_τnode_m (lo_a : atom) : context_ty :=
  [: TTree | q_tree_spec (vfvar r) (vfvar lo_a) ν bst_node_cov ].

Definition bst_Γf_m (lo_a : atom) : ctx := bst_Γfg true lo_a.
Definition bst_Γone_m (lo_a : atom) : ctx :=
  bst_Γf_m lo_a ,, (one_x ∷ const_precise_ty (cnat 1)).
Definition bst_Γrp_m (lo_a : atom) : ctx := bst_Γone_m lo_a ,, (rp ∷ bst_τrp_m lo_a).
Definition bst_Γls_m (lo_a : atom) : ctx :=
  bst_Γrp_m lo_a ,, (left_size ∷ binop_precise_ty bop_minus (vfvar rp) (vnat 1)).
Definition bst_Γrs_m (lo_a : atom) : ctx :=
  bst_Γls_m lo_a ,, (right_size ∷ binop_precise_ty bop_minus (vfvar r) (vfvar rp)).
Definition bst_Γnlo_m (lo_a : atom) : ctx :=
  bst_Γrs_m lo_a ,, (new_lo ∷ binop_precise_ty bop_plus (vfvar lo_a) (vfvar rp)).
Definition bst_Γleft_m (lo_a : atom) : ctx :=
  bst_Γnlo_m lo_a ,, (left_tree ∷ bst_τleft_m lo_a).
Definition bst_Γright_m (lo_a : atom) : ctx :=
  bst_Γleft_m lo_a ,, (right_tree ∷ bst_τright_m lo_a).

Definition bst_T1L : context_ty :=
  O[ ℕ ] → bst_Rp →
    [: TTree | q_tree_spec_d2 (vfvar left_size) (vbvar 2) ν (vfvar r) (vfvar rp) bst_P ].
Definition bst_T2L (lo_a : atom) : context_ty :=
  bst_Rp →
    [: TTree | q_tree_spec_d2 (vfvar left_size) (vfvar lo_a) ν (vfvar r) (vfvar rp) bst_P ].
Definition bst_T1R (lo_a : atom) : context_ty :=
  O[ ℕ ] → bst_Rp →
    [: TTree | q_tree_spec_d4 (vfvar right_size) (vbvar 2) ν
                 (vfvar r) (vfvar lo_a) (vfvar rp) (vfvar left_tree) bst_P ].
Definition bst_T2R (lo_a : atom) : context_ty :=
  bst_Rp →
    [: TTree | q_tree_spec_d4 (vfvar right_size) (vfvar new_lo) ν
                 (vfvar r) (vfvar lo_a) (vfvar rp) (vfvar left_tree) bst_P ].

Ltac bst_unfold_ctxs ::=
  unfold bst_Γright_m, bst_Γleft_m, bst_Γnlo_m, bst_Γrs_m, bst_Γls_m, bst_Γrp_m,
    bst_Γone_m, bst_Γf_m,
    bst_Γ4g, bst_Γtg, bst_Γfg, bst_Γsfg,
    bst_Γright, bst_Γleft, bst_Γnlo, bst_Γrs, bst_Γls, bst_Γrp, bst_Γone,
    bst_Γbf, bst_Γbt, bst_Γb, bst_Γf, bst_Γt, bst_Γ4, bst_Γ3, bst_Γrec in *.

Ltac bst_unfold_tys ::=
  unfold bst_RECTY, bst_RECTY_l, bst_RECTY_r, bst_full_ty;
  unfold bst_body_ty, bst_body_d2, bst_body_d4;
  unfold bst_T1L, bst_T2L, bst_T1R, bst_T2R;
  unfold bst_τrp_m, bst_Tg_fine, bst_body_d2, bst_body_d4, bst_RECTY_l,
    bst_RECTY_r, bst_τleft_m, bst_τright_m, bst_τnode_m, bst_le3;
  unfold bst_range_tail, bst_Tg, bst_Tg_closed, bst_r_pos_ty,
    bst_lt_r_ty, bst_T1, bst_T2, bst_τleft, bst_τright, bst_τrp, bst_τbg,
    bst_τisz, bst_Rp, bst_P, bst_full_ty, bst_body_ty, bst_RES, bst_RECTY,
    range_le_precise_ty, range_le_inner_ty, range_le_under_ty,
    range_strict_paper_ty;
  unfold const_precise_ty, bool_precise_ty, binop_precise_ty,
    primop_precise_ty, tree_node_precise_ty, fix_rec_call_ty;
  unfold precise_ty, over_ty, under_ty, bst_res_ty;
  unfold binop_result_qual, primop_result_qual, tree_node_result_qual,
    bool_qual, mk_q_eq, mk_q_lt_base, q_nat2, q_nat3, q_tree_spec,
    q_nat3d, q_tree_spec_d2, q_tree_spec_d4,
    qual_top, ONat, OTree, OBool, vnu.

Ltac bst_open_norm ::=
  unfold bst_T1L, bst_T2L, bst_T1R, bst_T2R;
  unfold bst_τrp_m, bst_Tg_fine, bst_body_d2, bst_body_d4, bst_τleft_m,
    bst_τright_m, bst_τnode_m;
  unfold bst_range_tail, bst_Tg, bst_Tg_closed, bst_r_pos_ty, bst_lt_r_ty,
    bst_T1, bst_T2, bst_τleft, bst_τright, bst_τrp, bst_P, precise_ty, over_ty, under_ty;
  cbn [cty_open bst_res_ty];
  rewrite ?bst_Rp_open;
  rewrite ?bst_qual_top_open;
  rewrite ?bst_q_nat2_open, ?bst_q_nat3_open, ?bst_q_tree_spec_open,
    ?bst_q_nat3d_open, ?bst_q_tree_spec_d2_open, ?bst_q_tree_spec_d4_open
    by (cbn [simple_value lvar_value_keys];
        first [exact I | solve [bst_notin_set] | set_solver]);
  cbn [open_value];
  reflexivity.

(** *** Must-specific obligations of the generator call *)

(** In the false branch of [r <= 0] every environment has [r ≥ 1]
    (as [bst_gen_obl_r_pos]). *)
Lemma bst_must_obl_r_pos y g :
  bst_ctx_sub_sem ({[r]}) (bst_Γone_m y ,, (g ∷ bst_Tg)) (r ∷ bst_r_pos_ty).
Proof.
  (* Semantic: [isz ∷ {ν = (r <= 0)} ⊓ .. ⊓ {ν = false} ⊓ ..] forces
     [1 ≤ r] in every environment; the target is demonic (row-wise). *)
Admitted.

(** [g = range one] at the closed, FINER type [bst_Tg_fine]: [one] is
    replaced by [1] (as in [bst_gen_obl_g_close]) and the angelic result
    additionally depends on [lo] (dummy).  Informal argument: [one = 1] in
    every environment, so the qualifiers with [one] and with [1] agree
    row-wise.  For the dummy: the arrow denotation quantifies over every
    fibre extension [F] of the argument (input = the formula's free
    variables).  Given an extension [F'] for the finer type (inputs
    [{g, lo}]) and a fibre [(a0, lo0)] of the result, let [G] be the set of
    values of [g] in that fibre; build an extension [F] for the coarse type
    (inputs [{g, one}], which it can read since [ext_in F = formula_fv]
    contains [g]) giving [a0] to the rows whose [g ∈ G] and a value
    [≠ a0] to the others (any [a ≥ 1] is a valid argument).  The coarse
    type yields every [v ∈ [1, a0]] in the [a0]-fibre of [F], whose rows
    have [g ∈ G]; the results of [g a0] depend only on the values of [g] and
    [a0], so the same results occur in the [(a0, lo0)]-fibre of [F'].  The
    demonic half is unchanged (row-wise). *)
Lemma bst_must_obl_g_fine y g :
  bst_sub_sem (bst_Γone_m y ,, (g ∷ bst_Tg)) bst_Tg (bst_Tg_fine y).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

Lemma bst_must_range_call_typing y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γone_m y ⊢ₓ range_arg @@ (one_x, r) ⋮ bst_τrp_m y.
Proof.
  intros Hy. unfold bst_fixed_atoms in *.
  bst_split_notin Hy.
  unfold call2_tm, tapp_tm.
  refine (EXT_Let ∅ (bst_Γone_m y) bst_Tg (bst_τrp_m y)
    (case_app range_arg one_x) (tapp (vbvar 0) (value_shift 0 (avar r)))
    ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
     {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
     {[right_tree]} ∪ {[y]}) _ _ _).
  - bst_wf_with bst_basic.
  - eapply (bst_appfun _ O[ ℕ ] bst_range_tail (avar range_arg) one_x bst_Tg).
    + bst_open_norm.
    + bst_wf_with bst_basic.
    + rewrite (bst_fv_closed_ty_at 1 bst_range_tail) by bst_ty_wf.
      rewrite (bst_fv_closed_ty O[ ℕ ]) by bst_ty_wf.
      cbn [fv_value avar]. bst_notin_set.
    + eapply (bst_sub _ _ bst_Rp).
      * bst_wf_with bst_basic.
      * bst_ty_wf.
      * reflexivity.
      * apply bst_gen_obl_persist_elim.
      * apply bst_var_proj; [bst_wf_with bst_basic | bst_comma_binds | bst_ty_wf |
          bst_lookup].
    + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
  - intros g Hg. bst_split_notin Hg.
    change ((tapp (vbvar 0) (value_shift 0 (avar r))) ^^ g) with
      (case_app (avar g) (avar r)).
    eapply (bst_appfun _ bst_r_pos_ty
      ({: TNat | q_nat3 (vnat 1) ν (vbvar 1) bst_le3 } ⊓
       [: TNat | q_nat3d (vnat 1) ν (vbvar 1) (vfvar y) bst_le3 ])
      (avar g) r (bst_τrp_m y)).
    + bst_open_norm.
    + bst_wf_with bst_basic.
    + apply (bst_appfun_fresh _ _ _ _ 0 1 ∅ ({[y]})).
      * cbn. bst_notin_set.
      * bst_ty_wf.
      * bst_ty_wf.
      * bst_notin_set.
      * bst_notin_set.
    + eapply (bst_sub _ _ bst_Tg).
      * bst_wf_with bst_basic.
      * bst_ctx_ty_wf.
      * reflexivity.
      * apply bst_must_obl_g_fine.
      * bst_var_dep.
    + apply bst_var_closed; [bst_wf_with bst_basic | bst_ty_wf | bst_lookup | ].
      apply bst_must_obl_r_pos.
Qed.

(** *** Obligations of the recursive calls (must reading) *)

(** [left_size = rp - 1 < r] (as [bst_gen_obl_left_size_dec]; the demonic
    half of [bst_τrp_m] gives [1 ≤ rp ≤ r] in every environment). *)
Lemma bst_must_obl_left_size_dec y :
  bst_sub_sem (bst_Γnlo_m y)
    (binop_precise_ty bop_minus (vfvar rp) (vnat 1)) bst_lt_r_ty.
Proof.
  (* Semantic: row-wise [rp - 1 < r] from [1 ≤ rp ≤ r]. *)
Admitted.

Lemma bst_must_obl_right_size_dec y :
  bst_sub_sem (bst_Γleft_m y)
    (binop_precise_ty bop_minus (vfvar r) (vfvar rp)) bst_lt_r_ty.
Proof.
  (* Semantic: row-wise [r - rp < r] from [1 ≤ rp], [1 ≤ r]. *)
Admitted.

(** FINER coverage of the recursive call (resolves round-1 F4).
    [rec ∷ RECTY] promises, for every extension of the world by arguments
    [(a, lo', rg)], every BST of [(lo', lo'+a]] in every [(a, lo')]-fibre of
    the results.  The target adds the dummies [r, rp] to the angelic
    qualifier, i.e. coverage in every [(a, lo', r, rp)]-fibre.  Informal
    argument (isolation): all rows of the current world satisfy [r ≥ 1]
    (false branch), so every row admits a valid argument [a < r].  Let
    [F'] be an argument extension for the target and [R0] a fibre
    [(a0, lo0, r0, rp0)] of its result world; let [G] be the set of
    CLOSURES (values of [rec]) occurring in [R0].  Build an extension [F]
    for the source, respecting that each [FForall] level only reads the
    free variables of its body ([ext_in F = formula_fv], so the [lo]-level
    need not see [r]):
    - [a]-level (inputs include [rec] and [r], through [{ν < r}]): give
      [a0] to the rows with [a0 < r], and some valid [a < r] otherwise;
    - [lo]-level (inputs include [rec] and [a]): give [lo0] exactly to the
      rows with [rec ∈ G] and [a = a0], and [lo0 + 1] to all others;
    - [range]-level: the persistent (hence unique) range value [ρ0].
    The source gives every tree of [φ(a0, lo0)] in the [(a0, lo0)]-fibre of
    [F], and by construction that fibre only contains closures from [G].
    The results of [rec a0 lo0 ρ0] depend only on [(rec, a0, lo0, ρ0)], and
    every [f ∈ G] occurs in [R0] applied to the same arguments; the result
    rows of that application keep [(a0, lo0, r0, rp0)], so every tree also
    occurs in [R0].  (Round-2 audit: the earlier version keyed the [lo]-level
    on [(rec, r)], which that level may not be able to read; keying on the
    closure alone, as here, fixes this.)  The guard (totality, basic typing) is
    shared.  This holds although [rec] itself is not persistent: the
    arrow's quantification over ALL argument extensions already makes its
    reachability guarantee per closure value. *)
Lemma bst_must_obl_rec_fine_left y :
  bst_sub_sem (bst_Γnlo_m y) (bst_RECTY bst_Rp true bst_P) bst_RECTY_l.
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** As [bst_must_obl_rec_fine_left] with dummies [r, lo, rp, left]: in
    every [(rs, nlo, r, lo, rp, left)]-fibre all trees of [φ(rs, nlo)]. *)
Lemma bst_must_obl_rec_fine_right y :
  bst_sub_sem (bst_Γleft_m y) (bst_RECTY bst_Rp true bst_P) (bst_RECTY_r y).
Proof.
  (* Semantic: the isolation argument of [bst_must_obl_rec_fine_left]. *)
Admitted.

Ltac bst_open_norm_m := bst_open_norm.

Lemma bst_must_left_call_typing y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γnlo_m y ⊢ₓ rec @@@ (left_size, y, range_arg) ⋮ bst_τleft_m y.
Proof.
  intros Hy. unfold bst_fixed_atoms in *.
  bst_split_notin Hy.
  unfold call3_tm, tapp_tm at 1.
  refine (EXT_Let ∅ (bst_Γnlo_m y) (bst_T2L y) (bst_τleft_m y)
    (call2_tm rec left_size y) (tapp (vbvar 0) (value_shift 0 (avar range_arg)))
    ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
     {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
     {[right_tree]} ∪ {[y]}) _ _ _).
  - bst_wf_with bst_basic.
  - unfold call2_tm, tapp_tm.
    refine (EXT_Let ∅ (bst_Γnlo_m y) bst_T1L (bst_T2L y)
      (case_app rec left_size) (tapp (vbvar 0) (value_shift 0 (avar y)))
      ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
       {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
       {[right_tree]} ∪ {[y]}) _ _ _).
    + bst_wf_with bst_basic.
    + eapply (bst_appfun _ bst_lt_r_ty (bst_body_d2 (vfvar r) (vfvar rp))
        (avar rec) left_size bst_T1L).
      * bst_open_norm_m.
      * bst_wf_with bst_basic.
      * apply (bst_appfun_fresh _ _ _ _ 0 1 ({[r]}) ({[r]} ∪ {[rp]})).
        -- cbn. bst_notin_set.
        -- bst_ty_wf.
        -- bst_ty_wf.
        -- bst_notin_set.
        -- bst_notin_set.
      * eapply (bst_sub _ _ (bst_RECTY bst_Rp true bst_P)).
        -- bst_wf_with bst_basic.
        -- bst_ctx_ty_wf.
        -- reflexivity.
        -- apply bst_must_obl_rec_fine_left.
        -- bst_var_dep.
      * eapply (bst_sub _ _ (binop_precise_ty bop_minus (vfvar rp) (vnat 1))).
        -- bst_wf_with bst_basic.
        -- bst_ctx_ty_wf.
        -- reflexivity.
        -- apply bst_must_obl_left_size_dec.
        -- bst_var_dep.
    + intros g1 Hg1. bst_split_notin Hg1.
      change ((tapp (vbvar 0) (value_shift 0 (avar y))) ^^ g1) with
        (case_app (avar g1) (avar y)).
      eapply (bst_appfun _ O[ ℕ ]
        (bst_Rp → [: TTree | q_tree_spec_d2 (vfvar left_size) (vbvar 2) ν
                               (vfvar r) (vfvar rp) bst_P ])
        (avar g1) y (bst_T2L y)).
      * bst_open_norm_m.
      * bst_wf_with bst_basic.
      * apply (bst_appfun_fresh _ _ _ _ 0 1 ∅ ({[left_size]} ∪ {[r]} ∪ {[rp]})).
        -- cbn. bst_notin_set.
        -- bst_ty_wf.
        -- bst_ty_wf.
        -- bst_notin_set.
        -- bst_notin_set.
      * bst_var_dep.
      * apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
  - intros g2 Hg2. bst_split_notin Hg2.
    change ((tapp (vbvar 0) (value_shift 0 (avar range_arg))) ^^ g2) with
      (case_app (avar g2) (avar range_arg)).
    eapply (bst_appfun _ bst_Rp
      ([: TTree | q_tree_spec_d2 (vfvar left_size) (vfvar y) ν (vfvar r) (vfvar rp) bst_P ])
      (avar g2) range_arg (bst_τleft_m y)).
    + bst_open_norm_m.
    + bst_wf_with bst_basic.
    + apply (bst_appfun_fresh _ _ _ _ 0 0 ∅ ({[left_size]} ∪ {[y]} ∪ {[r]} ∪ {[rp]})).
      * cbn. bst_notin_set.
      * apply bst_Rp_wf.
      * bst_ty_wf.
      * bst_notin_set.
      * bst_notin_set.
    + bst_var_dep.
    + apply bst_var_proj; [bst_wf_with bst_basic | bst_comma_binds | apply bst_Rp_wf |
        bst_lookup].
Qed.

Lemma bst_must_right_call_typing y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γleft_m y ⊢ₓ rec @@@ (right_size, new_lo, range_arg) ⋮ bst_τright_m y.
Proof.
  intros Hy. unfold bst_fixed_atoms in *.
  bst_split_notin Hy.
  unfold call3_tm, tapp_tm at 1.
  refine (EXT_Let ∅ (bst_Γleft_m y) (bst_T2R y) (bst_τright_m y)
    (call2_tm rec right_size new_lo) (tapp (vbvar 0) (value_shift 0 (avar range_arg)))
    ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
     {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
     {[right_tree]} ∪ {[y]}) _ _ _).
  - bst_wf_with bst_basic.
  - unfold call2_tm, tapp_tm.
    refine (EXT_Let ∅ (bst_Γleft_m y) (bst_T1R y) (bst_T2R y)
      (case_app rec right_size) (tapp (vbvar 0) (value_shift 0 (avar new_lo)))
      ({[r]} ∪ {[rec]} ∪ {[lo]} ∪ {[range_arg]} ∪ {[isz]} ∪ {[one_x]} ∪ {[rp]} ∪
       {[left_size]} ∪ {[right_size]} ∪ {[new_lo]} ∪ {[left_tree]} ∪
       {[right_tree]} ∪ {[y]}) _ _ _).
    + bst_wf_with bst_basic.
    + eapply (bst_appfun _ bst_lt_r_ty
        (bst_body_d4 (vfvar r) (vfvar y) (vfvar rp) (vfvar left_tree))
        (avar rec) right_size (bst_T1R y)).
      * bst_open_norm_m.
      * bst_wf_with bst_basic.
      * apply (bst_appfun_fresh _ _ _ _ 0 1 ({[r]})
          ({[r]} ∪ {[y]} ∪ {[rp]} ∪ {[left_tree]})).
        -- cbn. bst_notin_set.
        -- bst_ty_wf.
        -- bst_ty_wf.
        -- bst_notin_set.
        -- bst_notin_set.
      * eapply (bst_sub _ _ (bst_RECTY bst_Rp true bst_P)).
        -- bst_wf_with bst_basic.
        -- bst_ctx_ty_wf.
        -- reflexivity.
        -- apply bst_must_obl_rec_fine_right.
        -- bst_var_dep.
      * eapply (bst_sub _ _ (binop_precise_ty bop_minus (vfvar r) (vfvar rp))).
        -- bst_wf_with bst_basic.
        -- bst_ctx_ty_wf.
        -- reflexivity.
        -- apply bst_must_obl_right_size_dec.
        -- bst_var_dep.
    + intros g1 Hg1. bst_split_notin Hg1.
      change ((tapp (vbvar 0) (value_shift 0 (avar new_lo))) ^^ g1) with
        (case_app (avar g1) (avar new_lo)).
      eapply (bst_appfun _ O[ ℕ ]
        (bst_Rp → [: TTree | q_tree_spec_d4 (vfvar right_size) (vbvar 2) ν
                    (vfvar r) (vfvar y) (vfvar rp) (vfvar left_tree) bst_P ])
        (avar g1) new_lo (bst_T2R y)).
      * bst_open_norm_m.
      * bst_wf_with bst_basic.
      * apply (bst_appfun_fresh _ _ _ _ 0 1 ∅
          ({[right_size]} ∪ {[r]} ∪ {[y]} ∪ {[rp]} ∪ {[left_tree]})).
        -- cbn. bst_notin_set.
        -- bst_ty_wf.
        -- bst_ty_wf.
        -- bst_notin_set.
        -- bst_notin_set.
      * bst_var_dep.
      * apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
  - intros g2 Hg2. bst_split_notin Hg2.
    change ((tapp (vbvar 0) (value_shift 0 (avar range_arg))) ^^ g2) with
      (case_app (avar g2) (avar range_arg)).
    eapply (bst_appfun _ bst_Rp
      ([: TTree | q_tree_spec_d4 (vfvar right_size) (vfvar new_lo) ν
                  (vfvar r) (vfvar y) (vfvar rp) (vfvar left_tree) bst_P ])
      (avar g2) range_arg (bst_τright_m y)).
    + bst_open_norm_m.
    + bst_wf_with bst_basic.
    + apply (bst_appfun_fresh _ _ _ _ 0 0 ∅
        ({[right_size]} ∪ {[new_lo]} ∪ {[r]} ∪ {[y]} ∪ {[rp]} ∪ {[left_tree]})).
      * cbn. bst_notin_set.
      * apply bst_Rp_wf.
      * bst_ty_wf.
      * bst_notin_set.
      * bst_notin_set.
    + bst_var_dep.
    + apply bst_var_proj; [bst_wf_with bst_basic | bst_comma_binds | apply bst_Rp_wf |
        bst_lookup].
Qed.

(** Node coverage (Fig. 7, l.8), must reading.  Informal argument: fix an
    [(r, lo)]-fibre of the result world and a tree [t = Node k L R] with
    [bst_node_cov r lo t]; then [k = lo + k'] with [1 ≤ k' ≤ r],
    [bst_keys_within (k'-1) lo L] and [bst_keys_within (r-k') k R].
    (i) [rp ∷ [1 ≤ ν ≤ r ∧ (lo)]] (fibre [(r, lo)]) gives a row of the fibre
    with [rp = k'];  its [ls = k' - 1], [rs = r - k'], [nlo = lo + k']
    (demonic halves of the precise binop types, row-wise);
    (ii) [left ∷ [φ(ls, lo) ∧ (r, rp)]] (fibre [(ls, lo, r, rp)], which is
    non-empty by (i)) gives a row with additionally [left = L];
    (iii) [right ∷ [φ(rs, nlo) ∧ (r, lo, rp, left)]] (fibre
    [(rs, nlo, r, lo, rp, left)], non-empty by (ii)) gives a row with
    additionally [right = R].  The demonic half of the source type pins the
    result of that row to [Node nlo left right = t].  So [t] is reachable
    in the [(r, lo)]-fibre; the guard is the source's guard. *)
Lemma bst_must_obl_node_cov y :
  bst_sub_sem (bst_Γright_m y)
    (tree_node_precise_ty (vfvar new_lo) (vfvar left_tree) (vfvar right_tree))
    (bst_τnode_m y).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

Lemma bst_must_else_body_typing y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γf_m y ⊢ₓ bst_else_body y ⋮ bst_τnode_m y.
Proof.
  intros Hy.
  pose proof (bst_must_range_call_typing y Hy) as Hrange.
  pose proof (bst_must_left_call_typing y Hy) as Hleft.
  pose proof (bst_must_right_call_typing y Hy) as Hright.
  unfold bst_fixed_atoms in *.
  bst_split_notin Hy.
  unfold bst_else_body.
  eapply (EXT_LetNamed ∅ _ one_x (const_precise_ty (cnat 1)));
    [bst_wf_with bst_basic |
     apply bst_const_exact; [bst_wf_with bst_basic | bst_ty_wf] | ].
  unfold bst_rp_k.
  eapply (EXT_LetNamed ∅ _ rp (bst_τrp_m y)); [bst_wf_with bst_basic | exact Hrange | ].
  unfold bst_ls_k.
  eapply (EXT_LetNamed ∅ _ left_size (binop_precise_ty bop_minus (vfvar rp) (vnat 1)));
    [bst_wf_with bst_basic | apply EXT_BinOp; bst_wf_with bst_basic | ].
  unfold bst_rs_k.
  eapply (EXT_LetNamed ∅ _ right_size (binop_precise_ty bop_minus (vfvar r) (vfvar rp)));
    [bst_wf_with bst_basic | apply EXT_BinOp; bst_wf_with bst_basic | ].
  unfold bst_nlo_k.
  eapply (EXT_LetNamed ∅ _ new_lo (binop_precise_ty bop_plus (vfvar y) (vfvar rp)));
    [bst_wf_with bst_basic | apply EXT_BinOp; bst_wf_with bst_basic | ].
  unfold bst_left_k.
  eapply (EXT_LetNamed ∅ _ left_tree (bst_τleft_m y));
    [bst_wf_with bst_basic | exact Hleft | ].
  unfold bst_right_k.
  eapply (EXT_LetNamed ∅ _ right_tree (bst_τright_m y));
    [bst_wf_with bst_basic | exact Hright | ].
  unfold bst_node_k.
  clear Hrange Hleft Hright.
  eapply (bst_sub _ _
    (tree_node_precise_ty (vfvar new_lo) (vfvar left_tree) (vfvar right_tree))).
  - bst_wf_with bst_basic.
  - bst_ctx_ty_wf.
  - reflexivity.
  - apply bst_must_obl_node_cov.
  - apply EXT_TreeNode.
    + bst_wf_with bst_basic.
    + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
    + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
    + apply bst_var_top; [bst_wf_with bst_basic | bst_lookup].
Qed.

(** *** [Leaf ⊕ ...] with an independent [boolGen] (T-LetI) *)

(** Branch types of the [⊕]: they mention the choice [b] demonically so
    that the merge can locate the two summands (see
    [bst_must_obl_leaf_node_merge]). *)
Definition bst_τt (b lo_a : atom) : context_ty :=
  {: TTree | mk_q_eq (vfvar b) (vconst (cbool true)) } ⊓
  [: TTree | q_tree_spec (vfvar r) (vfvar lo_a) ν bst_leaf_only ].
Definition bst_τf (b lo_a : atom) : context_ty :=
  {: TTree | mk_q_eq (vfvar b) (vconst (cbool false)) } ⊓ bst_τnode_m lo_a.

Ltac bst_unfold_tys ::=
  unfold bst_τt, bst_τf;
  unfold bst_RECTY, bst_RECTY_l, bst_RECTY_r, bst_full_ty;
  unfold bst_body_ty, bst_body_d2, bst_body_d4;
  unfold bst_T1L, bst_T2L, bst_T1R, bst_T2R;
  unfold bst_τrp_m, bst_Tg_fine, bst_body_d2, bst_body_d4, bst_RECTY_l,
    bst_RECTY_r, bst_τleft_m, bst_τright_m, bst_τnode_m, bst_le3;
  unfold bst_range_tail, bst_Tg, bst_Tg_closed, bst_r_pos_ty,
    bst_lt_r_ty, bst_T1, bst_T2, bst_τleft, bst_τright, bst_τrp, bst_τbg,
    bst_τisz, bst_Rp, bst_P, bst_full_ty, bst_body_ty, bst_RES, bst_RECTY,
    range_le_precise_ty, range_le_inner_ty, range_le_under_ty,
    range_strict_paper_ty;
  unfold const_precise_ty, bool_precise_ty, binop_precise_ty,
    primop_precise_ty, tree_node_precise_ty, fix_rec_call_ty;
  unfold precise_ty, over_ty, under_ty, bst_res_ty;
  unfold binop_result_qual, primop_result_qual, tree_node_result_qual,
    bool_qual, mk_q_eq, mk_q_lt_base, q_nat2, q_nat3, q_tree_spec,
    q_nat3d, q_tree_spec_d2, q_tree_spec_d4,
    qual_top, ONat, OTree, OBool, vnu.

Lemma bst_erase_star Γ x τ :
  x ∉ ctx_dom Γ ->
  erase_ctx (Γ ∗ (x ∷ τ)) = <[x := erase_ty τ]> (erase_ctx Γ).
Proof.
  intros Hx. change (erase_ctx (Γ ∗ (x ∷ τ))) with (erase_ctx (Γ ,, (x ∷ τ))).
  apply bst_erase_comma. exact Hx.
Qed.

Lemma bst_erase_emp_star Γ : erase_ctx (Emp ∗ Γ) = erase_ctx Γ.
Proof. cbn [erase_ctx]. apply (left_id_L ∅ union). Qed.

Ltac bst_erase_norm ::=
  rewrite ?bst_RES_erase;
  rewrite ?bst_erase_sum, ?bst_erase_emp_star;
  repeat (rewrite bst_erase_star by bst_dom_fresh);
  repeat (rewrite bst_erase_comma by bst_dom_fresh);
  unfold bst_RECTY;
  cbn [erase_ctx erase_ty fix_rec_call_ty over_ty under_ty precise_ty];
  rewrite ?bst_res_ty_erase, ?bst_RES_erase, ?bst_body_ty_Rp_erase.

Lemma bst_store_restrict_empty_ty (X : aset) :
  storeA_restrict (∅ : gmap atom ty) X = ∅.
Proof. apply map_eq. intros k. apply storeA_restrict_lookup_none_l. reflexivity. Qed.

(** [Γ1 ∗ Γ2 ≤ Γ1] and [Γ1 ∗ Γ2 ≤ Γ2] (affine projections of [∗];
    proofs as in Section4Extension). *)
Lemma bst_ctx_sub_star_drop_right X Γ1 Γ2 :
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
  - intros m Hm. exists m. split; [apply res_restrict_le| ].
    cbn [ctx_denote_under] in Hm. rewrite !bst_store_restrict_empty_ty in Hm.
    apply res_models_and_iff in Hm as [_ Hm].
    apply res_models_star_iff in Hm as [m1 [m2 [Hc [Hle [Hm1 _]]]]].
    eapply res_models_kripke; [ | exact Hm1].
    etransitivity; [apply res_product_le_l | exact Hle].
Qed.

Lemma bst_ctx_sub_star_drop_left X Γ1 Γ2 :
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
  - intros m Hm. exists m. split; [apply res_restrict_le| ].
    cbn [ctx_denote_under] in Hm. rewrite !bst_store_restrict_empty_ty in Hm.
    apply res_models_and_iff in Hm as [_ Hm].
    apply res_models_star_iff in Hm as [m1 [m2 [Hc [Hle [_ Hm2]]]]].
    eapply res_models_kripke; [ | exact Hm2].
    etransitivity; [apply res_product_le_r | exact Hle].
Qed.

(** T-Frame-style use of T-CtxSub: drop the right factor of a [∗]. *)
Lemma bst_star_frame Γ B e τ :
  ∅; Γ ∗ B ⊢wf e ⋮ τ ->
  ∅; Γ ⊢wf e ⋮ τ ->
  ∅; Γ ⊢ₓ e ⋮ τ ->
  ∅; Γ ∗ B ⊢ₓ e ⋮ τ.
Proof.
  intros Hwf Hwf1 He.
  eapply EXT_CtxSub; [exact Hwf | exact He | ].
  apply bst_ctx_sub_star_drop_right; [exact (proj1 Hwf) | ].
  pose proof (context_typing_wf_fv_tm_subset _ _ _ _ Hwf1).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf1).
  rewrite <- (context_typing_wf_erase_dom _ _ _ _ Hwf1). set_solver.
Qed.

(** A variable bound by the right factor of a [∗] at a closed type. *)
Lemma bst_star_var Γ x τ :
  ∅; Γ ∗ (x ∷ τ) ⊢wf ret (avar x) ⋮ τ ->
  ∅; x ∷ τ ⊢wf ret (avar x) ⋮ τ ->
  ∅; Γ ∗ (x ∷ τ) ⊢ₓ ret (avar x) ⋮ τ.
Proof.
  intros Hwf Hwf1.
  eapply EXT_CtxSub; [exact Hwf | apply EXT_Var; exact Hwf1 | ].
  apply bst_ctx_sub_star_drop_left; [exact (proj1 Hwf) | ].
  pose proof (context_typing_wf_fv_tm_subset _ _ _ _ Hwf1).
  pose proof (context_typing_wf_fv_cty_subset_erase_dom _ _ _ _ Hwf1).
  rewrite <- (context_typing_wf_erase_dom _ _ _ _ Hwf1). set_solver.
Qed.

(** [Γ ≤ Emp ∗ Γ] (T-LetI with an empty left factor): a world [m] is the
    product of [m|∅] (the unit world, a model of [Emp]) with itself.
    Proved. *)
Lemma bst_product_restrict_empty (m : WfWorld (V := value)) Hc :
  res_product (res_restrict m ∅) m Hc = m.
Proof.
  apply wfworld_ext. apply world_ext.
  - rewrite res_product_dom, res_restrict_dom. set_solver.
  - intros σ. cbn. split.
    + intros [σ1 [σ2 [[σ0 [_ <-]] [Hσ2 [_ ->]]]]].
      rewrite storeA_restrict_empty_set. rewrite (left_id_L ∅ union). exact Hσ2.
    + intros Hσ. exists ∅, σ. split; [ | split; [exact Hσ | split]].
      * exists σ. split; [exact Hσ | apply storeA_restrict_empty_set].
      * apply storeA_disj_dom_compat. rewrite dom_empty_L. set_solver.
      * rewrite (left_id_L ∅ union). reflexivity.
Qed.

Lemma bst_ctx_sub_emp_star X Γ :
  bst_ctx_sub_sem X Γ (Emp ∗ Γ).
Proof.
  intros m Hm.
  assert (Hc : world_compat (res_restrict m ∅) m).
  { intros σ1 σ2 [σ0 [_ <-]] _. apply storeA_disj_dom_compat.
    rewrite storeA_restrict_empty_set, dom_empty_L. set_solver. }
  assert (Hemp : res_restrict m ∅ ⊨ ctx_denote_under ∅ Emp).
  { cbn [ctx_denote_under].
    assert (E : store_restrict (∅ : gmap atom ty) (ctx_fv Emp) ∪ erase_ctx Emp = ∅)
      by reflexivity.
    rewrite E.
    apply res_models_and_intro_from_models.
    - change (atom_env_to_lty_env (∅ : gmap atom ty)) with (∅ : lty_env).
      apply basic_world_formula_empty.
    - apply res_models_true. }
  pose proof (ctx_denote_under_star_intro_product ∅ Emp Γ (res_restrict m ∅) m Hc
    I Hemp Hm) as H.
  rewrite bst_product_restrict_empty in H.
  exists m. split; [apply res_restrict_le | exact H].
Qed.

Lemma bst_must_obl_emp_star X y :
  bst_ctx_sub_sem X (bst_Γf_m y) (Emp ∗ bst_Γf_m y).
Proof. apply bst_ctx_sub_emp_star. Qed.

(** [boolGen] bound independently ([∗]) splits by its value.  Informal
    argument: let [m ⊨ Γf ∗ b ∷ τbg]: [m1 × m2 ⊑ m] with [m1 ⊨ Γf],
    [m2 ⊨ b ∷ τbg]; the angelic half of [τbg] (no free variable besides
    [ν]) makes [m2] contain [b = true] and [b = false], its demonic half
    makes [m2 ⊆ {true, false}].  Then [m1 × {b=true}] and [m1 × {b=false}]
    are non-empty worlds of the two summands and their sum is [m1 × m2]; the
    witness is [m' = m] restricted to their common domain extended back
    (Kripke monotonicity of [∗]). *)
Lemma bst_must_obl_star_split X y b :
  bst_ctx_sub_sem X (bst_Γf_m y ∗ (b ∷ bst_τbg))
    ((bst_Γf_m y ∗ (b ∷ bool_precise_ty true)) ⊕
     (bst_Γf_m y ∗ (b ∷ bool_precise_ty false))).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** [Leaf] in the [b = true] part.  Informal argument: every result is
    [Leaf] (row-wise), so [Leaf] is reachable in every [(r, lo)]-fibre;
    [b = true] in every environment (precise type of [b]). *)
Lemma bst_must_obl_leaf_t y b :
  bst_sub_sem (bst_Γf_m y ∗ (b ∷ bool_precise_ty true))
    (const_precise_ty (ctree tr_leaf)) (bst_τt b y).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

(** Adding the (row-wise) fact [b = false] of the context. *)
Lemma bst_must_obl_else_f y b :
  bst_sub_sem (bst_Γf_m y ∗ (b ∷ bool_precise_ty false))
    (bst_τnode_m y) (bst_τf b y).
Proof.
  (* Semantic: [{b = false}] holds in every environment of the context,
     hence of every result extension; the second conjunct is the source. *)
Admitted.

(** The merge of the two [⊕] summands.  Informal argument: let
    [m ⊨ Γf ∗ b ∷ τbg] and [m_x] the result extension of [e];
    [m1 + m2 ⊑ m_x] with [m1 ⊨ τt], [m2 ⊨ τf].  By the product structure of
    [m] (see [bst_must_obl_star_split]) every [(r, lo)]-fibre of [m_x]
    contains rows with [b = true] and rows with [b = false]; the demonic
    halves put the former in [m1] and the latter in [m2].  So every fibre
    of [m_x] is a fibre of [m1] (where [Leaf] is reachable) and of [m2]
    (where every non-leaf BST within [(lo, lo+r]] is reachable): every tree
    of [bst_keys_within r lo] is reachable.  (With [,] instead of [∗] this
    is false: a world may pair the fibre [(r, lo)] with [b = false] only.) *)
Lemma bst_must_obl_leaf_node_merge y b :
  bst_sub_sem (bst_Γf_m y ∗ (b ∷ bst_τbg))
    (bst_τt b y ⊕ bst_τf b y) (bst_RES true bst_P y).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

Lemma bst_must_else_branch_typing y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γf_m y ⊢ₓ ret leaf_value ⊕ₙ bst_else_body y ⋮ bst_RES true bst_P y.
Proof.
  intros Hy.
  pose proof (bst_else_body_lc y Hy) as Hlc.
  pose proof (bst_must_else_body_typing y Hy) as Hbody.
  pose proof Hy as Hy'.
  unfold bst_fixed_atoms in Hy'. bst_split_notin Hy'.
  unfold nondet_tm.
  eapply (EXT_CtxSub ∅ _ (Emp ∗ bst_Γf_m y)).
  - clear Hbody. bst_wf_with bst_basic.
  - refine (EXT_LetD ∅ Emp (bst_Γf_m y) bst_τbg (bst_RES true bst_P y)
      (tprim op_boolGen (vbool false))
      (tmatch (vbvar 0) (tm_shift 0 (ret leaf_value)) (tm_shift 0 (bst_else_body y)))
      (bst_fixed_atoms ∪ {[y]}) _ _ _).
    + clear Hbody. bst_wf_with bst_basic.
    + apply EXT_AppOpValue. clear Hbody. bst_wf_with bst_basic.
    + intros b Hb.
      change ((tmatch (vbvar 0) (tm_shift 0 (ret leaf_value))
                 (tm_shift 0 (bst_else_body y))) ^^ b) with
        (tmatch (vfvar b) (open_tm 0 (vfvar b) (tm_shift 0 (ret leaf_value)))
           (open_tm 0 (vfvar b) (tm_shift 0 (bst_else_body y)))).
      rewrite !open_tm_shift0_lc by (exact Hlc || (constructor; constructor)).
      unfold bst_fixed_atoms in Hb. bst_split_notin Hb.
      eapply (bst_sub _ _ (bst_τt b y ⊕ bst_τf b y)).
      * clear Hbody. bst_wf_with bst_basic.
      * clear Hbody. bst_ctx_ty_wf.
      * reflexivity.
      * apply bst_must_obl_leaf_node_merge.
      * eapply (EXT_CtxSub ∅ _ ((bst_Γf_m y ∗ (b ∷ bool_precise_ty true)) ⊕
                                (bst_Γf_m y ∗ (b ∷ bool_precise_ty false)))).
        -- clear Hbody. bst_wf_with bst_basic.
        -- eapply (EXT_MatchBoth ∅ (bst_Γf_m y ∗ (b ∷ bool_precise_ty true))
                     (bst_Γf_m y ∗ (b ∷ bool_precise_ty false)) b).
           ++ clear Hbody. bst_wf_with bst_basic.
           ++ clear Hbody. apply bst_star_var; bst_wf_with bst_basic.
           ++ clear Hbody. apply bst_star_var; bst_wf_with bst_basic.
           ++ clear Hbody. apply bst_const_typing.
              ** bst_ctx_wf.
              ** bst_wf_with bst_basic.
              ** bst_ty_wf.
              ** reflexivity.
              ** apply bst_must_obl_leaf_t.
           ++ eapply (bst_sub _ _ (bst_τnode_m y)).
              ** clear Hbody. bst_wf_with bst_basic.
              ** clear Hbody. bst_ctx_ty_wf.
              ** reflexivity.
              ** apply bst_must_obl_else_f.
              ** apply bst_star_frame; [clear Hbody; bst_wf_with bst_basic |
                   clear Hbody; bst_wf_with bst_basic | exact Hbody].
        -- clear Hbody. apply bst_ctx_sub_intro.
           ++ bst_ctx_wf.
           ++ bst_ctx_wf.
           ++ intros a _. bst_unfold_ctxs. bst_erase_norm. reflexivity.
           ++ apply bst_must_obl_star_split.
  - clear Hbody. apply bst_ctx_sub_intro.
    + bst_ctx_wf.
    + bst_ctx_wf.
    + intros a _. bst_unfold_ctxs. bst_erase_norm. reflexivity.
    + apply bst_must_obl_emp_star.
Qed.

(** *** The [r <= 0] match and the whole program, must reading *)

(** All [isz] true means [r = 0] in every environment, where
    [bst_keys_within 0 lo t] holds only for [t = Leaf]: [Leaf] (the only
    result) covers every [(r, lo)]-fibre. *)
Lemma bst_must_obl_leaf_zero y :
  bst_sub_sem (bst_Γtg true y)
    (const_precise_ty (ctree tr_leaf)) (bst_RES true bst_P y).
Proof.
  (* Semantic: see the comment above ([isz = (r ≤? 0) = true] row-wise
     gives [r = 0]; a BST with all keys in (lo, lo] has no key). *)
Admitted.

(** Merging two summands of the SAME angelic type.  Informal argument:
    [m1 + m2 ⊑ m_x]; every row of [m_x] (on the common domain) lies in [m1]
    or [m2], so every fibre of [m_x] over [FV(q)∖ν] is a fibre of [m1] or
    of [m2] (possibly of both: then it is the union, a superset); in either
    case every value satisfying [q] is reachable in it. *)
Lemma bst_gen_obl_sum_under_merge Γ b q :
  bst_sub_sem Γ (([: b | q]) ⊕ ([: b | q])) ([: b | q]).
Proof.
  (* Semantic: see the comment above. *)
Admitted.

Lemma bst_inner_must_typing_modulo_mixed y :
  bst_isz_mixed_case_hyp true ->
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γ3 bst_Rp true bst_P y ⊢ₓ bst_inner y ⋮ bst_RES true bst_P y.
Proof.
  intros Hmixed Hy.
  pose proof (bst_must_else_branch_typing y Hy) as Helse.
  pose proof Hy as Hy'. unfold bst_fixed_atoms in Hy'. bst_split_notin Hy'.
  apply bst_inner_skeleton; [exact Hy | | exact Helse | | exact Hmixed].
  - clear Helse. apply bst_const_typing.
    + bst_ctx_wf.
    + bst_wf_with bst_basic.
    + bst_ty_wf.
    + reflexivity.
    + apply bst_must_obl_leaf_zero.
  - unfold bst_RES, bst_res_ty. apply bst_gen_obl_sum_under_merge.
Qed.

(** ** Main (conditional) theorem for the must/coverage reading

    Target: Fig. 7 with the range repaired (off by one, F1) and given its
    demonic bound (totality, F7), keys within (lo, lo+r].  Everything is
    derived except the mixed case of the [r <= 0] test, which is FALSE for
    the same reason as in the may reading (F6). *)
Theorem bst_gen_anf_must_fixed_typing_modulo :
  bst_isz_mixed_case_hyp true ->
  ∅; Emp ⊢ₓ bst_gen_program_anf ⋮ bst_gen_must_fixed_ty.
Proof.
  intros Hmixed.
  unfold bst_gen_must_fixed_ty.
  apply bst_outer.
  - exact bst_Rp_erase.
  - exact bst_Rp_open.
  - exact bst_Rp_wf.
  - exact bst_gen_obl_persist_emp.
  - intros y Hy. exact (bst_inner_must_typing_modulo_mixed y Hmixed Hy).
Qed.

(* ================================================================== *)
(** * Round 2 (fix): the verbatim Fig. 7 type is VACUOUSLY TRUE         *)
(* ================================================================== *)

(** ** (F1, corrected) The strict range parameter type is uninhabited

    Round 1 and the first round-2 report classified [bst_gen_paper_ty] as
    semantically false (off-by-one, [bst_counterexample_unreachable]).  That
    was wrong in this semantics (and in the paper's, Def. 4.7 and §4.3: atoms
    are EXACT and capabilities are non-empty).  The parameter type

      [range_strict_paper_ty = □(x:{ℕ|⊤} → y:{ℕ | x < ν} → [ℕ | x < ν < y])]

    has NO inhabitant: whatever closure [ρ] is bound to [range], extend the
    world with the constant columns [x ↦ 1], [y ↦ 2].  This is a total
    argument extension that satisfies [{ℕ|⊤}] and, per [x]-fibre, the
    demonic [{x < ν}] ([2 > 1]).  The arrow then requires
    [ρ 1 2 : [ℕ | 1 < ν < 2]].  Its denotation fixes [x = 1, y = 2] on the
    unique [(x, y)]-fibre ([FFibVars]) and demands [FUnder (FAtom q)] for
    [q = {ν | 1 < ν < 2} = ∅], i.e. a NON-EMPTY sub-world whose projection on
    [ν] is exactly empty ([res_models_under_FAtom_inv] gives a store
    satisfying [q]), which is impossible.  If [ρ 1 2] has no result at all,
    the totality guard [expr_total_formula] fails instead (basic typing and
    termination give at least one result, so the result extension of
    [ext_result_world_exists] exists).  Persistence ([□]) does not help: it
    only restricts the world to a singleton first.  Hence [range ∷ R] has no
    model, the [range] arrow of [bst_gen_paper_ty] holds VACUOUSLY, and
    [bst_gen_paper_ty] is vacuously TRUE of [bst_gen] (and of any total
    closure of the right basic type).  It is also DERIVABLE: the T-Fix body
    context [bst_Γ3 range_strict_paper_ty ...] is genuinely unsatisfiable,
    so the match is typed with T-MatchTrueOnly and [Leaf] by a vacuous
    subtyping (below; the else branch, and with it F5 and F6, is never
    reached).

    [bst_counterexample_unreachable] (a model of the INFORMAL intent:
    [range x y] returns exactly the [v] with [x < v < y]) remains a correct
    statement about that model, but the model generator does not inhabit
    the strict type (it returns [y] on empty intervals), so it is no
    counterexample to the typing claim.  What F1 shows is that Fig. 7's
    specification is not the intended one: the intended property (every
    BST with keys in (lo, lo+r] is generated) needs the [≤] repair, and
    the [≤]-repaired type [bst_gen_must_ty] is FALSE by F7; the corrected
    must target is [bst_gen_must_fixed_ty].

    A machine-checked proof of the uninhabitedness needs a chain of
    denotation eliminations (persistence to a singleton world, two arrow
    eliminations with result extensions, an FOver introduction for the
    argument [y = 2 : {x < ν}] on the [x = 1] fibre, and the under-atom
    inversion).  The library has the pieces (e.g.
    [res_models_forall_open_named_fresh], [res_models_under_FAtom_inv], and in
    [ExtendedRuleSoundness] [ext_arrow_value_elim] and
    [ext_result_world_exists]) but no packaged "semantic application" lemma,
    so this is kept as a named obligation. *)
Lemma bst_paper_obl_range_strict_uninhabited f (m : WfWorld (V := value)) :
  m ⊨ ctx_denote_under ∅ (f ∷ range_strict_paper_ty) -> False.
Proof.
  (* Semantic: see the comment above (argument extension [x ↦ 1, y ↦ 2];
     the angelic result [[ℕ | 1 < ν < 2]] is an exact atom on an empty set). *)
Admitted.

Definition bst_Γ3s (y : atom) : ctx :=
  bst_Γ3 range_strict_paper_ty true bst_keys_exact y.
Definition bst_Γ4s (y : atom) : ctx := bst_Γ3s y ,, (isz ∷ bst_τisz).
Definition bst_Γts (y : atom) : ctx :=
  bst_Γ3s y ,, (isz ∷ (bst_τisz ⊓ bool_precise_ty true)).

Ltac bst_s_unfold := unfold bst_Γts, bst_Γ4s, bst_Γ3s in *.

(** The T-Fix body context of the verbatim type has no model. *)
Lemma bst_Γ3s_unsat y (m : WfWorld (V := value)) :
  m ⊨ ctx_denote_under ∅ (bst_Γ3s y) -> False.
Proof.
  intros Hm. apply (bst_paper_obl_range_strict_uninhabited range_arg m).
  eapply (bst_comma_binds_denote (bst_Γ3s y) range_arg range_strict_paper_ty);
    [ | exact (range_strict_paper_wf 0 ∅) | exact Hm].
  unfold bst_Γ3s, bst_Γ3. cbn [comma_binds]. right. split; reflexivity.
Qed.

Lemma bst_Γ3s_comma_unsat y Γ (m : WfWorld (V := value)) :
  m ⊨ ctx_denote_under ∅ (bst_Γ3s y ,, Γ) -> False.
Proof.
  intros Hm. eapply bst_Γ3s_unsat. eapply ctx_denote_under_comma_left. exact Hm.
Qed.

(** Body of the A-normal program: [let isz := r ≤ 0] (T-BinOp), T-CtxSub to
    [isz ∷ τisz ⊓ {ν = true}] (vacuous: no model), T-MatchTrueOnly, and
    [Leaf] at the result type (vacuous subtyping: no model). *)
Lemma bst_inner_paper_vacuous y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γ3s y ⊢ₓ bst_inner y ⋮ bst_RES true bst_keys_exact y.
Proof.
  intros Hy.
  unfold bst_fixed_atoms in Hy. bst_split_notin Hy.
  unfold bst_inner.
  eapply (EXT_LetNamed ∅ _ isz bst_τisz);
    [bst_s_unfold; bst_wf_with bst_basic |
     apply EXT_BinOp; bst_s_unfold; bst_wf_with bst_basic | ].
  change (bst_Γ3s y ,, (isz ∷ bst_τisz)) with (bst_Γ4s y).
  eapply (EXT_CtxSub ∅ _ (bst_Γts y)).
  - bst_s_unfold. bst_wf_with bst_basic.
  - eapply (EXT_MatchTrueOnly ∅ _ isz).
    + bst_s_unfold. bst_wf_with bst_basic.
    + bst_s_unfold. bst_isz_var.
    + apply bst_const_typing.
      * bst_s_unfold. bst_ctx_wf.
      * bst_s_unfold. bst_wf_with bst_basic.
      * bst_ty_wf.
      * reflexivity.
      * intros e _ m Hm. exfalso. exact (bst_Γ3s_comma_unsat y _ m Hm).
  - apply bst_ctx_sub_intro.
    + bst_s_unfold. bst_ctx_wf.
    + bst_s_unfold. bst_ctx_wf.
    + intros ? _. bst_s_unfold. bst_erase_eq.
    + intros m Hm. exfalso. exact (bst_Γ3s_comma_unsat y _ m Hm).
Qed.

(** Fig. 7 verbatim, A-normal program: derivable, VACUOUSLY (the range
    parameter type is uninhabited). *)
Theorem bst_gen_anf_paper_typing_vacuous :
  ∅; Emp ⊢ₓ bst_gen_program_anf ⋮ bst_gen_paper_ty.
Proof.
  apply bst_gen_anf_paper_outer. intros y Hy. exact (bst_inner_paper_vacuous y Hy).
Qed.

(** *** The ORIGINAL program [bst_gen_program] at the verbatim type

    The constant argument of [range (1, r)] (F5) lives in the else branch,
    which the vacuous derivation never types, so the original program goes
    through as well.  [bst_inner_orig] is its body, verbatim. *)

Definition bst_inner_orig (lo_a : atom) : tm :=
  let isz := r ⟨ ≤ ⟩ vnat 0 in
  if isz then ret leaf_value
  else ret leaf_value ⊕ₙ
    (let rp := range_arg @@ (vnat 1, r) in
     let left_size := rp ⟨ - ⟩ vnat 1 in
     let right_size := r ⟨ - ⟩ rp in
     let new_lo := lo_a ⟨ + ⟩ rp in
     let left_tree := rec @@@ (left_size, lo_a, range_arg) in
     let right_tree := rec @@@ (right_size, new_lo, range_arg) in
     [| new_lo, left_tree, right_tree |]).

Definition bst_range_lam_orig (lo_a : atom) : tm :=
  ret (ƛ range_arg : ℕ →ᵦ ℕ →ᵦ ℕ => bst_inner_orig lo_a).

Lemma bst_gen_program_shape :
  bst_gen_program =
  ret (μ rec, r : ℕ ~> ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree =>
    ret (ƛ lo : ℕ => bst_range_lam_orig lo)).
Proof. reflexivity. Qed.

Lemma bst_open_close_lo_orig y :
  y ∉ bst_fixed_atoms ->
  open_tm 0 (vfvar y) (close_tm lo 0 (bst_range_lam_orig lo)) = bst_range_lam_orig y.
Proof.
  intros Hy. bst_fresh_hyps.
  rewrite bst_open_close_subst by reflexivity.
  unfold bst_range_lam_orig, bst_inner_orig, Ret.
  cbn [tm_subst].
  rewrite bst_subst_lam_named by bst_neq.
  rewrite bst_subst_let_named by bst_neq.
  unfold if_named. cbn [tm_subst].
  rewrite bst_subst_nondet.
  rewrite !bst_subst_let_named by bst_neq.
  rewrite !bst_subst_call2, !bst_subst_call3.
  unfold node_tm, avar, vnat, leaf_value. cbn [tm_subst value_subst].
  repeat match goal with
    | |- context [decide (?a = ?b)] =>
        destruct (decide (a = b)); try (exfalso; bst_neq); try congruence
    end.
Qed.

Lemma bst_program_orig_basic :
  ∅ ⊢ₑ bst_gen_program ⋮ (ℕ →ᵦ bst_fun_basic_ty).
Proof. exact bst_gen_program_basic_type. Qed.

Ltac bst_basic_orig :=
  unfold bst_range_lam_orig, bst_inner_orig; bst_basic.

(** Outer layers (T-PersistI, T-Fix, T-Lam, T-LamNamed) for the original
    program; same proof as [bst_outer]. *)
Lemma bst_outer_orig R ang P
  (HRer : erase_ty R = (ℕ →ᵦ ℕ →ᵦ ℕ))
  (HRopen : forall k x, cty_open k x R = R)
  (HRwf : forall d D, wf_context_ty_at d D R) :
  (forall y, y ∉ bst_fixed_atoms ->
     ∅; bst_Γ3 R ang P y ⊢ₓ bst_inner_orig y ⋮ bst_RES ang P y) ->
  ∅; Emp ⊢ₓ bst_gen_program ⋮ bst_full_ty R ang P.
Proof.
  intros Hbody.
  assert (Hwf0 : ∅; Emp ⊢wf bst_gen_program ⋮ bst_full_ty R ang P).
  { unfold context_typing_wf. split; [ | split].
    - unfold wf_ctx_under. cbn. exact I.
    - unfold bst_full_ty. cbn [wf_context_ty_at]. split; [bst_ty_wf | ].
      apply bst_body_ty_wf; exact HRwf.
    - unfold bst_full_ty. cbn [erase_ctx erase_ty]. rewrite bst_body_ty_erase by exact HRer.
      apply bst_program_orig_basic. }
  rewrite bst_gen_program_shape in *.
  unfold bst_full_ty in *.
  eapply EXT_PersistIntro; [exact Hwf0 | exact bst_gen_obl_persist_emp | ].
  refine (EXT_FixNamed ∅ Emp qual_top (bst_body_ty R ang P) rec r TNat
    bst_fun_basic_ty _ _ _ _).
  - apply bst_body_ty_erase; exact HRer.
  - unfold context_typing_wf. split; [ | split].
    + bst_ctx_wf.
    + cbn [wf_context_ty_at]. split; [bst_ty_wf | apply bst_body_ty_wf; exact HRwf].
    + cbn [erase_ctx erase_ty]. rewrite bst_body_ty_erase by exact HRer.
      exact bst_program_orig_basic.
  - rewrite (bst_body_open R ang P HRer HRopen HRwf).
    eapply EXT_LamNamedErased;
      [unfold fix_rec_call_ty; cbn [erase_ty]; rewrite bst_body_ty_erase by exact HRer;
       reflexivity | | ].
    { bst_wf_with ltac:(rewrite ?bst_body_ty_erase by exact HRer; rewrite ?HRer; bst_basic_orig). }
    refine (EXT_Lam ∅ (bst_Γrec R ang P) O[ ℕ ]
      (R → bst_res_ty ang (q_tree_spec (vfvar r) (vbvar 2) ν P))
      (close_tm lo 0 (bst_range_lam_orig lo)) bst_fixed_atoms _ _).
    { bst_wf_with ltac:(rewrite ?bst_body_ty_erase by exact HRer; rewrite ?HRer; bst_basic_orig). }
    intros y Hy.
    pose proof (bst_fresh_of_notin y Hy) as Hfr.
    change (close_tm lo 0 (bst_range_lam_orig lo) ^^ y) with
      (open_tm 0 (vfvar y) (close_tm lo 0 (bst_range_lam_orig lo))).
    rewrite (bst_open_close_lo_orig y Hy).
    change ((R → bst_res_ty ang (q_tree_spec r (vbvar 2) ν P)) ^^ y) with
      (cty_open 0 y (R → bst_res_ty ang (q_tree_spec r (vbvar 2) ν P))).
    rewrite (bst_res_open R ang P HRer HRopen HRwf) by (destruct Hfr; congruence).
    unfold bst_fresh in Hfr. destruct_and! Hfr.
    unfold bst_range_lam_orig.
    eapply EXT_LamNamedErased; [rewrite HRer; reflexivity | | ].
    { bst_wf_with ltac:(rewrite ?bst_body_ty_erase by exact HRer; rewrite ?HRer; bst_basic_orig). }
    apply Hbody. exact Hy.
Qed.

Lemma bst_inner_orig_paper_vacuous y :
  y ∉ bst_fixed_atoms ->
  ∅; bst_Γ3s y ⊢ₓ bst_inner_orig y ⋮ bst_RES true bst_keys_exact y.
Proof.
  intros Hy.
  unfold bst_fixed_atoms in Hy. bst_split_notin Hy.
  unfold bst_inner_orig.
  eapply (EXT_LetNamed ∅ _ isz bst_τisz);
    [bst_s_unfold; bst_wf_with bst_basic |
     apply EXT_BinOp; bst_s_unfold; bst_wf_with bst_basic | ].
  change (bst_Γ3s y ,, (isz ∷ bst_τisz)) with (bst_Γ4s y).
  eapply (EXT_CtxSub ∅ _ (bst_Γts y)).
  - bst_s_unfold. bst_wf_with bst_basic.
  - eapply (EXT_MatchTrueOnly ∅ _ isz).
    + bst_s_unfold. bst_wf_with bst_basic.
    + bst_s_unfold. bst_isz_var.
    + apply bst_const_typing.
      * bst_s_unfold. bst_ctx_wf.
      * bst_s_unfold. bst_wf_with bst_basic.
      * bst_ty_wf.
      * reflexivity.
      * intros e _ m Hm. exfalso. exact (bst_Γ3s_comma_unsat y _ m Hm).
  - apply bst_ctx_sub_intro.
    + bst_s_unfold. bst_ctx_wf.
    + bst_s_unfold. bst_ctx_wf.
    + intros ? _. bst_s_unfold. bst_erase_eq.
    + intros m Hm. exfalso. exact (bst_Γ3s_comma_unsat y _ m Hm).
Qed.

(** Fig. 7 verbatim, ORIGINAL program: derivable, VACUOUSLY.  Depends only
    on [bst_paper_obl_range_strict_uninhabited]. *)
Theorem bst_gen_paper_typing_vacuous :
  ∅; Emp ⊢ₓ bst_gen_program ⋮ bst_gen_paper_ty.
Proof.
  unfold bst_gen_paper_ty.
  apply bst_outer_orig; [reflexivity | exact range_strict_paper_open |
    exact range_strict_paper_wf | ].
  intros y Hy. exact (bst_inner_orig_paper_vacuous y Hy).
Qed.

Local Open Scope nat_scope.

(** ** A set-of-results model of Fig. 7 (sanity checks of the specs)

    [bst_gen_model range r lo t] holds iff [t] is a possible result of
    [bst_gen r lo range] when [range x y] may return exactly the values [v]
    with [range x y v] (Leaf ⊕ ... is angelic choice). *)
Inductive bst_gen_model (range : nat -> nat -> nat -> Prop) :
    nat -> nat -> tree -> Prop :=
  | bgm_leaf r0 lo0 : bst_gen_model range r0 lo0 tr_leaf
  | bgm_node r0 lo0 r' L Rt :
      0 < r0 ->
      range 1 r0 r' ->
      bst_gen_model range (r' - 1) lo0 L ->
      bst_gen_model range (r0 - r') (lo0 + r') Rt ->
      bst_gen_model range r0 lo0 (tr_node (lo0 + r') L Rt).

(** The corrected generator: [range x y] returns exactly [x ≤ v ≤ y]. *)
Definition range_le_rel (x y v : nat) : Prop := x <= v <= y.

(** A model of the INFORMAL intent of Fig. 7's range: return exactly the
    values strictly between [x] and [y] (on an empty interval we let it
    return [y]).  CAUTION (round-2 fix): this generator does NOT inhabit
    [range_strict_paper_ty]; no generator does, because on the empty
    interval [y = x + 1] the angelic result [[x < ν < y]] is an exact atom
    over an empty set (see [bst_paper_obl_range_strict_uninhabited]).
    The lemmas below about [range_strict_rel] therefore concern the model,
    not the typing claim. *)
Definition range_strict_rel (x y v : nat) : Prop :=
  (x < v < y) \/ (y <= S x /\ v = y).

Lemma bst_keys_within_node_inv r0 lo0 k L Rt :
  bst_keys_within r0 lo0 (tr_node k L Rt) ->
  lo0 < k <= lo0 + r0 /\
  bst_keys_within (k - lo0 - 1) lo0 L /\
  bst_keys_within (r0 - (k - lo0)) k Rt.
Proof.
  intros [[HL [HR [HbL HbR]]] Hmem].
  assert (Hk : lo0 < k <= lo0 + r0) by (apply Hmem; cbn; left; reflexivity).
  split; [exact Hk | split; split; try assumption].
  - intros n Hn. specialize (HL n Hn).
    assert (lo0 < n <= lo0 + r0) by (apply Hmem; cbn; right; left; exact Hn).
    lia.
  - intros n Hn. specialize (HR n Hn).
    assert (lo0 < n <= lo0 + r0) by (apply Hmem; cbn; right; right; exact Hn).
    lia.
Qed.

(** Safety of the corrected generator (the may type, in the model). *)
Lemma bst_gen_model_le_sound r0 lo0 t :
  bst_gen_model range_le_rel r0 lo0 t -> bst_keys_within r0 lo0 t.
Proof.
  induction 1 as [r0 lo0 | r0 lo0 r' L Rt Hpos Hr HL IHL HR IHR].
  - split; [exact I | intros n []].
  - unfold range_le_rel in Hr.
    destruct IHL as [HbL HmL], IHR as [HbR HmR].
    split.
    + cbn. repeat split; try assumption.
      * intros n Hn. specialize (HmL n Hn). lia.
      * intros n Hn. specialize (HmR n Hn). lia.
    + intros n [->|[Hn|Hn]].
      * lia.
      * specialize (HmL n Hn). lia.
      * specialize (HmR n Hn). lia.
Qed.

(** Completeness of the corrected generator (the must type, in the model):
    every BST whose keys lie within (lo, lo + r] is a possible result. *)
Lemma bst_gen_model_le_complete t :
  forall r0 lo0, bst_keys_within r0 lo0 t -> bst_gen_model range_le_rel r0 lo0 t.
Proof.
  induction t as [ | k L IHL Rt IHR]; intros r0 lo0 Hspec.
  - constructor.
  - apply bst_keys_within_node_inv in Hspec as [Hk [HL HR]].
    replace k with (lo0 + (k - lo0)) by lia.
    apply bgm_node.
    + lia.
    + unfold range_le_rel. lia.
    + replace (k - lo0 - 1) with (k - lo0 - 1) in HL by reflexivity.
      apply IHL. exact HL.
    + replace (lo0 + (k - lo0)) with k by lia. apply IHR. exact HR.
Qed.

(** Off-by-one of Fig. 7's SPECIFICATION (model level only, see F1): with
    the informal strict generator [range_strict_rel], [bst_gen 3 0] never
    produces a tree whose root is [1], although
    [Node 1 Leaf (Node 2 Leaf (Node 3 Leaf Leaf))] is a BST whose keys are
    exactly [{1,2,3}] (so it satisfies both the [⟺] and the [⟹]
    reading of the paper's specification).  This is NOT a counterexample to
    the typing [bst_gen_paper_ty], which holds vacuously. *)
Definition bst_counterexample_tree : tree :=
  tr_node 1 tr_leaf (tr_node 2 tr_leaf (tr_node 3 tr_leaf tr_leaf)).

Lemma bst_counterexample_spec :
  bst_keys_exact 3 0 bst_counterexample_tree /\
  bst_keys_within 3 0 bst_counterexample_tree.
Proof.
  unfold bst_keys_exact, bst_keys_within, bst_counterexample_tree.
  assert (Hbst : is_bst
    (tr_node 1 tr_leaf (tr_node 2 tr_leaf (tr_node 3 tr_leaf tr_leaf)))).
  { cbn. repeat split; intros n Hn; cbn in Hn; lia. }
  split; split; try exact Hbst.
  - intros n. cbn. lia.
  - intros n Hn. cbn in Hn. lia.
Qed.

Lemma bst_counterexample_unreachable :
  ~ bst_gen_model range_strict_rel 3 0 bst_counterexample_tree.
Proof.
  unfold bst_counterexample_tree. intros H.
  inversion H as [ | r0 lo0 r' L Rt Hpos Hr HL HR]; subst.
  unfold range_strict_rel in Hr.
  (* the root is [0 + r'] with [1 < r' < 3], i.e. [r' = 2], not [1] *)
  lia.
Qed.

(** ** (F7) Model of the call graph: an under-approximate range makes
    [bst_gen] non-terminating (see the comment before
    [bst_gen_must_fixed_ty]). *)

Inductive bst_calls (range : nat -> nat -> nat -> Prop) :
    nat -> nat -> nat -> nat -> Prop :=
  | bc_left r0 lo0 k :
      0 < r0 -> range 1 r0 k -> bst_calls range r0 lo0 (k - 1) lo0
  | bc_right r0 lo0 k :
      0 < r0 -> range 1 r0 k -> bst_calls range r0 lo0 (r0 - k) (lo0 + k).

Definition range_bad_rel (x y v : nat) : Prop := (x <= v <= y)%nat \/ v = S y.

Lemma range_bad_covers x y v : range_le_rel x y v -> range_bad_rel x y v.
Proof. intros H. left. exact H. Qed.

Lemma bst_bad_range_self_call lo0 : bst_calls range_bad_rel 1 lo0 1 lo0.
Proof.
  exact (bc_left range_bad_rel 1 lo0 2 ltac:(lia) ltac:(right; reflexivity)).
Qed.

Lemma bst_le_range_calls_decrease r0 lo0 r1 lo1 :
  bst_calls range_le_rel r0 lo0 r1 lo1 -> (r1 < r0)%nat.
Proof. intros H; inversion H; subst; unfold range_le_rel in *; lia. Qed.


End BSTGeneratorExample.
