(** * Merge/disprove case-study program *)

From ProofAutomation Require Import BasicTypeInfer.
From LocallyNameless Require Import Tactics.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section DisproveMergeExample.

Definition merge : atom := 40%positive.
Definition xs : atom := 41%positive.
Definition ys : atom := 42%positive.
Definition h1 : atom := 43%positive.
Definition t1 : atom := 44%positive.
Definition h2 : atom := 45%positive.
Definition t2 : atom := 46%positive.
Definition t : atom := 47%positive.
Definition lt12 : atom := 48%positive.
Definition gt12 : atom := 49%positive.
Definition tail12 : atom := 50%positive.
Definition tail21 : atom := 51%positive.

Fixpoint mem_list (n : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => False
  | x :: xs => n = x \/ mem_list n xs
  end.

Fixpoint sorted_from (prev : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs => prev <= x /\ sorted_from x xs
  end.

Definition sorted (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs => sorted_from x xs
  end.

Definition q_sorted_list (v : value) : type_qualifier :=
  q_list_pred v sorted.

Definition q_not_sorted_list (v : value) : type_qualifier :=
  q_list_pred v (fun xs => ~ sorted xs).

Definition OSortedList : context_ty :=
  over_ty TList (q_sorted_list ν).

Definition UNotSortedList : context_ty :=
  under_ty TList (q_not_sorted_list ν).

Definition merge_basic_ty : ty :=
  List →ᵦ List →ᵦ List.

Definition le_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition merge_safety_ty : context_ty :=
  OSortedList → OSortedList → OSortedList.

Definition merge_disprove_ty : context_ty :=
  O[ List ] → O[ List ] → OSortedList ⊕ UNotSortedList.

Definition merge_program : tm :=
  ret (μ merge, xs : List ~> List →ᵦ List =>
    ret (ƛ ys : List =>
      matchList (xs;
      Nil => ret ys;
      Cons (h1, t1) =>
        matchList (ys;
        Nil => ret xs;
        Cons (h2, t2) =>
          (let t := merge @@ (t1, t2) in
          let lt12 := h1 ⟨ < ⟩ h2 in
          if lt12 then
            let tail12 := h2 ::ᵗ t in
            h1 ::ᵗ tail12
          else
            let gt12 := h1 ⟨ > ⟩ h2 in
            if gt12 then
              let tail21 := h1 ::ᵗ t in
              h2 ::ᵗ tail21
            else
              h1 ::ᵗ t)
        )
			      ))).

Ltac merge_lookup :=
  repeat (rewrite lookup_insert_ne by
    solve [eassumption | symmetry; eassumption | vm_compute; congruence]);
  try rewrite lookup_insert;
  reflexivity.

Ltac finite_set_in :=
  first
    [ apply elem_of_singleton; reflexivity
    | apply elem_of_union_l; finite_set_in
    | apply elem_of_union_r; finite_set_in ].

Lemma merge_program_basic_type :
  ∅ ⊢ₑ merge_program ⋮ merge_basic_ty.
Proof.
  unfold merge_program, merge_basic_ty.
  repeat progress basic_type_surface_norm.
  eapply TT_Ret.
  eapply basic_typing_fixfun_named; [basic_type_fresh|basic_type_fresh|idtac].
  eapply TT_Ret.
  eapply basic_typing_lam_named; [basic_type_fresh|idtac].
  unfold match_list_named.
  eapply TT_ListMatch with
    (L := {[merge; xs; ys]});
    [basic_type|basic_type|idtac].
  intros hd tl Hhd Htl.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in Hhd, Htl.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21.
  assert (Htl_ys : tl <> 42%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_ys : hd <> 42%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_xs : tl <> 41%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_xs : hd <> 41%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_merge : tl <> 40%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_merge : hd <> 40%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_hd : tl <> hd)
    by (intro Heq; subst; apply Htl; finite_set_in).
  simpl.
  eapply TT_ListMatch with
    (L := {[merge; hd; tl]}).
  - eapply VT_FVar;
      rewrite lookup_insert_ne by exact Htl_ys;
      rewrite lookup_insert_ne by exact Hhd_ys;
      try rewrite lookup_insert;
      reflexivity.
  - eapply TT_Ret; eapply VT_FVar;
      rewrite lookup_insert_ne by exact Htl_xs;
      rewrite lookup_insert_ne by exact Hhd_xs;
      try rewrite lookup_insert_ne by (vm_compute; congruence);
      try rewrite lookup_insert_ne by (unfold merge; vm_compute; congruence);
      try rewrite lookup_insert;
      reflexivity.
  - 
  intros hd2 tl2 Hhd2 Htl2.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in Hhd2, Htl2.
  assert (Hhd2_merge : hd2 <> 40%positive)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_merge : tl2 <> 40%positive)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Hhd2_tl : hd2 <> tl)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_tl : tl2 <> tl)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Hhd2_hd : hd2 <> hd)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_hd : tl2 <> hd)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Htl2_hd2 : tl2 <> hd2)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  simpl.
  repeat progress basic_type_surface_norm.
  eapply_tt_let_with_stales.
  { eapply TT_Let with
      (L := {[merge; hd; tl; hd2; tl2]})
      (T1 := (List →ᵦ List)).
    { eapply TT_App.
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar. basic_lookup. } }
    { intros f Hf.
      assert (Hf_tl2 : f <> tl2)
        by (intro Heq; subst; apply Hf; finite_set_in).
      simpl.
      eapply TT_App.
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar.
        rewrite lookup_insert_ne by exact Hf_tl2.
        basic_lookup. } } }
  { intros mt Hmt.
    assert (Hmt_hd : mt <> hd)
      by (intro Heq; subst; apply Hmt; finite_set_in).
    assert (Hmt_hd2 : mt <> hd2)
      by (intro Heq; subst; apply Hmt; finite_set_in).
    simpl.
    repeat progress basic_type_surface_norm.
    eapply TT_Let with
      (L := {[merge; hd; tl; hd2; tl2; mt]})
      (T1 := 𝔹).
    { eapply TT_BinOp.
      { reflexivity. }
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar. basic_lookup. } }
    { intros mlt Hmlt.
      assert (Hmlt_hd : mlt <> hd)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      assert (Hmlt_hd2 : mlt <> hd2)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      assert (Hmlt_mt : mlt <> mt)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      simpl.
      eapply TT_Match.
      { basic_type. }
      { eapply TT_Let with
          (L := {[merge; hd; tl; hd2; tl2; mt; mlt]})
          (T1 := TBase TList).
        { eapply TT_ListCons.
          { eapply VT_FVar. basic_lookup. }
          { eapply VT_FVar. basic_lookup. } }
        { intros mtail Hmtail.
          assert (Hmtail_hd : mtail <> hd)
            by (intro Heq; subst; apply Hmtail; finite_set_in).
          simpl.
          eapply TT_ListCons.
          { eapply VT_FVar.
            rewrite lookup_insert_ne by exact Hmtail_hd.
            basic_lookup. }
          { eapply VT_FVar. basic_lookup. } } }
      { eapply TT_Let with
          (L := {[merge; hd; tl; hd2; tl2; mt; mlt]})
          (T1 := 𝔹).
        { eapply TT_BinOp.
          { reflexivity. }
          { eapply VT_FVar. basic_lookup. }
          { eapply VT_FVar. basic_lookup. } }
        { intros mgt Hmgt.
          assert (Hmgt_hd : mgt <> hd)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          assert (Hmgt_hd2 : mgt <> hd2)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          assert (Hmgt_mt : mgt <> mt)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          simpl.
          eapply TT_Match.
          { basic_type. }
          { eapply TT_Let with
              (L := {[merge; hd; tl; hd2; tl2; mt; mlt; mgt]})
              (T1 := TBase TList).
            { eapply TT_ListCons.
              { eapply VT_FVar. basic_lookup. }
              { eapply VT_FVar. basic_lookup. } }
            { intros mtail2 Hmtail2.
              assert (Hmtail2_hd2 : mtail2 <> hd2)
                by (intro Heq; subst; apply Hmtail2; finite_set_in).
              simpl.
              eapply TT_ListCons.
              { eapply VT_FVar.
                rewrite lookup_insert_ne by exact Hmtail2_hd2.
                basic_lookup. }
              { eapply VT_FVar. basic_lookup. } } }
          { basic_type. } } } } }
Qed.

Lemma sorted_nil :
  sorted [].
Proof. cbn. exact I. Qed.

Lemma sorted_singleton n :
  sorted [n].
Proof. cbn. exact I. Qed.

Lemma mem_list_here n xs :
  mem_list n (n :: xs).
Proof. cbn. left. reflexivity. Qed.

Lemma basic_type_nil_ret Γ :
  Γ ⊢ₑ Ret nil_value ⋮ List.
Proof.
  unfold Ret, nil_value.
  constructor. constructor.
Qed.

Lemma basic_type_cons_nat_list Γ n xs :
  Γ ⊢ₑ cons_tm (vnat n) (vlist xs) ⋮ List.
Proof.
  unfold cons_tm, vnat, vlist.
  econstructor; constructor.
Qed.

Lemma merge_basic_first_call Γ (merge xs : atom) :
  Γ !! merge = Some merge_basic_ty ->
  Γ !! xs = Some (List : ty) ->
  Γ ⊢ₑ tapp merge xs ⋮ (List →ᵦ List).
Proof.
  intros Hmerge Hxs.
  econstructor.
  - constructor. exact Hmerge.
  - constructor. exact Hxs.
Qed.


(** ** Paper-facing decomposition of [merge_program]

    [merge_step_tm] is literally the code after the recursive call
    [let t := merge t1 t2 in ...] (Fig. 8, lines 7-9).  It is factored out
    so that the bug-witness fragment below can be typed on its own. *)

Definition merge_step_tm : tm :=
  let lt12 := h1 ⟨ < ⟩ h2 in
  if lt12 then
    let tail12 := h2 ::ᵗ t in
    h1 ::ᵗ tail12
  else
    let gt12 := h1 ⟨ > ⟩ h2 in
    if gt12 then
      let tail21 := h1 ::ᵗ t in
      h2 ::ᵗ tail21
    else
      h1 ::ᵗ t.

(** Alias for the recursive binder; after importing stdpp-heavy modules the
    bare name [merge] is shadowed by stdpp's [merge]. *)
Definition merge_self : atom := merge.

Definition merge_fix_value : value :=
  μ merge, xs : List ~> List →ᵦ List =>
    ret (ƛ ys : List =>
      matchList (xs;
      Nil => ret ys;
      Cons (h1, t1) =>
        matchList (ys;
        Nil => ret xs;
        Cons (h2, t2) =>
          (let t := merge @@ (t1, t2) in merge_step_tm)))).

Lemma merge_program_unfold :
  merge_program = ret merge_fix_value.
Proof. reflexivity. Qed.


(** Concrete data of the paper's counterexample (Fig. 8 discussion):
    [merge [1;2] [3;4] ↦* [1;3;2;4]], whose last step runs
    [merge_step_tm] with [h1 = 1], [h2 = 3] and [t = merge [2] [4] = [2;4]]. *)
Definition cex_l1 : list nat := [1%nat; 2%nat].
Definition cex_l2 : list nat := [3%nat; 4%nat].
Definition cex_rec : list nat := [2%nat; 4%nat].
Definition cex_out : list nat := [1%nat; 3%nat; 2%nat; 4%nat].

Lemma cex_l1_sorted : sorted cex_l1.
Proof. cbn. lia. Qed.

Lemma cex_l2_sorted : sorted cex_l2.
Proof. cbn. lia. Qed.

Lemma cex_out_not_sorted : ~ sorted cex_out.
Proof. cbn. lia. Qed.


Lemma merge_step_basic (Γ : gmap atom ty) :
  Γ !! h1 = Some (TBase TNat) -> Γ !! h2 = Some (TBase TNat) ->
  Γ !! t = Some (TBase TList) ->
  lt12 ∉ dom Γ -> tail12 ∉ dom Γ -> gt12 ∉ dom Γ -> tail21 ∉ dom Γ ->
  Γ ⊢ₑ merge_step_tm ⋮ List.
Proof.
  intros Hh1 Hh2 Ht Hlt Htl Hgt Htr.
  unfold merge_step_tm.
  eapply basic_typing_let_named; [exact Hlt | | ].
  { eapply TT_BinOp; [reflexivity|constructor; exact Hh1|constructor; exact Hh2]. }
  unfold if_named. eapply TT_Match.
  - constructor. apply map_lookup_insert.
  - basic_type.
  - basic_type.
Qed.

(** Basic-typing building blocks for the typed fragments below (they replay
    the proof of [merge_program_basic_type] on its sub-terms). *)
Definition merge_rec_body : tm :=
  matchList (xs;
  Nil => ret ys;
  Cons (h1, t1) =>
    matchList (ys;
    Nil => ret xs;
    Cons (h2, t2) =>
      (let t := merge @@ (t1, t2) in merge_step_tm))).

Definition merge_env_match : gmap atom ty :=
  <[ys:=TBase TList]> (<[merge:=merge_basic_ty]> (<[xs:=TBase TList]> ∅)).

Lemma merge_match_basic :
  merge_env_match ⊢ₑ merge_rec_body ⋮ List.
Proof.
  unfold merge_env_match, merge_rec_body, merge_step_tm, merge_basic_ty.
  unfold match_list_named.
  eapply TT_ListMatch with
    (L := {[merge; xs; ys]});
    [basic_type|basic_type|idtac].
  intros hd tl Hhd Htl.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in Hhd, Htl.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21.
  assert (Htl_ys : tl <> 42%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_ys : hd <> 42%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_xs : tl <> 41%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_xs : hd <> 41%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_merge : tl <> 40%positive)
    by (intro Heq; subst; apply Htl; finite_set_in).
  assert (Hhd_merge : hd <> 40%positive)
    by (intro Heq; subst; apply Hhd; finite_set_in).
  assert (Htl_hd : tl <> hd)
    by (intro Heq; subst; apply Htl; finite_set_in).
  simpl.
  eapply TT_ListMatch with
    (L := {[merge; hd; tl]}).
  - eapply VT_FVar;
      rewrite lookup_insert_ne by exact Htl_ys;
      rewrite lookup_insert_ne by exact Hhd_ys;
      try rewrite lookup_insert;
      reflexivity.
  - eapply TT_Ret; eapply VT_FVar;
      rewrite lookup_insert_ne by exact Htl_xs;
      rewrite lookup_insert_ne by exact Hhd_xs;
      try rewrite lookup_insert_ne by (vm_compute; congruence);
      try rewrite lookup_insert_ne by (unfold merge; vm_compute; congruence);
      try rewrite lookup_insert;
      reflexivity.
  - 
  intros hd2 tl2 Hhd2 Htl2.
  unfold merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in Hhd2, Htl2.
  assert (Hhd2_merge : hd2 <> 40%positive)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_merge : tl2 <> 40%positive)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Hhd2_tl : hd2 <> tl)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_tl : tl2 <> tl)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Hhd2_hd : hd2 <> hd)
    by (intro Heq; subst; apply Hhd2; finite_set_in).
  assert (Htl2_hd : tl2 <> hd)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  assert (Htl2_hd2 : tl2 <> hd2)
    by (intro Heq; subst; apply Htl2; finite_set_in).
  simpl.
  repeat progress basic_type_surface_norm.
  eapply_tt_let_with_stales.
  { eapply TT_Let with
      (L := {[merge; hd; tl; hd2; tl2]})
      (T1 := (List →ᵦ List)).
    { eapply TT_App.
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar. basic_lookup. } }
    { intros f Hf.
      assert (Hf_tl2 : f <> tl2)
        by (intro Heq; subst; apply Hf; finite_set_in).
      simpl.
      eapply TT_App.
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar.
        rewrite lookup_insert_ne by exact Hf_tl2.
        basic_lookup. } } }
  { intros mt Hmt.
    assert (Hmt_hd : mt <> hd)
      by (intro Heq; subst; apply Hmt; finite_set_in).
    assert (Hmt_hd2 : mt <> hd2)
      by (intro Heq; subst; apply Hmt; finite_set_in).
    simpl.
    repeat progress basic_type_surface_norm.
    eapply TT_Let with
      (L := {[merge; hd; tl; hd2; tl2; mt]})
      (T1 := 𝔹).
    { eapply TT_BinOp.
      { reflexivity. }
      { eapply VT_FVar. basic_lookup. }
      { eapply VT_FVar. basic_lookup. } }
    { intros mlt Hmlt.
      assert (Hmlt_hd : mlt <> hd)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      assert (Hmlt_hd2 : mlt <> hd2)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      assert (Hmlt_mt : mlt <> mt)
        by (intro Heq; subst; apply Hmlt; finite_set_in).
      simpl.
      eapply TT_Match.
      { basic_type. }
      { eapply TT_Let with
          (L := {[merge; hd; tl; hd2; tl2; mt; mlt]})
          (T1 := TBase TList).
        { eapply TT_ListCons.
          { eapply VT_FVar. basic_lookup. }
          { eapply VT_FVar. basic_lookup. } }
        { intros mtail Hmtail.
          assert (Hmtail_hd : mtail <> hd)
            by (intro Heq; subst; apply Hmtail; finite_set_in).
          simpl.
          eapply TT_ListCons.
          { eapply VT_FVar.
            rewrite lookup_insert_ne by exact Hmtail_hd.
            basic_lookup. }
          { eapply VT_FVar. basic_lookup. } } }
      { eapply TT_Let with
          (L := {[merge; hd; tl; hd2; tl2; mt; mlt]})
          (T1 := 𝔹).
        { eapply TT_BinOp.
          { reflexivity. }
          { eapply VT_FVar. basic_lookup. }
          { eapply VT_FVar. basic_lookup. } }
        { intros mgt Hmgt.
          assert (Hmgt_hd : mgt <> hd)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          assert (Hmgt_hd2 : mgt <> hd2)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          assert (Hmgt_mt : mgt <> mt)
            by (intro Heq; subst; apply Hmgt; finite_set_in).
          simpl.
          eapply TT_Match.
          { basic_type. }
          { eapply TT_Let with
              (L := {[merge; hd; tl; hd2; tl2; mt; mlt; mgt]})
              (T1 := TBase TList).
            { eapply TT_ListCons.
              { eapply VT_FVar. basic_lookup. }
              { eapply VT_FVar. basic_lookup. } }
            { intros mtail2 Hmtail2.
              assert (Hmtail2_hd2 : mtail2 <> hd2)
                by (intro Heq; subst; apply Hmtail2; finite_set_in).
              simpl.
              eapply TT_ListCons.
              { eapply VT_FVar.
                rewrite lookup_insert_ne by exact Hmtail2_hd2.
                basic_lookup. }
              { eapply VT_FVar. basic_lookup. } } }
          { basic_type. } } } } }
Qed.

Lemma merge_lam_ys_basic :
  <[merge:=merge_basic_ty]> (<[xs:=TBase TList]> ∅) ⊢ₑ
    ret (ƛ ys : List => merge_rec_body) ⋮ (List →ᵦ List).
Proof.
  eapply TT_Ret. eapply basic_typing_lam_named; [basic_type_fresh | ].
  exact merge_match_basic.
Qed.

Lemma merge_lam_self_basic :
  <[xs:=TBase TList]> ∅ ⊢ₑ
    ret (lam_named merge (TBase TList →ₜ (List →ᵦ List)) (ret (ƛ ys : List => merge_rec_body)))
    ⋮ (merge_basic_ty →ᵦ List →ᵦ List).
Proof.
  eapply TT_Ret. eapply basic_typing_lam_named; [basic_type_fresh | ].
  exact merge_lam_ys_basic.
Qed.

End DisproveMergeExample.

(** * Operational witness of the safety failure (Fig. 8 discussion)

    [merge [1;2] [3;4] ↦* [1;3;2;4]]: both inputs are sorted
    ([cex_l1_sorted], [cex_l2_sorted]) but the output is not
    ([cex_out_not_sorted]).  This is checked against the core small-step
    semantics of [merge_program], not against a Rocq re-implementation. *)

From CoreLang Require Import SmallStep OperationalProps BasicTyping.

Definition cex_tm : tm :=
  call2_tm merge_fix_value (vlist cex_l1) (vlist cex_l2).

Lemma cex_tm_basic : ∅ ⊢ₑ cex_tm ⋮ List.
Proof.
  pose proof merge_program_basic_type as H.
  rewrite merge_program_unfold in H. unfold Ret in H.
  inversion H; subst.
  unfold cex_tm, call2_tm, case_app.
  eapply basic_typing_tapp_tm.
  - eapply TT_App; [exact H2 | constructor].
  - constructor.
Qed.

Ltac solve_step Hlc :=
  lazymatch goal with
  | |- step (tlete (tret ?v) ?e) _ => apply Step_head; apply HS_Ret; exact Hlc
  | |- step (tlete ?e1 ?e2) _ =>
      let H1 := fresh "Hlc1" in
      assert (H1 : lc_tm e1) by (inversion Hlc; assumption);
      apply Step_let; [solve_step H1 | exact Hlc]
  | |- step (tapp (vfix _ _) _) _ => apply Step_head; apply HS_Fix; exact Hlc
  | |- step (tapp (vlam _ _) _) _ => apply Step_head; apply HS_Beta; exact Hlc
  | |- step (tbinop _ (vconst _) (vconst _)) _ =>
      apply Step_head; eapply HS_BinOp; [constructor | exact Hlc]
  | |- step (tmatch (vconst (cbool true)) _ _) _ => apply Step_head; apply HS_MatchTrue; exact Hlc
  | |- step (tmatch (vconst (cbool false)) _ _) _ => apply Step_head; apply HS_MatchFalse; exact Hlc
  | |- step (tcons (vconst (cnat _)) (vconst (clist _))) _ => apply Step_head; apply HS_ListCons; exact Hlc
  | |- step (tmatchlist (vconst (clist nil)) _ _) _ => apply Step_head; apply HS_MatchListNil; exact Hlc
  | |- step (tmatchlist (vconst (clist (_ :: _))) _ _) _ => apply Step_head; apply HS_MatchListCons; exact Hlc
  end.

Ltac run_steps Hty :=
  lazymatch goal with
  | |- steps (tret ?v) _ => apply Steps_refl; exact (typing_tm_lc _ _ _ Hty)
  | |- steps ?e _ =>
      let Hs := fresh "Hs" in
      let Hty' := fresh "Hty" in
      let Hl := fresh "Hl" in
      pose proof (typing_tm_lc _ _ _ Hty) as Hl;
      eassert (Hs : step e _) by (solve_step Hl);
      clear Hl;
      pose proof (basic_step_preservation _ _ _ _ Hty Hs) as Hty';
      eapply Steps_step; [exact Hs | ];
      clear Hs Hty;
      vm_compute in Hty' |- *;
      run_steps Hty'
  end.

Lemma merge_cex_reduces : cex_tm →* tret (vlist cex_out).
Proof.
  pose proof cex_tm_basic as Hty.
  vm_compute in Hty |- *.
  run_steps Hty.
Qed.

Lemma merge_safety_violated :
  sorted cex_l1 /\ sorted cex_l2 /\
  cex_tm →* tret (vlist cex_out) /\ ~ sorted cex_out.
Proof.
  split; [exact cex_l1_sorted | ].
  split; [exact cex_l2_sorted | ].
  split; [exact merge_cex_reduces | exact cex_out_not_sorted].
Qed.

From ProofAutomation Require Import ExtendedTypeInfer.
From ContextTyping Require Import Typing PrimOpConcreteContext.
From ContextLogic Require Import FormulaSemantics.
From ContextBasicDenotation Require Import StoreTyping BasicTypingFormula TermTLet RelevantEnv.
From Denotation Require Import Context TypeEquivCore.

Open Scope ctx_scope.

(** * Context typing of the merge case study (paper §6, Fig. 8)

    ** Summary (round 2; see also the round-2 section at the end of the file)

    The paper claims (p. 23)

      merge : l1:[ν: nat list | ⊤] -∗ l2:[ν: nat list | ⊤] -∗
              {ν: nat list | ¬sorted ν} ⊕ {ν: nat list | ⊤}

    and, from the surrounding text ("l1 and l2 each range over all sorted
    lists"), presumably means the parameters to be [ν | sorted ν].  Both
    targets are defined below ([merge_paper_ty], [merge_paper_sorted_ty]) and
    checked well formed.  Paper [nat list] is Rocq [List] (lists of [ℕ]).

    - DERIVED (round 3, repaired): [merge_cex_extended_type], the disproof
      type with the angelic ranges instantiated to the counterexample
      [l1 = [1;2]], [l2 = [3;4]] (precise singleton capabilities), by
      unrolling ([EXT_FixUnrollNamed], at the [fix_unroll_shape] target
      [mu_cex_arrow_ty = l1 → l2 -∗ {¬sorted} ⊕ {⊤}]) and the corrected
      named list-match rules (pattern variables bound by the branch context
      itself, introduced with [EXT_CtxSub]); the paper's [l1 -∗ l2 -∗ ..]
      form then follows by [EXT_Sub] with the PROVED generic subtyping
      [τx → τ <: τx -∗ τ] ([mu_sub_arrow_to_wand]).  The pattern
      introductions are PROVED ([mu_pat_intro]); the remaining semantic
      obligations (pattern equations, the comparison [1 < 3], and the final
      unsorted-result subtyping) are Admitted, as in round 2.
    - NOT derivable, although semantically true: [merge_paper_sorted_ty] and
      [merge_paper_ty].  Both require termination of [merge] on unboundedly
      deep recursion, which only T-Fix could provide, and the T-Fix premise
      of [merge] is semantically false in Rocq's denotation (finding F7 in
      the round-2 section: the self binding is vacuous on capabilities that
      contain the base case [xs = []]).

    Round-1 findings, re-examined with the round-2 rules:

    (F1) Matching on a demonic variable: now possible with [EXT_CtxCase]
      (split into "both", "nil only", "cons only").  It does not help inside
      T-Fix bodies because of F7.
    (F2) Dependent variables: resolved by [EXT_VarComma] (used below).
    (F3) Pattern-equation premise of list/tree matches: resolved by the
      paper-form [EXT_ListMatch*Named] rules (used below).  Round 2 used an
      UNSOUND earlier shape of these rules (premises under [Γ ,, Γpat],
      conclusion at [Γ]; see
      [ExtendedRuleSoundness.ext_list_match_cons_only_named_unsound]).  With
      the corrected rules the pattern bindings are introduced by
      [EXT_CtxSub] into the branch context, whose extension condition is
      exactly the missing semantic content; for the counterexample it is
      provable ([mu_pat_intro]: extend every model by the constant pattern
      values).
    (F4, paper-level) The literal type with [⊤] parameters does not witness
      the bug: a CORRECT merge also inhabits it ([merge [] l2 = l2], and [l2]
      ranges over unsorted lists); see [merge_nil_only_extended_type].  The
      meaningful disproof uses sorted parameters ([merge_paper_sorted_ty]);
      it is true for the buggy merge ([merge_safety_violated]).
    (F5) [U[b]] was trivial in round 1; [CaseTypes] now defines it
      faithfully ([q_base_all]).  [UAllList] below is now literally [U[List]].
    (F6) The pre-existing [merge_disprove_ty]
      ([O[List] → O[List] → OSortedList ⊕ UNotSortedList]) is false for
      merge: the singleton capability [l1 = l2 = []] yields the single
      result [[]], and [UNotSortedList] would have to reach every unsorted
      list.  The pre-existing [merge_safety_ty] is the paper's ✗ judgment
      (false, see [merge_safety_violated]).

    (F8) [EXT_FixUnrollNamed] is only sound for [fix_unroll_shape]
      targets (no top-level [-∗]/[⊕]/[□]); round 2 unrolled directly at the
      paper's [-∗] type.  This costs nothing here: [τx → τ <: τx -∗ τ] holds
      in general in the Rocq semantics ([mu_sub_arrow_to_wand], proved: a
      wand argument world only adds the fresh argument coordinate, and world
      compatibility makes the product a full-world extension), so the
      [-∗] form follows from the arrow form by [EXT_Sub].

    Also derived (round 1, still valid; structural derivations [Qed]):
    - [merge_nil_only_extended_type]: the whole [merge_program] at
      [{ν = []} → l2:[⊤] -∗ {¬sorted} ⊕ {⊤}].
    - [merge_step_witness_extended_type]: the buggy step under the
      counterexample's run-time context.
    - [merge_safety_violated] (operational, in the section above). *)

(** ** Generic helper lemmas (proposed for sharing)

    [merge_proj_over_top]: projecting any binding of base type [b] out of a
    context onto the singleton context [x ∷ O[b]];
    [merge_proj_star_r]: projecting the right binding of a star context. *)
Lemma merge_over_top_guard b x (m : WfWorld) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  m ⊨ ty_guard_formula
    (relevant_env (atom_env_to_lty_env (<[x := TBase b]> (∅ : gmap atom ty)))
      (CTOver b qual_top) (tret (vfvar x)))
    (CTOver b qual_top) (tret (vfvar x)).
Proof.
  intros Hworld_single.
  assert (Hworld :
    m ⊨ basic_world_formula
      (relevant_env (atom_env_to_lty_env (<[x := TBase b]> (∅ : gmap atom ty)))
        (CTOver b qual_top) (tret (vfvar x)))).
  {
    eapply basic_world_formula_subenv; [ | exact Hworld_single].
    intros v T Hlook.
    destruct v as [k|a].
    - unfold relevant_env, lty_env_restrict_lvars in Hlook.
      apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
      rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
      discriminate.
    - destruct (decide (a = x)) as [->|Hax].
      + unfold relevant_env, lty_env_restrict_lvars in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        rewrite atom_store_to_lvar_store_lookup_free in Hlook.
        unfold store_insert, store_empty in Hlook.
        rewrite lookup_insert in Hlook.
        rewrite decide_True in Hlook by reflexivity.
        transitivity (Some (TBase b)).
        * apply map_lookup_insert.
        * exact Hlook.
      + unfold relevant_env, lty_env_restrict_lvars in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        rewrite atom_store_to_lvar_store_lookup_free in Hlook.
        unfold store_insert, store_empty in Hlook.
        rewrite lookup_insert_ne in Hlook by congruence.
        rewrite lookup_empty in Hlook. discriminate.
  }
  assert (Hbasic :
    m ⊨ expr_basic_typing_formula
      (relevant_env (atom_env_to_lty_env (<[x := TBase b]> (∅ : gmap atom ty)))
        (CTOver b qual_top) (tret (vfvar x)))
      (tret (vfvar x)) (TBase b)).
  {
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc | ]. split; [exact Hscope | ].
    constructor. constructor.
    unfold relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2.
    - rewrite atom_store_to_lvar_store_lookup_free.
      unfold store_insert, store_empty.
      apply map_lookup_insert.
    - unfold relevant_lvars.
      cbn [tm_lvars tm_lvars_at value_lvars_at].
      unfold qual_top.
      cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars].
      apply elem_of_union_r.
      apply elem_of_singleton. reflexivity.
  }
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
    split; [exact Hlc | ]. split; [exact Hscope | ].
    eapply (basic_context_ty_lvars_mono (lvars_of_atoms ∅)).
    + intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      rewrite elem_of_empty in Ha. contradiction.
    + apply basic_context_ty_to_lvars.
      apply over_top_basic.
  - split; [exact Hworld | ]. split; [exact Hbasic | ].
    eapply expr_total_formula_tret_of_basic; eauto.
Qed.

Lemma merge_ctx_bind_over_top x b (m : WfWorld) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  m ⊨ ctx_denote_under ∅ (x ∷ over_ty b qual_top).
Proof.
  intros Hw.
  apply ctx_bind_from_base_denotation.
  - apply over_top_basic.
  - set_solver.
  - apply over_top_denotation_gas.
    exact (merge_over_top_guard b x m Hw).
Qed.

Lemma merge_proj_over_top Γ x b :
  wf_ctx_under ∅ Γ ->
  erase_ctx Γ !! x = Some (TBase b) ->
  ctx_sub_under ∅ (fv_tm (tret (vfvar x)) ∪ fv_cty (over_ty b qual_top))
    Γ (x ∷ over_ty b qual_top).
Proof.
  intros HΓ Hx.
  assert (HX : fv_tm (tret (vfvar x)) ∪ fv_cty (over_ty b qual_top) = {[x]}).
  { unfold over_ty, qual_top. cty_fv_syntax_norm. cbn [fv_tm fv_value qual_vars qual_lvars].
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_empty. set_solver. }
  rewrite HX.
  split; [exact HΓ | ]. split.
  { split; [set_solver | apply over_top_basic]. }
  split.
  { intros y Hy. apply elem_of_singleton in Hy. subst y.
    rewrite Hx. cbn [erase_ctx erase_ty]. symmetry. apply map_lookup_insert. }
  intros r Hr. exists (res_restrict r {[x]}). split; [reflexivity | ].
  apply merge_ctx_bind_over_top.
  pose proof (ctx_denote_under_basic_world ∅ Γ r Hr) as Hw.
  assert (Hw1 : r ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅)).
  { eapply basic_world_formula_subenv; [ | exact Hw].
    intros v T Hv. destruct (decide (v = LVFree x)) as [->|Hne].
    - rewrite lookup_insert in Hv. rewrite decide_True in Hv by reflexivity.
      inversion Hv; subst. unfold ctx_erasure_under.
      apply atom_env_to_lty_env_erase_ctx_union_subenv.
      + replace (dom (store_restrict (∅ : gmap atom ty) (ctx_fv Γ))) with (dom (∅ : gmap atom ty)).
        * exact HΓ.
        * first [reflexivity | vm_compute; reflexivity | (rewrite (storeA_restrict_empty (V:=ty)); reflexivity)].
      + rewrite atom_store_to_lvar_store_lookup_free. exact Hx.
    - rewrite lookup_insert_ne in Hv by congruence. rewrite lookup_empty in Hv. discriminate. }
  pose proof (res_models_restrict_fv r _ Hw1) as Hr1.
  rewrite formula_fv_basic_world_formula in Hr1.
  replace (lvars_fv (dom (<[LVFree x:=TBase b]> (∅ : gmap logic_var ty)))) with ({[x]} : aset) in Hr1.
  - exact Hr1.
  - rewrite lvar_store_lvars_fv_dom_insert_free, dom_empty_L, lvars_fv_empty. set_solver.
Qed.

Lemma merge_proj_star_r Γ1 x τ :
  wf_ctx_under ∅ (Γ1 ∗ (x ∷ τ)) ->
  wf_ctx_under ∅ (x ∷ τ) ->
  ctx_sub_under ∅ (fv_tm (tret (vfvar x)) ∪ fv_cty τ) (Γ1 ∗ (x ∷ τ)) (x ∷ τ).
Proof.
  intros HΓ Hx.
  split; [exact HΓ | ]. split; [exact Hx | ]. split.
  - intros y Hy. destruct HΓ as [HΓ1 [_ Hdisj]].
    cbn [erase_ctx].
    assert (Hfv : fv_cty τ ⊆ ∅).
    { destruct Hx as [_ Hτ]. pose proof (wf_context_ty_at_fv_subset 0 _ τ Hτ) as Hs.
      rewrite dom_empty_L in Hs. exact Hs. }
    assert (y = x) as -> .
    { cbn [fv_tm fv_value] in Hy. set_solver. }
    pose proof (basic_ctx_erase_dom (dom (∅ : gmap atom ty)) Γ1 HΓ1) as Hdom1.
    assert (Hnone : erase_ctx Γ1 !! x = None).
    { apply not_elem_of_dom. rewrite Hdom1. cbn [ctx_dom] in Hdisj. set_solver. }
    assert (Hs : ({[x := erase_ty τ]} : gmap atom ty) !! x = Some (erase_ty τ)).
    { first [apply lookup_singleton | apply map_lookup_singleton | vm_compute; reflexivity | rewrite lookup_singleton; reflexivity]. }
    rewrite Hs. apply map_lookup_union_Some_raw. right. split; [exact Hnone | exact Hs].
  - intros r Hr. exists r. split; [apply res_restrict_le | ].
    destruct (ctx_denote_under_star_elim _ _ _ _ Hr) as (m1 & m2 & Hc & Hle & H1 & H2).
    eapply res_models_kripke; [ | exact H2].
    etransitivity; [apply res_product_le_r | exact Hle].
Qed.


Lemma closed_ty_lc_fresh τ x :
  wf_context_ty_at 0 ∅ τ -> cty_lc_at 0 τ /\ x ∉ fv_cty τ.
Proof.
  intros Hwf. split.
  - exact (wf_context_ty_at_lc 0 ∅ τ Hwf).
  - intros Hx. pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hwf x Hx). set_solver.
Qed.

(** ** Types

    Paper [int]/[nat list] are Rocq [ℕ]/[List] (lists of naturals); the
    qualifier [sorted] is the non-strict order of [sorted_from] above, so
    [[1;3;2;4]] is unsorted and [[1;2]], [[3;4]] are sorted. *)

Definition ONotSortedList : context_ty := over_ty TList (q_not_sorted_list ν).
Definition USortedList : context_ty := under_ty TList (q_sorted_list ν).

(** Paper [[ν: nat list | ⊤]].  Round 1 used a local qualifier here because
    [U[List]] was trivial; [CaseTypes] now defines [U[List]] faithfully
    ([q_base_all TList], every list value), so [UAllList] is the shared
    alias.  [q_any_list] is kept for reference (semantically the same). *)
Definition q_any_list (v : value) : type_qualifier :=
  q_list_pred v (fun _ => True).
Definition UAllList : context_ty := U[ List ].

(** Paper result type [{ν | ¬sorted ν} ⊕ {ν | ⊤}] ("affine reachability"). *)
Definition merge_result_ty : context_ty := ONotSortedList ⊕ O[List].

(** Paper p. 23, literal: [l1:[⊤] -∗ l2:[⊤] -∗ {¬sorted} ⊕ {⊤}]. *)
Definition merge_paper_ty : context_ty := UAllList -∗ (UAllList -∗ merge_result_ty).

(** Paper p. 23, as described in the text (sorted angelic inputs). *)
Definition merge_paper_sorted_ty : context_ty :=
  USortedList -∗ (USortedList -∗ merge_result_ty).

(** Paper p. 23, the ✗ safety judgment
    [l1:{⊤} → l2:{⊤} → {ν | sorted ν}] (false; not typed). *)
Definition merge_paper_safety_ty : context_ty :=
  O[List] → (O[List] → OSortedList).

Lemma merge_paper_ty_wf : context_typing_wf ∅ Emp merge_program merge_paper_ty.
Proof.
  unfold context_typing_wf. split; [ | split ].
  - exact I.
  - unfold merge_paper_ty, UAllList, q_any_list, merge_result_ty, ONotSortedList,
      q_not_sorted_list, q_list_pred, q_const_pred.
    extended_wf_type.
  - exact merge_program_basic_type.
Qed.

Lemma merge_paper_sorted_ty_wf : context_typing_wf ∅ Emp merge_program merge_paper_sorted_ty.
Proof.
  unfold context_typing_wf. split; [ | split ].
  - exact I.
  - unfold merge_paper_sorted_ty, USortedList, q_sorted_list, merge_result_ty, ONotSortedList,
      q_not_sorted_list, q_list_pred, q_const_pred.
    extended_wf_type.
  - exact merge_program_basic_type.
Qed.

Lemma merge_paper_safety_ty_wf : context_typing_wf ∅ Emp merge_program merge_paper_safety_ty.
Proof.
  unfold context_typing_wf. split; [ | split ].
  - exact I.
  - unfold merge_paper_safety_ty, OSortedList, q_sorted_list, q_list_pred, q_const_pred.
    extended_wf_type.
  - exact merge_program_basic_type.
Qed.

(** ** Contexts of the typed fragments *)

(** Run-time context of the buggy step in [merge [1;2] [3;4]]:
    [h1 = 1], [h2 = 3], [t = merge [2] [4] = [2;4]] (all precise). *)
Definition Γw : ctx :=
  ((h1 ∷ const_precise_ty (cnat 1)) ,, (h2 ∷ const_precise_ty (cnat 3))) ,,
  (t ∷ const_precise_ty (clist cex_rec)).

Definition Γw1 : ctx := Γw ,, (lt12 ∷ binop_precise_ty bop_lt (avar h1) (avar h2)).
Definition Γw2 : ctx := Γw1 ,, (tail12 ∷ list_cons_precise_ty (avar h2) (avar t)).

(** Nil-only typing of merge (F1/F3): the first parameter is [{ν = []}]. *)
Definition q_nil_list (v : value) : type_qualifier :=
  q_list_pred v (fun l => l = []).

Definition merge_nil_only_ty : context_ty :=
  {: List | q_nil_list ν} → (UAllList -∗ merge_result_ty).

Definition merge_nil_self_ty : context_ty :=
  fix_rec_call_ty TList xs ({: List | q_nil_list ν}) (UAllList -∗ merge_result_ty).

Definition Γnil_body : ctx :=
  ((Emp ,, (xs ∷ {: List | q_nil_list ν})) ,, (merge_self ∷ merge_nil_self_ty))
    ∗ (ys ∷ UAllList).

Definition nil_list : list nat := nil.

(** ** Well-formedness automation *)

Ltac merge_atom_fact G a :=
  let r := eval vm_compute in (G !! a) in
  lazymatch r with
  | Some ?T => assert (G !! a = Some T) by (vm_compute; reflexivity)
  | None => assert (a ∉ dom G) by (apply not_elem_of_dom; vm_compute; reflexivity)
  end.

Ltac merge_basic :=
  lazymatch goal with
  | |- ?G ⊢ₑ ?e ⋮ ?T =>
      let T' := eval vm_compute in T in change (G ⊢ₑ e ⋮ T');
      merge_atom_fact G merge_self; merge_atom_fact G xs; merge_atom_fact G ys;
      merge_atom_fact G h1; merge_atom_fact G t1; merge_atom_fact G h2;
      merge_atom_fact G t2; merge_atom_fact G t; merge_atom_fact G lt12;
      merge_atom_fact G gt12; merge_atom_fact G tail12; merge_atom_fact G tail21;
      generalize dependent G; intros;
      unfold merge_step_tm in *; basic_type
  end.

Ltac merge_big_basic :=
  lazymatch goal with
  | |- ?G ⊢ₑ ?e ⋮ ?T =>
      let T' := eval vm_compute in T in
      lazymatch T' with
      | TBase TList =>
          change (G ⊢ₑ merge_rec_body ⋮ List);
          replace G with merge_env_match by (vm_compute; reflexivity);
          exact merge_match_basic
      | TArrow (TBase TList) (TArrow _ _) =>
          change (G ⊢ₑ merge_program ⋮ merge_basic_ty);
          replace G with (∅ : gmap atom ty) by (vm_compute; reflexivity);
          exact merge_program_basic_type
      | TArrow (TBase TList) (TBase TList) =>
          change (G ⊢ₑ ret (ƛ ys : List => merge_rec_body) ⋮ (List →ᵦ List));
          replace G with (<[merge_self:=merge_basic_ty]> (<[xs:=TBase TList]> (∅ : gmap atom ty)))
            by (vm_compute; reflexivity);
          exact merge_lam_ys_basic
      | TArrow (TArrow _ _) _ =>
          change (G ⊢ₑ ret (lam_named merge_self (TBase TList →ₜ (List →ᵦ List))
              (ret (ƛ ys : List => merge_rec_body))) ⋮ (merge_basic_ty →ᵦ List →ᵦ List));
          replace G with (<[xs:=TBase TList]> (∅ : gmap atom ty)) by (vm_compute; reflexivity);
          exact merge_lam_self_basic
      end
  end.

Ltac merge_atoms := unfold merge_self, DisproveMerge.merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in *.

Ltac mwf :=
  unfold Γw2, Γw1, Γw, UAllList, q_any_list, merge_result_ty, ONotSortedList, q_not_sorted_list,
    q_list_pred, q_const_pred in *;
  unfold context_typing_wf; repeat split;
  try solve [extended_wf_ctx | extended_wf_type | fast_set_solver!!];
  try solve [cbn [ctx_dom]; merge_atoms; set_solver];
  try solve [merge_basic].

Ltac mwf_big :=
  unfold UAllList, q_any_list, merge_result_ty, ONotSortedList, q_not_sorted_list,
    q_list_pred, q_const_pred in *;
  unfold context_typing_wf; repeat split;
  try solve [extended_wf_ctx | extended_wf_type | fast_set_solver!!];
  try solve [cbn [ctx_dom]; merge_atoms; set_solver];
  merge_big_basic.


Ltac mwf_big2 :=
  unfold Γnil_body, merge_nil_self_ty, merge_nil_only_ty, q_nil_list in *; mwf_big.

Ltac mwf2 :=
  unfold Γnil_body, merge_nil_self_ty, merge_nil_only_ty, q_nil_list in *; mwf.

Lemma Γnil_body_wf : wf_ctx_under ∅ Γnil_body.
Proof.
  unfold Γnil_body, merge_nil_self_ty, q_nil_list, UAllList, q_any_list, merge_result_ty,
    ONotSortedList, q_not_sorted_list, q_list_pred, q_const_pred, fix_rec_call_ty, mk_q_lt_base.
  unfold wf_ctx_under. cbn [basic_ctx ctx_dom].
  repeat split; try extended_wf_type; try (merge_atoms; set_solver).
Qed.

Lemma Γw2_wf : wf_ctx_under ∅ Γw2.
Proof.
  unfold Γw2, Γw1, Γw. unfold wf_ctx_under. cbn [basic_ctx ctx_dom].
  repeat split; try extended_wf_type; try (merge_atoms; set_solver).
Qed.

Lemma Γw1_wf : wf_ctx_under ∅ Γw1.
Proof. pose proof Γw2_wf as H. unfold Γw2, wf_ctx_under in H. cbn [basic_ctx] in H. tauto. Qed.

(** * (1) The maximal derivable typing of the whole program

    ∅; Emp ⊢ₓ merge_program ⋮ {ν = []} → l2:[all lists] -∗ {¬sorted} ⊕ {⊤}

    Semantic obligations: *)

(** Admitted.  Informal argument: [sub_type_under] asks, for every [e]
    with [erase Γnil_body ⊢ₑ e ⋮ List] and every world [m ⊨ Γnil_body] and
    extension [m' ⊒ m] with [m' ⊨ const_precise_ty [] e], that
    [m' ⊨ list_match_eq_ty xs e].  By the star elimination of
    [Γnil_body] and [xs ∷ {: List | ν = []}] (closed qualifier, so no
    fibering) every store of [m'] maps [xs] to [[]]; hence [xs]-fibering
    has the single fiber [xs = []].  The over part of [const_precise_ty []]
    says every result of [e] is [[]], the under part (plus totality from the
    guard) that [[]] is reached; on the fiber [xs = []] this is exactly
    [{ν = xs} ⊓ [ν = xs]].  The guard (well-formedness, basic typing of [e]
    in the relevant environment [{xs : List}], totality) is inherited. *)
Lemma merge_nil_only_obl_nil_eq :
  sub_type_under ∅ Γnil_body
    (const_precise_ty (clist nil_list)) (list_match_eq_ty (avar xs)).
Proof. Admitted.

Lemma merge_nil_only_obl_ctx_emp :
  ctx_sub_under ∅
    (fv_tm (ret (vconst (clist nil_list))) ∪ fv_cty (const_precise_ty (clist nil_list)))
    Γnil_body Emp.
Proof.
  unfold ctx_sub_under. split; [ | split; [ | split]].
  - exact Γnil_body_wf.
  - exact I.
  - intros x Hx. exfalso. clear - Hx.
    unfold const_precise_ty, precise_ty, over_ty, under_ty, mk_q_eq in Hx.
    cty_fv_syntax_norm_in Hx. cbn [qual_vars qual_lvars lvar_value_keys] in Hx.
    rewrite !lvars_fv_lvars_at_depth, !lvars_fv_union, !lvars_fv_singleton_bound,
      !lvars_fv_empty in Hx.
    set_solver.
  - intros r Hr. eexists. split; [reflexivity | ].
    cbn [ctx_denote_under].
    apply res_models_and_intro_from_models.
    + match goal with |- _ ⊨ basic_world_formula ?E =>
        replace E with (∅ : gmap logic_var ty) by (vm_compute; reflexivity) end.
      apply basic_world_formula_empty.
    + apply res_models_true.
Qed.

Lemma merge_nil_only_obl_proj_ys :
  ctx_sub_under ∅ (fv_tm (ret (avar ys)) ∪ fv_cty UAllList) Γnil_body (ys ∷ UAllList).
Proof.
  apply merge_proj_star_r.
  - exact Γnil_body_wf.
  - unfold wf_ctx_under, UAllList, q_any_list, q_list_pred, q_const_pred.
    cbn [basic_ctx]. split; [set_solver | extended_wf_type].
Qed.

(** Admitted.  Informal argument (context independent, closed types):
    if [m' ⊨ UAllList e], the result-extended world [m'ν] has a
    sub-world whose [ν]-projection is EXACTLY the set of all list constants
    ([U[List]] = [under_ty TList (q_base_all TList)] mentions [ν]), so some
    store of [m'ν] has an unsorted
    result, e.g. [[1;0]].  Take [m1] = the stores of [m'ν] whose result is
    unsorted (non-empty) and [m2] = [m'ν]; then [res_sum m1 m2 = m'ν], [m1]
    satisfies the over type [{¬sorted}] on its (closed, unfibered)
    qualifier and [m2] satisfies [O[List]] (trivial).  Guards (typing of
    [ret ν], totality) hold since [ν] is bound to list values.  Hence
    [m' ⊨ merge_result_ty e].  (With the round-1 trivial
    [U[List]] = [under_ty TList qual_top] this obligation would be FALSE,
    e.g. for [e = ret []].) *)
Lemma merge_nil_only_obl_reach :
  sub_type_under ∅ Γnil_body UAllList merge_result_ty.
Proof. Admitted.

Lemma merge_nil_only_extended_type : ∅; Emp ⊢ₓ merge_program ⋮ merge_nil_only_ty.
Proof.
  rewrite merge_program_unfold. unfold merge_fix_value, merge_nil_only_ty.
  change (ret (fixfun_named merge_self xs (TBase TList) (List →ᵦ List) ?b))
    with (ret (fixfun_named merge_self xs (TBase TList) (List →ᵦ List) b)).
  assert (Hcl : wf_context_ty_at 0 ∅ (UAllList -∗ merge_result_ty))
    by (unfold UAllList, q_any_list, merge_result_ty, ONotSortedList, q_not_sorted_list,
          q_list_pred, q_const_pred; extended_wf_type).
  eapply EXT_FixNamed.
  - reflexivity.
  - mwf_big2.
  - assert (Hopen : open_one 0 xs (UAllList -∗ merge_result_ty) = (UAllList -∗ merge_result_ty)).
    { destruct (closed_ty_lc_fresh _ xs Hcl) as [Hlc Hfr].
      apply (cty_open_above_lc_fresh 0 0); [lia | exact Hlc | exact Hfr]. }
    rewrite Hopen.
    eapply EXT_LamNamedErased.
    + reflexivity.
    + mwf_big2.
    + eapply EXT_LamDNamedErased.
      * reflexivity.
      * mwf_big2.
      * fold merge_nil_self_ty. fold Γnil_body.
        unfold match_list_named. eapply EXT_ListMatchNilOnly.
        -- mwf_big2.
        -- eapply EXT_Sub with (τ1 := const_precise_ty (clist nil_list)).
           ++ mwf2.
           ++ eapply EXT_CtxSub with (Γ2 := Emp).
              ** mwf2.
              ** eapply EXT_Const. mwf2.
              ** exact merge_nil_only_obl_ctx_emp.
           ++ exact merge_nil_only_obl_nil_eq.
        -- eapply EXT_Sub with (τ1 := UAllList).
           ++ mwf2.
           ++ eapply EXT_CtxSub with (Γ2 := ys ∷ UAllList).
              ** mwf2.
              ** eapply EXT_Var. mwf2.
              ** exact merge_nil_only_obl_proj_ys.
           ++ exact merge_nil_only_obl_reach.
Qed.

(** * (2) The buggy step under the counterexample's run-time context

    ∅; Γw ⊢ₓ merge_step_tm ⋮ {¬sorted} ⊕ {⊤}

    Semantic obligations: *)

(** Admitted.  Informal argument: let [r ⊨ Γw1].  The over parts of
    [h1 ∷ const_precise_ty 1] and [h2 ∷ const_precise_ty 3] (closed
    qualifiers [ν = c]) force [h1 = 1], [h2 = 3] in every store.
    [binop_precise_ty bop_lt h1 h2] is fibered over [{h1, h2}]; on the only
    fiber [(1, 3)] its over part forces [lt12 ∈ {c' | bin_step bop_lt 1 3 c'}
    = {true}].  So [r' := r|{lt12}] is the non-empty world [{[lt12 ↦ true]}]
    and [r|X ⊑ r'] holds with [X = {lt12}].  [r'] satisfies
    [lt12 ∷ bool_precise_ty true] (= [const_precise_ty (cbool true)]): the
    over part since all values are [true], the under part since [true] is
    present, the guard since [lt12] is a boolean and [ret lt12] is total. *)
Lemma merge_step_witness_obl_lt_true :
  ctx_sub_under ∅ (fv_tm (ret (avar lt12)) ∪ fv_cty (bool_precise_ty true))
    Γw1 (lt12 ∷ bool_precise_ty true).
Proof. Admitted.

Lemma merge_step_witness_obl_proj_h2 :
  ctx_sub_under ∅ (fv_tm (ret (avar h2)) ∪ fv_cty ONat) Γw1 (h2 ∷ ONat).
Proof.
  apply (merge_proj_over_top Γw1 h2 TNat).
  - exact Γw1_wf.
  - vm_compute. reflexivity.
Qed.

Lemma merge_step_witness_obl_proj_t :
  ctx_sub_under ∅ (fv_tm (ret (avar t)) ∪ fv_cty OList) Γw1 (t ∷ OList).
Proof.
  apply (merge_proj_over_top Γw1 t TList).
  - exact Γw1_wf.
  - vm_compute. reflexivity.
Qed.

Lemma merge_step_witness_obl_proj_h1 :
  ctx_sub_under ∅ (fv_tm (ret (avar h1)) ∪ fv_cty ONat) Γw2 (h1 ∷ ONat).
Proof.
  apply (merge_proj_over_top Γw2 h1 TNat).
  - exact Γw2_wf.
  - vm_compute. reflexivity.
Qed.

Lemma merge_step_witness_obl_proj_tail12 :
  ctx_sub_under ∅ (fv_tm (ret (avar tail12)) ∪ fv_cty OList) Γw2 (tail12 ∷ OList).
Proof.
  apply (merge_proj_over_top Γw2 tail12 TList).
  - exact Γw2_wf.
  - vm_compute. reflexivity.
Qed.

(** Admitted.  Informal argument: let [m ⊨ Γw2], [m' ⊒ m] and
    [m' ⊨ list_cons_precise_ty h1 tail12 e].  As in the previous
    obligation, every store of [m'] has [h1 = 1], [h2 = 3], [t = [2;4]],
    and the over part of [tail12 ∷ list_cons_precise_ty h2 t] (fibered over
    [{h2, t}], single fiber) forces [tail12 = [3;2;4]].  The over part of
    the hypothesis, on the single [{h1, tail12}] fiber, forces every result
    of [e] to be [1 :: [3;2;4] = [1;3;2;4]], which is unsorted
    ([cex_out_not_sorted]); totality makes the result world non-empty.
    Hence the sum split [m1 = m2 = m'ν] (the whole result-extended world)
    witnesses [{¬sorted} ⊕ {⊤}]: [m1] satisfies the closed over qualifier
    [¬sorted ν], [m2] satisfies [O[List]], and [res_sum m1 m2 = m'ν]. *)
Lemma merge_step_witness_obl_unsorted :
  sub_type_under ∅ Γw2 (list_cons_precise_ty (avar h1) (avar tail12)) merge_result_ty.
Proof. Admitted.

Lemma merge_step_witness_extended_type :
  ∅; Γw ⊢ₓ merge_step_tm ⋮ merge_result_ty.
Proof.
  unfold merge_step_tm.
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_lt (avar h1) (avar h2)).
  - mwf.
  - eapply EXT_BinOp. mwf.
  - fold Γw1. unfold if_named.
    eapply EXT_MatchTrueOnly.
    + mwf.
    + eapply EXT_CtxSub with (Γ2 := lt12 ∷ bool_precise_ty true).
      * mwf.
      * eapply EXT_Var. mwf.
      * exact merge_step_witness_obl_lt_true.
    + eapply EXT_LetNamed with (τ1 := list_cons_precise_ty (avar h2) (avar t)).
      * mwf.
      * eapply EXT_ListCons.
        -- mwf.
        -- eapply EXT_CtxSub with (Γ2 := h2 ∷ ONat);
             [mwf | eapply EXT_Var; mwf | exact merge_step_witness_obl_proj_h2].
        -- eapply EXT_CtxSub with (Γ2 := t ∷ OList);
             [mwf | eapply EXT_Var; mwf | exact merge_step_witness_obl_proj_t].
      * fold Γw2.
        eapply EXT_Sub with (τ1 := list_cons_precise_ty (avar h1) (avar tail12)).
        -- mwf.
        -- eapply EXT_ListCons.
           ++ mwf.
           ++ eapply EXT_CtxSub with (Γ2 := h1 ∷ ONat);
                [mwf | eapply EXT_Var; mwf | exact merge_step_witness_obl_proj_h1].
           ++ eapply EXT_CtxSub with (Γ2 := tail12 ∷ OList);
                [mwf | eapply EXT_Var; mwf | exact merge_step_witness_obl_proj_tail12].
        -- exact merge_step_witness_obl_unsorted.
Qed.

(** * The "carefully crafted context" of p. 23 (counterexample, ✗)

    The paper's program
      let l1 = sorted_list_gen () in
      let l2 = match l1 with [] -> sorted_list_gen () | _ -> [] in
      merge l1 l2
    corresponds to the entangled context [Γhide] ([l2]'s angelic range
    depends on [l1]).  Every pair it admits has [l1 = []] or [l2 = []], so
    [merge l1 l2] always returns one of its (sorted) inputs and
    [merge l1 l2 ⋮ merge_result_ty] is FALSE under [Γhide]: no non-empty
    sub-capability has unsorted results.  This is why the disproof type
    uses the separating arrow [-∗] for [l2].  The language has no list
    generator primitive, so the program itself is not expressible; we only
    record the context and check that it is well formed. *)

Definition l1 : atom := 52%positive.
Definition l2 : atom := 53%positive.

Definition q_hide_l2 (v : value) : type_qualifier :=
  tqual (lvar_value_keys v ∪ lvar_value_keys (avar l1))
    (fun σ =>
       exists a b,
         denote_lvar_value (lso_store σ) v = Some (vconst (clist a)) /\
         denote_lvar_value (lso_store σ) (avar l1) = Some (vconst (clist b)) /\
         ((b = nil /\ sorted a) \/ (b <> nil /\ a = nil))).

Definition Γhide : ctx :=
  (l1 ∷ USortedList) ,, (l2 ∷ under_ty TList (q_hide_l2 ν)).

Lemma Γhide_wf : wf_ctx_under ∅ Γhide.
Proof.
  unfold Γhide, USortedList, q_sorted_list, q_hide_l2, q_list_pred, q_const_pred.
  unfold wf_ctx_under. cbn [basic_ctx ctx_dom].
  repeat split; try extended_wf_type; try (unfold l1, l2; set_solver).
Qed.

(** * Round 2/3: disproof of [merge] by unrolling (paper §6, Fig. 8)

    Main result ([merge_cex_extended_type], structural derivation [Qed]):

      ∅; Emp ⊢ₓ merge_program ⋮
        l1:([ν = [1;2]] ⊓ {ν = [1;2]}) -∗ l2:([ν = [3;4]] ⊓ {ν = [3;4]}) -∗
        {ν: nat list | ¬sorted ν} ⊕ {ν: nat list | ⊤}

    i.e. the paper's disproof type with the angelic parameter ranges
    instantiated to the counterexample (precise singleton capabilities,
    [mu_Pc c = const_precise_ty (clist c)]).  The derivation follows the
    incorrectness-style plan: [EXT_FixUnrollNamed] unfolds [merge] at the
    outer call ([merge [1;2] [3;4]]) and again for the two recursive calls
    ([mu_fix24 : merge [2] [4] = [2;4]], [mu_fix00 : merge [] [] = []]).
    All unrolling targets are [fix_unroll_shape] (top-level [→]); the outer
    one is [merge_cex_extended_arrow_type] at
    [mu_cex_arrow_ty = l1 → l2 -∗ {¬sorted} ⊕ {⊤}] (the [-∗] of [l2] sits
    under the arrow), and [merge_cex_extended_type] follows by [EXT_Sub]
    with the proved [mu_cex_obl_arrow_wand] (generic [τx → τ <: τx -∗ τ]).
    The matches use the corrected [EXT_ListMatchConsOnlyNamed] (and
    [EXT_ListMatchNilOnly] at the base): before each match, [EXT_CtxSub]
    moves to a branch context that itself binds the pattern variables with
    closed constant over types (e.g. [GA1 = (GA0 ,, h1 ∷ {ν = 2}) ,,
    t1 ∷ {ν = []}]); this pattern introduction is proved ([mu_pat_intro]),
    and the pattern equation [h1 :: t1 : {ν = xs} ⊓ [ν = xs]] is checked in
    that same context.  The recursive call [merge t1 t2] is typed with
    [EXT_Let]/[EXT_AppFun] on the unrolled closed value, variables with
    [EXT_VarComma]/[EXT_Var] plus [EXT_CtxSub], and the buggy step (Fig. 8
    line 7) with [EXT_MatchTrueOnly].

    Why the paper's own ranges ([l1, l2 : [ν | sorted ν]] or [[⊤]]) are NOT
    derivable although the type is semantically true (finding F7):

    (F7, T-Fix self binding is vacuous on mixed capabilities.)  The binding
      [self ∷ (a : {φx ∧ ν ≺ x}) → τ] added by [EXT_Fix]/[EXT_FixNamed] is
      denoted by an arrow formula that quantifies over whole-world
      extensions with an argument [a] whose (fibered, over-approximate)
      argument formula must hold on EVERY [x]-fiber.  On a fiber with no
      [≺]-smaller [φx]-value (for lists: [x = []]) it fails, so the
      implication is vacuous and ANY function value (even a diverging one)
      satisfies the self binding.  Concretely,
      [r = {[xs ↦ []], [xs ↦ [5]]} ⊨ xs ∷ {List | ⊤}], and [r] extended with
      [self := fix f. λa. f a] satisfies [self ∷ fix_rec_call_ty ..].  The
      T-Fix premise of [merge] then demands that [λys. body] be total on the
      [[5]]-fiber with [ys = [7]], but the body calls [self [] []], which
      diverges; every [ty_denote] contains the totality guard, so the premise
      is semantically FALSE for every result type and every [φx] that admits
      a list on which the body recurses.  Hence (the rules being sound) no
      typing of [merge] by T-Fix exists.  The disproof type with ranges
      [[sorted]] or [[⊤]] needs termination of [merge] on every pair of its
      (unbounded) input capabilities ([U] types mean "at least these
      values", and the result guard requires totality on every store), i.e.
      on unbounded recursion depth; [EXT_FixUnrollNamed] unfolds one level
      per use and [EXT_Sub]/[EXT_CtxSub]/[EXT_CtxCase] do not change the
      term, so a finite derivation would need a T-Fix node for [merge].  The
      "strengthened signature" route ([{⊤} → {⊤} → {ν = mspec l1 l2}] by
      T-Fix, then T-Sub) fails at the same premise ([mspec] below is the
      Rocq functional specification of the buggy merge).  [EXT_CtxCase]
      cannot repair this: a nil/cons split of [r] would need the cons part
      to satisfy the self binding, which [r] does not constrain.  Possible
      fix: interpret the self binding (or arrows) fiberwise, e.g. an
      [FFibVars] over the free variables of the argument type around the
      arrow's [FForall], or a T-Fix premise over single-[x]-fiber
      capabilities. *)

(** ** Functional specification of the (buggy) merge

    [mspec] mirrors [merge_program] (same branch order and comparisons).  It
    is the specification of the "strengthened signature" route discussed in
    F7 ([{⊤} → {⊤} → {ν = mspec l1 l2}] by T-Fix, then T-Sub), which is not
    derivable; it is kept to state the counterexample computation. *)

Fixpoint mspec (a b : list nat) : list nat :=
  match a with
  | [] => b
  | h1 :: t1 =>
      match b with
      | [] => a
      | h2 :: t2 =>
          match Nat.ltb h1 h2 with
          | true => h1 :: h2 :: mspec t1 t2
          | false =>
              match Nat.ltb h2 h1 with
              | true => h2 :: h1 :: mspec t1 t2
              | false => h1 :: mspec t1 t2
              end
          end
      end
  end.

Lemma mspec_cex : mspec cex_l1 cex_l2 = cex_out.
Proof. reflexivity. Qed.

Definition merge_fixed_atoms : aset :=
  {[merge_self]} ∪ {[xs]} ∪ {[ys]} ∪ {[h1]} ∪ {[t1]} ∪ {[h2]} ∪ {[t2]} ∪ {[t]} ∪
  {[lt12]} ∪ {[gt12]} ∪ {[tail12]} ∪ {[tail21]}.


(** ** Types of the unrolling derivation *)

Definition mu_Oc (l : list nat) : context_ty := {: List | mk_q_eq ν (vconst (clist l)) }.
Definition mu_On (n : nat) : context_ty := {: ℕ | mk_q_eq ν (vconst (cnat n)) }.
Definition mu_Pc (l : list nat) : context_ty := const_precise_ty (clist l).

(** Inner unrollings: [merge [2] [4] = [2;4]] and [merge [] [] = []]. *)
Definition mu_T4 : context_ty := mu_Oc (4%nat :: nil) → mu_Oc cex_rec.
Definition mu_T24 : context_ty := mu_Oc (2%nat :: nil) → mu_T4.
Definition mu_T0 : context_ty := mu_Oc nil → mu_Oc nil.
Definition mu_T00 : context_ty := mu_Oc nil → mu_T0.

(** The counterexample instance of the paper's disproof type:
    l1:[ν = [1;2]] -∗ l2:[ν = [3;4]] -∗ {ν | ¬sorted ν} ⊕ {ν | ⊤}. *)
Definition mu_cex_ty : context_ty :=
  mu_Pc cex_l1 -∗ (mu_Pc cex_l2 -∗ merge_result_ty).

(** The form actually derived by unrolling: [EXT_FixUnrollNamed] needs a
    [fix_unroll_shape] target (no top-level [-∗]), so the outer parameter is
    an arrow; the [-∗] of the second parameter sits under that arrow, which
    is allowed.  [mu_cex_ty] is then obtained by [EXT_Sub]
    ([mu_cex_obl_arrow_wand]). *)
Definition mu_cex_arrow_ty : context_ty :=
  mu_Pc cex_l1 → (mu_Pc cex_l2 -∗ merge_result_ty).

Ltac mu_ctx_hook := idtac.

Ltac m2_in :=
  first
    [ apply elem_of_singleton; reflexivity
    | apply elem_of_union_l; m2_in
    | apply elem_of_union_r; m2_in ].

Ltac m2_neq :=
  first
    [ solve [congruence]
    | solve [vm_compute; congruence]
    | let Heq := fresh "Heq" in intro Heq;
      first [ rewrite Heq in * | rewrite <- Heq in * ];
      unfold merge_fixed_atoms in *;
      match goal with
      | H : ?z ∉ ?S |- False => apply H; m2_in
      end ].

Lemma m2_lookup_union (m1 m2 : gmap atom ty) i :
  (m1 ∪ m2) !! i = match m1 !! i with Some v => Some v | None => m2 !! i end.
Proof.
  destruct (m1 !! i) eqn:E.
  - apply map_lookup_union_Some_raw. left. exact E.
  - destruct (m2 !! i) eqn:E2.
    + apply map_lookup_union_Some_raw. right. split; assumption.
    + apply map_lookup_union_None. split; assumption.
Qed.

Lemma m2_lk_single (x : atom) (T : ty) : ({[x := T]} : gmap atom ty) !! x = Some T.
Proof. apply map_lookup_singleton. Qed.
Lemma m2_lk_single_ne (x z : atom) (T : ty) : z <> x -> ({[x := T]} : gmap atom ty) !! z = None.
Proof. apply map_lookup_singleton_ne. Qed.
Lemma m2_lk_empty (z : atom) : (∅ : gmap atom ty) !! z = None.
Proof. apply lookup_empty. Qed.

Lemma m2_lk_ins (x : atom) (T : ty) (m : gmap atom ty) : (<[x := T]> m) !! x = Some T.
Proof. apply map_lookup_insert. Qed.
Lemma m2_lk_ins_ne (x z : atom) (T : ty) (m : gmap atom ty) : z <> x -> (<[x := T]> m) !! z = m !! z.
Proof. apply map_lookup_insert_ne. Qed.

Ltac m2_eval_lookup :=
  mu_ctx_hook;
  cbn [erase_ctx];
  rewrite ?m2_lookup_union;
  repeat first
    [ rewrite m2_lk_single
    | rewrite m2_lk_single_ne by m2_neq
    | rewrite m2_lk_empty
    | rewrite m2_lk_ins
    | rewrite m2_lk_ins_ne by m2_neq ];
  cbn [erase_ty]; reflexivity.

Ltac m2_fact G a :=
  let H := fresh "Hlk" in
  eassert (H : G !! a = _) by m2_eval_lookup;
  lazymatch type of H with
  | _ = None => apply not_elem_of_dom in H
  | _ => idtac
  end.

Lemma m2_dom_comma Γ1 Γ2 :
  dom (erase_ctx (CtxComma Γ1 Γ2)) = dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2).
Proof. cbn [erase_ctx]. apply dom_union_L. Qed.
Lemma m2_dom_star Γ1 Γ2 :
  dom (erase_ctx (CtxStar Γ1 Γ2)) = dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2).
Proof. cbn [erase_ctx]. apply dom_union_L. Qed.
Lemma m2_dom_sum Γ1 Γ2 : dom (erase_ctx (CtxSum Γ1 Γ2)) = dom (erase_ctx Γ1).
Proof. reflexivity. Qed.
Lemma m2_dom_emp : dom (erase_ctx CtxEmpty) = (∅ : aset).
Proof. cbn [erase_ctx]. apply dom_empty_L. Qed.

Ltac m2_dom_norm :=
  repeat first [ rewrite m2_dom_comma | rewrite m2_dom_star | rewrite m2_dom_sum
               | rewrite m2_dom_emp | rewrite erase_ctx_bind_dom ].

Ltac m2_set :=
  mu_ctx_hook; m2_dom_norm; cbn [ctx_dom] in *;
  unfold merge_fixed_atoms in *; set_solver.

Ltac m2_unfold_tys :=
  unfold mu_Oc, mu_On, mu_Pc, merge_result_ty, ONotSortedList, q_not_sorted_list,
    mu_T24, mu_T00, mu_T4, mu_T0, mu_cex_ty, mu_cex_arrow_ty,
    q_list_pred, q_const_pred, mk_q_lt_base,
    ONat, OList, OBool, qual_top, mk_q_eq, vnu,
    binop_precise_ty, binop_result_qual, list_cons_precise_ty, list_cons_result_qual,
    list_match_eq_ty, const_precise_ty, bool_precise_ty, bool_qual, precise_ty,
    over_ty, under_ty in *;
  cbn [bin_op_type base_ty_of_const] in *.

Ltac m2_lvars_wf :=
  unfold lvars_wf_at;
  let Hlv := fresh "Hlv" in
  intros [?|?] Hlv; cbn [lvar_wf_at]; set_unfold in Hlv;
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
  repeat match goal with
         | H : LVBound _ = LVBound _ |- _ => inversion H; subst; clear H
         | H : LVFree _ = LVFree _ |- _ => inversion H; subst; clear H
         | H : LVBound _ = LVFree _ |- _ => discriminate H
         | H : LVFree _ = LVBound _ |- _ => discriminate H
         | H : False |- _ => destruct H
         end;
  first [ lia | m2_set ].

Ltac m2_wf_type_core :=
  m2_unfold_tys;
  unfold basic_context_ty;
  cbn [wf_context_ty_at erase_ty qual_vars qual_lvars lvar_value_keys] in *;
  repeat split; try reflexivity; m2_lvars_wf.

Lemma mu_closed_fv τ : wf_context_ty_at 0 ∅ τ -> fv_cty τ = ∅.
Proof.
  intros Hwf. pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hwf). set_solver.
Qed.

Lemma mu_closed_open k x τ : wf_context_ty_at 0 ∅ τ -> cty_open k x τ = τ.
Proof.
  intros Hwf. destruct (closed_ty_lc_fresh τ x Hwf) as [Hlc Hfr].
  apply (cty_open_above_lc_fresh 0 k); [lia | exact Hlc | exact Hfr].
Qed.

Ltac m2_wf_type :=
  repeat match goal with
  | |- context[@open_one atom context_ty open_cty_atom_inst ?k ?x ?τ] =>
      change (@open_one atom context_ty open_cty_atom_inst k x τ) with (cty_open k x τ)
  end;
  repeat match goal with
  | |- context[cty_open ?k ?x ?τ] => rewrite (mu_closed_open k x τ) by m2_wf_type_core
  end;
  m2_wf_type_core.

Ltac m2_wf_goal :=
  lazymatch goal with
  | |- True => exact I
  | |- _ ∉ _ => m2_set
  | |- _ ## _ => m2_set
  | |- _ ⊆ _ => m2_set
  | |- @eq aset _ _ => m2_set
  | |- erase_ty _ = erase_ty _ => m2_unfold_tys; cbn [erase_ty]; reflexivity
  | |- _ = _ => reflexivity
  | |- _ => m2_wf_type
  end.

Ltac m2_wf_ctx :=
  mu_ctx_hook; unfold wf_ctx_under; cbn [basic_ctx] in *; repeat split; m2_wf_goal.


(** ** Basic typing of the opened body (renaming the [ys] binder) *)

Definition E01 : gmap atom ty := <[merge_self:=merge_basic_ty]> (<[xs:=TBase TList]> ∅).

Definition E_inner : tm :=
  let_named t (call2_tm (vfvar merge_self) (vfvar t1) (vfvar t2)) merge_step_tm.

Definition inner_at (y : atom) : tm :=
  match_list_named (vfvar y) (ret (vfvar xs)) h2 t2 E_inner.


Definition E02 : gmap atom ty := <[t1 := TBase TList]> (<[h1 := TBase TNat]> E01).
Definition E03 : gmap atom ty := <[t2 := TBase TList]> (<[h2 := TBase TNat]> E02).

Lemma m2_notin_ins (x z : atom) (T : ty) (m : gmap atom ty) :
  z <> x -> z ∉ dom m -> z ∉ dom (<[x := T]> m).
Proof.
  intros Hne Hz. apply not_elem_of_dom. rewrite m2_lk_ins_ne by exact Hne.
  apply not_elem_of_dom. exact Hz.
Qed.

Lemma BT_Einner_gen (G : gmap atom ty) :
  G !! merge_self = Some merge_basic_ty -> G !! t1 = Some (TBase TList) ->
  G !! t2 = Some (TBase TList) -> G !! h1 = Some (TBase TNat) -> G !! h2 = Some (TBase TNat) ->
  t ∉ dom G -> lt12 ∉ dom G -> tail12 ∉ dom G -> gt12 ∉ dom G -> tail21 ∉ dom G ->
  G ⊢ₑ E_inner ⋮ List.
Proof.
  intros Hm Ht1 Ht2 Hh1 Hh2 Ht Hlt Htl Hgt Htr.
  unfold E_inner. eapply basic_typing_let_named; [exact Ht | | ].
  - unfold call2_tm, case_app. eapply basic_typing_tapp_tm.
    + eapply TT_App; [constructor; exact Hm | constructor; exact Ht1].
    + constructor. exact Ht2.
  - apply merge_step_basic.
    + rewrite m2_lk_ins_ne by m2_neq. exact Hh1.
    + rewrite m2_lk_ins_ne by m2_neq. exact Hh2.
    + apply m2_lk_ins.
    + apply m2_notin_ins; [m2_neq | assumption].
    + apply m2_notin_ins; [m2_neq | assumption].
    + apply m2_notin_ins; [m2_neq | assumption].
    + apply m2_notin_ins; [m2_neq | assumption].
Qed.

Ltac m2_lookup :=
  repeat (rewrite m2_lk_ins_ne by m2_neq); first [apply m2_lk_ins | reflexivity].

Lemma BT_inner_ys : <[ys := TBase TList]> E02 ⊢ₑ inner_at ys ⋮ List.
Proof.
  unfold inner_at, match_list_named.
  eapply TT_ListMatch with (L := {[merge_self]} ∪ {[xs]} ∪ {[ys]} ∪ {[h1]} ∪ {[t1]} ∪ {[t]} ∪
      {[lt12]} ∪ {[gt12]} ∪ {[tail12]} ∪ {[tail21]}).
  - constructor. apply m2_lk_ins.
  - constructor. constructor. unfold E02, E01. vm_compute. reflexivity.
  - intros hd2 tl2 Hhd2 Htl2.
    unfold E_inner, merge_step_tm, let_named, call2_tm, tapp_tm, case_app, if_named, cons_tm, Ret.
    unfold E02, E01, merge_basic_ty in *.
    unfold merge_self, DisproveMerge.merge, xs, ys, h1, t1, h2, t2, t, lt12, gt12, tail12, tail21 in *.
    simpl.
    repeat progress basic_type_surface_norm.
    eapply TT_Let with (L := ({[40%positive]} ∪ {[43%positive]} ∪ {[44%positive]} ∪ {[hd2]} ∪ {[tl2]})) (T1 := TBase TList).
    { eapply TT_Let with (L := ({[40%positive]} ∪ {[43%positive]} ∪ {[44%positive]} ∪ {[hd2]} ∪ {[tl2]}))
        (T1 := (List →ᵦ List)).
      { eapply TT_App.
        { eapply VT_FVar. m2_lookup. }
        { eapply VT_FVar. m2_lookup. } }
      { intros f Hf. simpl.
        eapply TT_App.
        { eapply VT_FVar. m2_lookup. }
        { eapply VT_FVar. m2_lookup. } } }
    { intros mt Hmt.
      simpl.
      eapply TT_Let with (L := ({[40%positive]} ∪ {[43%positive]} ∪ {[44%positive]} ∪ {[hd2]} ∪ {[tl2]} ∪ {[mt]}))
        (T1 := 𝔹).
      { eapply TT_BinOp.
        { reflexivity. }
        { eapply VT_FVar. m2_lookup. }
        { eapply VT_FVar. m2_lookup. } }
      { intros mlt Hmlt. simpl.
        eapply TT_Match.
        { basic_type. }
        { eapply TT_Let with (L := ({[40%positive]} ∪ {[43%positive]} ∪ {[44%positive]} ∪ {[hd2]} ∪ {[tl2]} ∪ {[mt]} ∪ {[mlt]}))
            (T1 := TBase TList).
          { eapply TT_ListCons.
            { eapply VT_FVar. m2_lookup. }
            { eapply VT_FVar. m2_lookup. } }
          { intros mtail Hmtail. simpl.
            eapply TT_ListCons.
            { eapply VT_FVar. m2_lookup. }
            { eapply VT_FVar. m2_lookup. } } }
        { eapply TT_Let with (L := ({[40%positive]} ∪ {[43%positive]} ∪ {[44%positive]} ∪ {[hd2]} ∪ {[tl2]} ∪ {[mt]} ∪ {[mlt]}))
            (T1 := 𝔹).
          { eapply TT_BinOp.
            { reflexivity. }
            { eapply VT_FVar. m2_lookup. }
            { eapply VT_FVar. m2_lookup. } }
          { intros mgt Hmgt. simpl.
            eapply TT_Match.
            { basic_type. }
            { eapply TT_Let with (L := ({[40%positive]} ∪ {[43%positive]} ∪ {[44%positive]} ∪ {[hd2]} ∪ {[tl2]} ∪ {[mt]} ∪ {[mlt]} ∪ {[mgt]}))
                (T1 := TBase TList).
              { eapply TT_ListCons.
                { eapply VT_FVar. m2_lookup. }
                { eapply VT_FVar. m2_lookup. } }
              { intros mtail2 Hmtail2. simpl.
                eapply TT_ListCons.
                { eapply VT_FVar. m2_lookup. }
                { eapply VT_FVar. m2_lookup. } } }
            { eapply TT_ListCons; eapply VT_FVar; m2_lookup. } } } } }
Qed.

Lemma m2_ins_subseteq (a : atom) (T : ty) (m G : gmap atom ty) :
  G !! a = Some T -> m ⊆ G -> <[a := T]> m ⊆ G.
Proof. intros Ha Hm. apply insert_subseteq_l; assumption. Qed.

Lemma m2_empty_subseteq (G : gmap atom ty) : (∅ : gmap atom ty) ⊆ G.
Proof. apply map_empty_subseteq. Qed.

Lemma m2_empty_subseteq2 (G : gmap atom ty) :
  @subseteq (gmap atom ty) (@map_subseteq atom (gmap atom) (@gmap_lookup atom _ _) ty)
    (@empty (gmap atom ty) (@store_empty ty)) G.
Proof. apply map_subseteq_spec. intros i x Hi. vm_compute in Hi. discriminate. Qed.

Ltac m2_subseteq :=
  unfold E03, E02, E01 in *;
  repeat (first [eapply insert_subseteq_l | eapply m2_ins_subseteq]; [m2_eval_lookup | ]);
  first [apply m2_empty_subseteq2 | apply m2_empty_subseteq | apply map_empty_subseteq].

Ltac m2_facts_basic :=
  lazymatch goal with
  | |- ?G ⊢ₑ ?e ⋮ ?T =>
      let T' := eval vm_compute in T in change (G ⊢ₑ e ⋮ T');
      repeat match goal with
      | a : atom |- _ =>
          lazymatch goal with
          | H : G !! a = _ |- _ => fail
          | H : a ∉ dom G |- _ => fail
          | _ => m2_fact G a
          end
      end;
      m2_fact G merge_self; m2_fact G xs; m2_fact G ys; m2_fact G h1; m2_fact G t1;
      m2_fact G h2; m2_fact G t2; m2_fact G t; m2_fact G lt12; m2_fact G gt12;
      m2_fact G tail12; m2_fact G tail21;
      let GG := fresh "GG" in
      set (GG := G) in *; clearbody GG;
      repeat match goal with
      | H : ?a ∉ ?L |- _ =>
          lazymatch L with dom GG => fail | _ => clear H end
      end;
      m2_unfold_tys; unfold merge_basic_ty in *; cbn [erase_ty] in *;
      unfold merge_step_tm in *; basic_type
  end.


(** ** Unrolling [merge_fix_value] *)

Definition rec_body_with (F : value) : tm :=
  match_list_named (vfvar xs) (ret (vfvar ys)) h1 t1
    (match_list_named (vfvar ys) (ret (vfvar xs)) h2 t2
       (let_named t (call2_tm F (vfvar t1) (vfvar t2)) merge_step_tm)).

Definition inner_with (F : value) : tm :=
  match_list_named (vfvar ys) (ret (vfvar xs)) h2 t2
    (let_named t (call2_tm F (vfvar t1) (vfvar t2)) merge_step_tm).

Definition E_with (F : value) : tm :=
  let_named t (call2_tm F (vfvar t1) (vfvar t2)) merge_step_tm.

Lemma mu_unroll_eq :
  tm_subst merge_self merge_fix_value (ret (lam_named ys (TBase TList) merge_rec_body)) =
  ret (lam_named ys (TBase TList) (rec_body_with merge_fix_value)).
Proof. vm_compute. reflexivity. Qed.

Lemma mu_fix_basic : ∅ ⊢ᵥ merge_fix_value ⋮ merge_basic_ty.
Proof.
  pose proof merge_program_basic_type as H.
  rewrite merge_program_unfold in H. unfold Ret in H.
  inversion H; subst. assumption.
Qed.

Lemma BT_bodyF :
  <[ys := TBase TList]> (<[xs := TBase TList]> ∅) ⊢ₑ rec_body_with merge_fix_value ⋮ List.
Proof.
  pose proof (subst_typing_tm merge_env_match merge_self merge_basic_ty merge_rec_body
    (TBase TList) merge_fix_value merge_match_basic mu_fix_basic) as H.
  replace (delete merge_self merge_env_match) with
    (<[ys := TBase TList]> (<[xs := TBase TList]> (∅ : gmap atom ty))) in H
    by (vm_compute; reflexivity).
  replace ({merge_self := merge_fix_value} merge_rec_body) with
    (rec_body_with merge_fix_value) in H by (vm_compute; reflexivity).
  apply H. vm_compute. reflexivity.
Qed.

Lemma BT_innerF :
  <[ys := TBase TList]> (<[t1 := TBase TList]> (<[h1 := TBase TNat]>
    (<[xs := TBase TList]> ∅))) ⊢ₑ inner_with merge_fix_value ⋮ List.
Proof.
  pose proof (subst_typing_tm (<[ys := TBase TList]> E02) merge_self merge_basic_ty
    (inner_at ys) (TBase TList) merge_fix_value BT_inner_ys mu_fix_basic) as H.
  replace (delete merge_self (<[ys := TBase TList]> E02)) with
    (<[ys := TBase TList]> (<[t1 := TBase TList]> (<[h1 := TBase TNat]>
      (<[xs := TBase TList]> (∅ : gmap atom ty))))) in H
    by (vm_compute; reflexivity).
  replace ({merge_self := merge_fix_value} (inner_at ys)) with
    (inner_with merge_fix_value) in H by (vm_compute; reflexivity).
  apply H. vm_compute. reflexivity.
Qed.

Definition E03F : gmap atom ty :=
  <[t2 := TBase TList]> (<[h2 := TBase TNat]> (<[t1 := TBase TList]> (<[h1 := TBase TNat]> ∅))).

Lemma BT_EF : E03F ⊢ₑ E_with merge_fix_value ⋮ List.
Proof.
  assert (H0 : <[merge_self := merge_basic_ty]> E03F ⊢ₑ E_inner ⋮ List).
  { apply BT_Einner_gen; unfold E03F;
      first [ m2_eval_lookup | apply not_elem_of_dom; m2_eval_lookup ]. }
  pose proof (subst_typing_tm _ merge_self merge_basic_ty E_inner (TBase TList)
    merge_fix_value H0 mu_fix_basic) as H.
  replace (delete merge_self (<[merge_self := merge_basic_ty]> E03F)) with E03F in H
    by (vm_compute; reflexivity).
  replace ({merge_self := merge_fix_value} E_inner) with
    (E_with merge_fix_value) in H by (vm_compute; reflexivity).
  apply H. apply m2_lk_ins.
Qed.

Lemma BT_lamF :
  ∅ ⊢ₑ ret (lam_named xs (TBase TList) (ret (lam_named ys (TBase TList)
        (rec_body_with merge_fix_value)))) ⋮ merge_basic_ty.
Proof.
  apply TT_Ret. apply basic_typing_lam_named; [set_solver | ].
  apply TT_Ret. apply basic_typing_lam_named.
  - apply not_elem_of_dom. vm_compute. reflexivity.
  - exact BT_bodyF.
Qed.

Lemma BT_lam2F :
  <[xs := TBase TList]> ∅ ⊢ₑ ret (lam_named ys (TBase TList)
        (rec_body_with merge_fix_value)) ⋮ (List →ᵦ List).
Proof.
  apply TT_Ret. apply basic_typing_lam_named.
  - apply not_elem_of_dom. vm_compute. reflexivity.
  - exact BT_bodyF.
Qed.

Lemma BT_fixret : ∅ ⊢ₑ ret merge_fix_value ⋮ merge_basic_ty.
Proof. apply TT_Ret. exact mu_fix_basic. Qed.

Lemma mu_fix_basic_any (G : gmap atom ty) : G ⊢ᵥ merge_fix_value ⋮ merge_basic_ty.
Proof. eapply basic_typing_weaken_value; [exact mu_fix_basic | apply m2_empty_subseteq2]. Qed.

Lemma BT_app1 (G : gmap atom ty) :
  G !! t1 = Some (TBase TList) -> G ⊢ₑ tapp merge_fix_value (vfvar t1) ⋮ (List →ᵦ List).
Proof. intros H. eapply TT_App; [apply mu_fix_basic_any | constructor; exact H]. Qed.

Lemma BT_call (G : gmap atom ty) :
  G !! t1 = Some (TBase TList) -> G !! t2 = Some (TBase TList) ->
  G ⊢ₑ call2_tm merge_fix_value (vfvar t1) (vfvar t2) ⋮ List.
Proof.
  intros H1 H2. unfold call2_tm, case_app. eapply basic_typing_tapp_tm.
  - apply BT_app1. exact H1.
  - constructor. exact H2.
Qed.

Ltac m2_bt_by e0 lem :=
  lazymatch goal with
  | |- ?G ⊢ₑ ?e ⋮ ?T =>
      change (G ⊢ₑ e0 ⋮ T);
      eapply basic_typing_weaken_tm; [exact lem | m2_subseteq]
  end.

Ltac m2_basic :=
  first
    [ m2_bt_by (ret merge_fix_value) BT_fixret
    | m2_bt_by (ret (lam_named xs (TBase TList) (ret (lam_named ys (TBase TList)
        (rec_body_with merge_fix_value))))) BT_lamF
    | m2_bt_by (ret (lam_named ys (TBase TList) (rec_body_with merge_fix_value))) BT_lam2F
    | m2_bt_by (rec_body_with merge_fix_value) BT_bodyF
    | m2_bt_by (inner_with merge_fix_value) BT_innerF
    | m2_bt_by (E_with merge_fix_value) BT_EF
    | lazymatch goal with |- ?G ⊢ₑ ?e ⋮ ?T =>
        change (G ⊢ₑ call2_tm merge_fix_value (vfvar t1) (vfvar t2) ⋮ T);
        apply BT_call; m2_eval_lookup end
    | lazymatch goal with |- ?G ⊢ₑ ?e ⋮ ?T =>
        change (G ⊢ₑ tapp merge_fix_value (vfvar t1) ⋮ T);
        apply BT_app1; m2_eval_lookup end
    | m2_facts_basic ].

Ltac m2_wf :=
  mu_ctx_hook; unfold context_typing_wf;
  split; [m2_wf_ctx | split; [m2_wf_type | m2_basic]].

(** ** Generic structural helpers *)

Lemma mu_ctx_sub_emp Γ (X : aset) :
  wf_ctx_under ∅ Γ -> X = ∅ -> ctx_sub_under ∅ X Γ Emp.
Proof.
  intros HΓ ->. unfold ctx_sub_under. split; [exact HΓ | split; [exact I | split]].
  - intros x Hx. set_solver.
  - intros r Hr. eexists. split; [reflexivity | ].
    cbn [ctx_denote_under].
    apply res_models_and_intro_from_models.
    + match goal with |- _ ⊨ basic_world_formula ?E =>
        replace E with (∅ : gmap logic_var ty) by (vm_compute; reflexivity) end.
      apply basic_world_formula_empty.
    + apply res_models_true.
Qed.

Ltac mu_fv_empty :=
  repeat match goal with
  | |- context[fv_cty ?τ] => rewrite (mu_closed_fv τ) by m2_wf_type
  end;
  vm_compute; reflexivity.

Ltac mu_fix_form :=
  change merge_fix_value with
    (fixfun_named merge_self xs (TBase TList) (List →ᵦ List)
       (ret (lam_named ys (TBase TList) merge_rec_body))).

Ltac mu_after_unroll :=
  change (fixfun_named merge_self xs (TBase TList) (List →ᵦ List)
       (ret (lam_named ys (TBase TList) merge_rec_body))) with merge_fix_value;
  rewrite mu_unroll_eq.

Ltac mu_proj_top x b :=
  eapply EXT_CtxSub with (Γ2 := x ∷ over_ty b qual_top);
  [ m2_wf | eapply EXT_Var; m2_wf
  | apply merge_proj_over_top; [m2_wf_ctx | m2_eval_lookup] ].

Lemma mu_den_comma_l Σ Γ1 Γ2 (r : WfWorld) :
  r ⊨ ctx_denote_under Σ (CtxComma Γ1 Γ2) ->
  r ⊨ ctx_denote_under (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2))) Γ1.
Proof.
  intros H. cbn [ctx_denote_under] in H.
  apply res_models_and_elim_r in H. apply res_models_and_elim_l in H. exact H.
Qed.

Lemma mu_den_comma_r Σ Γ1 Γ2 (r : WfWorld) :
  r ⊨ ctx_denote_under Σ (CtxComma Γ1 Γ2) ->
  r ⊨ ctx_denote_under (store_restrict Σ (ctx_fv (CtxComma Γ1 Γ2)) ∪ erase_ctx Γ1) Γ2.
Proof.
  intros H. cbn [ctx_denote_under] in H.
  apply res_models_and_elim_r in H. apply res_models_and_elim_r in H. exact H.
Qed.

Lemma mu_den_bind_closed Σ x τ (r : WfWorld) :
  fv_cty τ = ∅ ->
  r ⊨ ctx_denote_under Σ (CtxBind x τ) ->
  r ⊨ ctx_denote_under ∅ (CtxBind x τ).
Proof.
  intros Hfv H. rewrite ctx_denote_under_minimal in H |- *.
  cbn [ctx_fv] in H |- *. rewrite Hfv in H |- *.
  rewrite storeA_restrict_empty_set in H |- *. exact H.
Qed.

Lemma mu_bind_ctx_sub (Γ : ctx) (x : atom) (τ : context_ty) :
  wf_ctx_under ∅ Γ -> wf_ctx_under ∅ (x ∷ τ) ->
  fv_cty τ = ∅ ->
  erase_ctx Γ !! x = Some (erase_ty τ) ->
  (forall r : WfWorld, r ⊨ ctx_denote_under ∅ Γ -> r ⊨ ctx_denote_under ∅ (x ∷ τ)) ->
  ctx_sub_under ∅ (fv_tm (ret (vfvar x)) ∪ fv_cty τ) Γ (x ∷ τ).
Proof.
  intros HΓ Hx Hfv Hlk Hden.
  split; [exact HΓ | split; [exact Hx | split]].
  - intros z Hz. rewrite Hfv in Hz. cbn [fv_tm fv_value] in Hz.
    assert (z = x) as -> by set_solver.
    rewrite Hlk. symmetry. apply m2_lk_single.
  - intros r Hr. exists r. split; [apply res_restrict_le | apply Hden; exact Hr].
Qed.

Ltac mu_proj_closed :=
  apply mu_bind_ctx_sub;
  [ m2_wf_ctx | m2_wf_ctx | apply mu_closed_fv; m2_wf_type | m2_eval_lookup | ];
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; eapply mu_den_bind_closed; [apply mu_closed_fv; m2_wf_type | ].

(** ** Unrolling and pattern-introduction helpers *)

Lemma mu_unroll_lc : lc_tm (ret (lam_named ys (TBase TList) merge_rec_body)).
Proof. exact (typing_tm_lc _ _ _ merge_lam_ys_basic). Qed.

(** [EXT_FixUnrollNamed] at a [fix_unroll_shape] target.  All unrolling
    targets below are top-level arrows ([mu_T00], [mu_T24],
    [mu_cex_arrow_ty]), so the shape premise is [I]; the body is locally
    closed by basic typing. *)
Ltac mu_unroll :=
  mu_fix_form; eapply EXT_FixUnrollNamed;
  [ exact mu_unroll_lc | m2_wf | mu_after_unroll ].

(** Use a pattern-introduction obligation stated over the free variables
    [X'] of the match: the [EXT_CtxSub] goal mentions
    [fv_tm match ∪ fv_cty τ], which computes to [X']. *)
Ltac mu_use_sub lem :=
  lazymatch type of lem with
  | ctx_sub_under _ ?X' _ _ =>
      lazymatch goal with
      | |- ctx_sub_under ?S ?X ?G1 ?G2 =>
          replace X with X';
          [ exact lem
          | rewrite ?mu_closed_fv by m2_wf_type; vm_compute; reflexivity ]
      end
  end.

(** ** Semantic helper lemmas for the obligations of the unrolling derivation

    Two generic, fully proved facts used below:
    - [mu_pat_intro]: the pattern introduction required by the corrected
      [EXT_ListMatchConsOnlyNamed] (the branch context itself binds the
      pattern variables, introduced with [EXT_CtxSub]).  For a context [Γ]
      with closed bindings and constants [c1], [c2],
        ctx_sub_under ∅ (dom ⌊Γ⌋) Γ ((Γ ,, x1 ∷ {ν = c1}) ,, x2 ∷ {ν = c2}).
      Proof: restrict a model [r] of [Γ] to [dom ⌊Γ⌋] (the context formula
      only reads these variables), then extend it twice by the result of
      [ret c1], [ret c2] exactly as T-Let does
      ([Soundness.ctx_comma_bind_of_result_ext]); the bound terms are typed
      by the T-Const denotation ([ConstDenote.const_direct_denotation_gas_in_ctx])
      weakened to its over part.
    - [mu_sub_arrow_to_wand]: [τx → τ <: τx -∗ τ] in every context.  In the
      Rocq semantics [FForall (FImpl A B)] entails [FBWand 1 A B]
      ([mu_forall_impl_to_bwand]): for a wand argument world [m'] compatible
      with [m] that adds exactly the fresh coordinate [z], the product
      [m' × m] is an extension of [m] by [z] (world compatibility forces the
      shared coordinates to be constant), so the arrow's full-world
      quantifier ([res_models_forall_rev]) applies to it, and [m' ⊑ m' × m]
      transports the argument formula. *)

From ProofAutomation Require Import ExtendedSubsumption.
From ContextLogic Require Import FormulaConnectives FormulaConnectivesHigher.
From ContextAlgebra Require Import ResourceInterface.
From ContextBasicDenotation Require Import TermExtension.
From Denotation Require Import TypeDenote ConstDenote ConstDenoteBase.
From ContextTyping Require Import Soundness.

Lemma mu_forall_impl_to_bwand (m : WfWorld (V := value)) (A B : Formula (V := value)) :
  formula_scoped_in_world m (FBWand 1 A B) ->
  m ⊨ FForall (FImpl A B) -> m ⊨ FBWand 1 A B.
Proof.
  intros Hscope Hall.
  destruct (res_models_forall_rev m _ Hall) as [L HL].
  apply res_models_fbwand_intro; [exact Hscope | ].
  exists (L ∪ world_dom (m : World (V := value))).
  intros η m' Hc Hbind Hfresh Hdom Harg.
  destruct (open_env_binds_one_inv η Hbind) as [z ->].
  rewrite formula_open_env_singleton in Harg |- *.
  assert (Hat : open_env_atoms (<[0%nat := z]> (∅ : gmap nat atom)) = {[z]}).
  { rewrite open_env_atoms_insert by apply lookup_empty.
    rewrite open_env_atoms_empty. set_solver. }
  rewrite Hat in Hfresh, Hdom.
  assert (Hle : m ⊑ res_product m' m Hc) by apply res_product_le_r.
  pose proof (HL z ltac:(set_solver) (res_product m' m Hc) Hdom
    (res_restrict_eq_of_le _ _ Hle)) as H.
  rewrite formula_open_impl in H.
  eapply res_models_impl_elim; [exact H | ].
  eapply res_models_kripke; [apply res_product_le_l | exact Harg].
Qed.

Lemma mu_ty_denote_gas_arrow_to_wand gas Σ τx τ e (m : WfWorld (V := value)) :
  m ⊨ ty_denote_gas gas Σ (CTArrow τx τ) e ->
  m ⊨ ty_denote_gas gas Σ (CTWand τx τ) e.
Proof.
  intros H.
  assert (Hguard_tr : forall n : WfWorld (V := value),
    n ⊨ ty_guard_formula (relevant_env Σ (CTArrow τx τ) e) (CTArrow τx τ) e ->
    n ⊨ ty_guard_formula (relevant_env Σ (CTWand τx τ) e) (CTWand τx τ) e).
  { intros n Hg.
    change (relevant_env Σ (CTWand τx τ) e) with (relevant_env Σ (CTArrow τx τ) e).
    pose proof Hg as Hg'. unfold ty_guard_formula in Hg'.
    rewrite !res_models_and_iff in Hg'.
    destruct Hg' as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    apply ty_guard_transport; [reflexivity | | exact Hshape | exact Hg].
    change (context_ty_lvars (CTWand τx τ)) with (context_ty_lvars (CTArrow τx τ)).
    reflexivity. }
  destruct gas as [ |g]; cbn [ty_denote_gas] in H |- *;
    rewrite res_models_and_iff in H |- *; destruct H as [Hg Hb];
    (split; [apply Hguard_tr; exact Hg | ]).
  - exact Hb.
  - change (relevant_env Σ (CTWand τx τ) e) with (relevant_env Σ (CTArrow τx τ) e).
    change (erase_ty (CTWand τx τ)) with (erase_ty (CTArrow τx τ)).
    unfold arrow_value_denote_gas_with in Hb. unfold wand_value_denote_gas_with.
    eapply res_models_forall_full_world_impl_map;
      [ exact (res_models_scoped _ _ Hb) | | exact Hb ].
    exists ∅. intros y _ my _ _. split; [auto | ].
    rewrite formula_open_forall, formula_open_fbwand, formula_open_impl.
    intros Hx. apply mu_forall_impl_to_bwand; [ exact (res_models_scoped _ _ Hx) | exact Hx ].
Qed.

Lemma mu_sub_arrow_to_wand Σ Γ τx τ :
  wf_ctx_under Σ Γ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTArrow τx τ) ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) (CTWand τx τ) ->
  sub_type_under Σ Γ (CTArrow τx τ) (CTWand τx τ).
Proof.
  intros HΓ H1 H2.
  apply ext_sub_type_of_pointwise.
  - split; [exact HΓ | split; [exact H1 | split; [exact H2 | reflexivity]]].
  - intros e m _ H. unfold ty_denote in *.
    change (cty_depth (CTWand τx τ)) with (cty_depth (CTArrow τx τ)).
    apply mu_ty_denote_gas_arrow_to_wand. exact H.
Qed.

Fixpoint mu_closed_binds (Γ : ctx) : Prop :=
  match Γ with
  | CtxEmpty => True
  | CtxBind _ τ => fv_cty τ = ∅
  | CtxComma Γ1 Γ2 | CtxStar Γ1 Γ2 => mu_closed_binds Γ1 /\ mu_closed_binds Γ2
  | CtxSum _ _ => False
  end.

Lemma mu_closed_binds_fv Γ : mu_closed_binds Γ -> ctx_fv Γ = ∅.
Proof.
  induction Γ; cbn [mu_closed_binds ctx_fv]; intros H; try contradiction.
  - reflexivity.
  - exact H.
  - destruct H as [H1 H2]. rewrite IHΓ1, IHΓ2 by assumption. set_solver.
  - destruct H as [H1 H2]. rewrite IHΓ1, IHΓ2 by assumption. set_solver.
Qed.

Lemma mu_store_restrict_empty_ty (Σ : gmap atom ty) :
  storeA_restrict Σ ∅ = ∅.
Proof. apply map_eq. intros k. apply storeA_restrict_lookup_none_r. set_solver. Qed.

Lemma mu_ctx_denote_fv_closed Γ :
  mu_closed_binds Γ ->
  forall Σ, formula_fv (ctx_denote_under Σ Γ) ⊆ dom (erase_ctx Γ).
Proof.
  induction Γ; intros Hcl Σ; pose proof (mu_closed_binds_fv _ Hcl) as Hfv;
    cbn [ctx_denote_under]; rewrite Hfv, mu_store_restrict_empty_ty;
    rewrite formula_fv_and, formula_fv_basic_world_formula, lvars_fv_atom_env_to_lty_env_dom;
    rewrite (left_id_L ∅ union); cbn [mu_closed_binds] in Hcl; try contradiction.
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
    cbn [erase_ctx] in *. rewrite ?dom_union_L in *. set_solver.
  - destruct Hcl as [H1 H2].
    rewrite formula_fv_star.
    pose proof (IHΓ1 H1 ∅) as Hi1. pose proof (IHΓ2 H2 ∅) as Hi2.
    cbn [erase_ctx] in *. rewrite ?dom_union_L in *. set_solver.
Qed.

(** [{ν = c}] at the base type of [c]; [mu_On n] and [mu_Oc l] are instances. *)
Definition mu_const_over (c : constant) : context_ty :=
  over_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)).

Lemma mu_const_over_denote Γ c (m : WfWorld) :
  m ⊨ ty_denote_under ∅ Γ (mu_const_over c) (tret (vconst c)).
Proof.
  assert (Hemp : m ⊨ ctx_denote_under ∅ CtxEmpty).
  { cbn [ctx_denote_under]. apply res_models_and_intro_from_models.
    + match goal with |- _ ⊨ basic_world_formula ?E =>
        replace E with (∅ : gmap logic_var ty) by (vm_compute; reflexivity) end.
      apply basic_world_formula_empty.
    + apply res_models_true. }
  assert (Hbt : ctx_erasure_under ∅ CtxEmpty ⊢ₑ
      tret (vconst c) ⋮ erase_ty (const_precise_ty c)).
  { apply TT_Ret. constructor. }
  pose proof (const_direct_denotation_gas_in_ctx (cty_depth (const_precise_ty c)) ∅ c m
    Hemp Hbt) as Hp.
  change (m ⊨ ty_denote (ctx_erasure_under ∅ CtxEmpty)
    (CTInter (mu_const_over c) (under_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
    (tret (vconst c))) in Hp.
  apply ty_denote_inter_elim_l in Hp.
  unfold ty_denote_under, ty_denote in *.
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars (mu_const_over c) (tret (vconst c))); [reflexivity | | exact Hp].
  change (relevant_env (atom_env_to_lty_env (ctx_erasure_under ∅ CtxEmpty))
            (mu_const_over c) (tret (vconst c)) =
          relevant_env (atom_env_to_lty_env (erase_ctx Γ)) (mu_const_over c) (tret (vconst c))).
  unfold mu_const_over, over_ty.
  rewrite !relevant_env_const_over_atom_env_empty. reflexivity.
Qed.

Lemma mu_extend_comma_const Γ x c (m : WfWorld) :
  context_typing_wf ∅ Γ (tret (vconst c)) (mu_const_over c) ->
  x ∉ dom (erase_ctx Γ) ->
  x ∉ world_dom (m : World) ->
  m ⊨ ctx_denote_under ∅ Γ ->
  exists mx : WfWorld, m ⊑ mx /\ world_dom (mx : World) = world_dom (m : World) ∪ {[x]} /\
    mx ⊨ ctx_denote_under ∅ (Γ ,, (x ∷ mu_const_over c)).
Proof.
  intros Hwf HxΓ Hxm Hm.
  destruct (expr_result_extension_witness_exists (tret (vconst c)) x) as [Fx HFx].
  { cbn [fv_tm fv_value]. set_solver. }
  assert (Happ : extension_applicable Fx m).
  { destruct HFx as [_ [Hin Hout] _].
    constructor.
    - change (ext_in Fx ⊆ world_dom (m : World)). rewrite Hin. cbn [fv_tm fv_value]. set_solver.
    - change (ext_out Fx ## world_dom (m : World)). rewrite Hout. set_solver. }
  destruct (res_extend_by_exists m Fx Happ) as [mx Hext].
  exists mx. split; [eapply res_extend_by_le; exact Hext | split].
  - rewrite (res_extend_by_dom m Fx mx Hext).
    destruct HFx as [_ [_ Hout] _].
    change (world_dom (m : World) ∪ ext_out Fx = world_dom (m : World) ∪ {[x]}).
    rewrite Hout. reflexivity.
  - eapply (ctx_comma_bind_of_result_ext concrete_Φ concrete_Φ_wf);
      [exact Hwf | exact Hm | | exact HFx | exact HxΓ | exact Hext].
    apply mu_const_over_denote.
Qed.

Lemma mu_pat_intro (Γ : ctx) (X : aset) (x1 x2 : atom) (c1 c2 : constant) :
  mu_closed_binds Γ ->
  dom (erase_ctx Γ) = X ->
  wf_ctx_under ∅ ((Γ ,, (x1 ∷ mu_const_over c1)) ,, (x2 ∷ mu_const_over c2)) ->
  context_typing_wf ∅ Γ (tret (vconst c1)) (mu_const_over c1) ->
  context_typing_wf ∅ (Γ ,, (x1 ∷ mu_const_over c1)) (tret (vconst c2)) (mu_const_over c2) ->
  x1 ∉ X -> x2 ∉ X ∪ {[x1]} ->
  ctx_sub_under ∅ X Γ ((Γ ,, (x1 ∷ mu_const_over c1)) ,, (x2 ∷ mu_const_over c2)).
Proof.
  intros Hcl HX Hwf2 Hwf1 Hwf1' Hx1 Hx2.
  pose proof (context_typing_wf_ctx _ _ _ _ Hwf1) as HwfΓ.
  split; [exact HwfΓ | split; [exact Hwf2 | split]].
  - intros z Hz. rewrite <- HX in Hz. apply elem_of_dom in Hz as [T HT].
    rewrite HT. symmetry. cbn [erase_ctx].
    apply map_lookup_union_Some_raw. left.
    apply map_lookup_union_Some_raw. left. exact HT.
  - intros r Hr.
    assert (Hfv : formula_fv (ctx_denote_under ∅ Γ) ⊆ X).
    { rewrite <- HX. apply mu_ctx_denote_fv_closed. exact Hcl. }
    pose proof (proj1 (res_models_minimal_on X r _ Hfv) Hr) as Hm0.
    assert (Hd0 : x1 ∉ world_dom (res_restrict r X : World)).
    { rewrite res_restrict_dom. set_solver. }
    destruct (mu_extend_comma_const Γ x1 c1 (res_restrict r X) Hwf1
      ltac:(rewrite HX; exact Hx1) Hd0 Hm0) as [m1 [Hle1 [Hdom1 Hm1]]].
    assert (Hd1 : x2 ∉ world_dom (m1 : World)).
    { rewrite Hdom1, res_restrict_dom. set_solver. }
    assert (Hx2Γ : x2 ∉ dom (erase_ctx (Γ ,, (x1 ∷ mu_const_over c1)))).
    { rewrite m2_dom_comma, erase_ctx_bind_dom, HX. set_solver. }
    destruct (mu_extend_comma_const (Γ ,, (x1 ∷ mu_const_over c1)) x2 c2 m1 Hwf1'
      Hx2Γ Hd1 Hm1) as [m2 [Hle2 [_ Hm2]]].
    exists m2. split; [etransitivity; [exact Hle1 | exact Hle2] | exact Hm2].
Qed.

(** Instantiates [mu_pat_intro] for the concrete contexts below. *)
Ltac mu_pat_tac :=
  repeat match goal with
  | |- context [mu_On ?n] => change (mu_On n) with (mu_const_over (cnat n))
  | |- context [mu_Oc ?l] => change (mu_Oc l) with (mu_const_over (clist l))
  end;
  apply mu_pat_intro;
  [ mu_ctx_hook; cbn [mu_closed_binds]; repeat split; apply mu_closed_fv; m2_wf_type
  | m2_set
  | unfold mu_const_over; m2_wf_ctx
  | unfold mu_const_over; m2_wf
  | unfold mu_const_over; m2_wf
  | rewrite !elem_of_union, !elem_of_singleton; vm_compute; intuition congruence
  | rewrite !elem_of_union, !elem_of_singleton; vm_compute; intuition congruence ].

(** ** Level B: [merge [] [] = []] *)

Definition GB0 : ctx := (Emp ,, (xs ∷ mu_Oc nil)) ,, (ys ∷ mu_Oc nil).

(** Admitted.  Informal argument: in every model of [GB0] the over part of
    [xs ∷ {ν = []}] (closed qualifier, no fibering) forces [xs = []] in every
    store, so the [xs]-fibering of the target has the single fiber
    [xs = []].  For [m' ⊨ const_precise_ty [] e] the over part says every
    result of [e] is [[]] and the under part (with totality from the guard)
    that [[]] is reached; on the fiber [xs = []] this is exactly
    [{ν = xs} ⊓ [ν = xs]].  The guard (well-formedness, basic typing at
    [List], totality) is shared by both sides since the erasures agree. *)
Lemma mu_B_obl_nil_eq :
  sub_type_under ∅ GB0 (const_precise_ty (clist nil)) (list_match_eq_ty (vfvar xs)).
Proof. Admitted.

Lemma mu_fix00 : ∅; Emp ⊢ₓ ret merge_fix_value ⋮ mu_T00.
Proof.
  mu_unroll.
  eapply EXT_LamNamedErased with (τx := mu_Oc nil) (τ := mu_T0); [reflexivity | m2_wf | ].
  eapply EXT_LamNamedErased with (τx := mu_Oc nil) (τ := mu_Oc nil); [reflexivity | m2_wf | ].
  fold GB0. unfold rec_body_with, match_list_named.
  eapply EXT_ListMatchNilOnly.
  - m2_wf.
  - eapply EXT_Sub with (τ1 := const_precise_ty (clist nil)).
    + m2_wf.
    + eapply EXT_CtxSub with (Γ2 := Emp).
      * m2_wf.
      * eapply EXT_Const. m2_wf.
      * apply mu_ctx_sub_emp; [m2_wf_ctx | mu_fv_empty].
    + exact mu_B_obl_nil_eq.
  - unfold GB0. eapply EXT_VarComma. m2_wf.
Qed.

(** ** Level A: [merge [2] [4] = [2;4]] *)

Definition GA0 : ctx := (Emp ,, (xs ∷ mu_Oc (2%nat :: nil))) ,, (ys ∷ mu_Oc (4%nat :: nil)).
(** Branch contexts binding the pattern variables (introduced by
    [EXT_CtxSub], see [mu_A_obl_pat1]). *)
Definition GA1 : ctx := (GA0 ,, (h1 ∷ mu_On 2)) ,, (t1 ∷ mu_Oc nil).
Definition GA2 : ctx := (GA1 ,, (h2 ∷ mu_On 4)) ,, (t2 ∷ mu_Oc nil).
Definition GA3 : ctx := GA2 ,, (t ∷ mu_Oc nil).
Definition GA4 : ctx := GA3 ,, (lt12 ∷ binop_precise_ty bop_lt (vfvar h1) (vfvar h2)).
Definition GA5 : ctx := GA4 ,, (tail12 ∷ list_cons_precise_ty (vfvar h2) (vfvar t)).

Ltac mu_ctx_hook ::= repeat progress unfold GB0, GA0, GA1, GA2, GA3, GA4, GA5 in *.

(** Semantic obligations of level A.  In every model of [GA0..GA5] the over
    parts of the closed bindings force, in every store, [xs = [2]],
    [ys = [4]], [h1 = 2], [t1 = []], [h2 = 4], [t2 = []], [t = []]
    (each binding [x ∷ {ν = c}] has a closed qualifier, see
    [ty_denote_over_ret_fvar_const_lookup]).  Hence every fibering below has a
    single fiber.

    [mu_A_obl_pat1] / [mu_A_obl_pat2] (PROVED, instances of [mu_pat_intro])
    are the pattern introductions required by the corrected
    [EXT_ListMatchConsOnlyNamed] (the branch context itself binds the
    pattern variables; [EXT_CtxSub] introduces them): every model [r] of
    [GA0] restricted to [{xs, ys}] extends to a model of
    [(GA0 ,, h1 ∷ {ν = 2}) ,, t1 ∷ {ν = []}] by the constant coordinates
    [h1 ↦ 2], [t1 ↦ []].  This is NOT vacuous in the sense of the unsound old
    rule: the extension exists for EVERY model of [GA0]; the correctness of
    the chosen values is checked separately by the pattern equation
    [mu_A_obl_eq1] ([h1 :: t1 : {ν = xs} ⊓ [ν = xs]], true since [xs = [2]]).

    [mu_A_obl_eq1] (Admitted): the source [list_cons_precise_ty h1 t1] is
    fibered over [{h1, t1}]; on the single fiber [(2, [])] every result of [e]
    is [2 :: [] = [2]] (over part) and [[2]] is reached (under part).  The
    target is fibered over [{xs}]; on its single fiber [xs = [2]] this is
    exactly [{ν = xs} ⊓ [ν = xs]].  Guards coincide. *)
Lemma mu_A_obl_pat1 :
  ctx_sub_under ∅ ({[xs]} ∪ {[ys]}) GA0 GA1.
Proof. unfold GA1. mu_pat_tac. Qed.
Lemma mu_A_obl_pat2 :
  ctx_sub_under ∅ ({[xs]} ∪ {[ys]} ∪ {[h1]} ∪ {[t1]}) GA1 GA2.
Proof. unfold GA2. mu_pat_tac. Qed.
Lemma mu_A_obl_eq1 :
  sub_type_under ∅ GA1 (list_cons_precise_ty (vfvar h1) (vfvar t1)) (list_match_eq_ty (vfvar xs)).
Proof. Admitted.
(** Admitted: as [mu_A_obl_eq1] with [h2 = 4], [t2 = []], [ys = [4]]. *)
Lemma mu_A_obl_eq2 :
  sub_type_under ∅ GA2 (list_cons_precise_ty (vfvar h2) (vfvar t2)) (list_match_eq_ty (vfvar ys)).
Proof. Admitted.
Lemma mu_A_obl_proj_t1 :
  ctx_sub_under ∅ (fv_tm (ret (vfvar t1)) ∪ fv_cty (mu_Oc nil)) GA2 (t1 ∷ mu_Oc nil).
Proof.
  mu_proj_closed.
  unfold GA2 in Hr. apply mu_den_comma_l, mu_den_comma_l in Hr.
  unfold GA1 in Hr. apply mu_den_comma_r in Hr. exact Hr.
Qed.
Lemma mu_A_obl_proj_t2 (f : atom) :
  f ∉ merge_fixed_atoms ->
  ctx_sub_under ∅ (fv_tm (ret (vfvar t2)) ∪ fv_cty (mu_Oc nil)) (GA2 ,, (f ∷ mu_T0)) (t2 ∷ mu_Oc nil).
Proof.
  intros Hf. mu_proj_closed.
  apply mu_den_comma_l in Hr.
  unfold GA2 in Hr. apply mu_den_comma_r in Hr. exact Hr.
Qed.
(** Admitted.  [h1 = 2], [h2 = 4] in every store; [binop_precise_ty bop_lt h1 h2]
    is fibered over [{h1, h2}] and on the single fiber [(2, 4)] its over part
    forces [lt12 ∈ {c | bin_step bop_lt 2 4 c} = {true}].  Take
    [r' := r|{lt12} = {[lt12 ↦ true]}]: it satisfies the over part
    (all [true]), the under part ([true] present) and the guard ([lt12] is a
    boolean, [ret lt12] is total) of [lt12 ∷ bool_precise_ty true]. *)
Lemma mu_A_obl_lt_true :
  ctx_sub_under ∅ (fv_tm (ret (vfvar lt12)) ∪ fv_cty (bool_precise_ty true)) GA4
    (lt12 ∷ bool_precise_ty true).
Proof. Admitted.
(** Admitted.  In [GA5] additionally [tail12 = h2 :: t = [4]] (over part of
    [list_cons_precise_ty h2 t] on its single fiber [(4, [])]).  The over part
    of the source on the single fiber [(h1, tail12) = (2, [4])] makes every
    result of [e] equal to [[2; 4]], which is the closed qualifier of
    [mu_Oc [2;4]]; the guards coincide. *)
Lemma mu_A_obl_leaf :
  sub_type_under ∅ GA5 (list_cons_precise_ty (vfvar h1) (vfvar tail12)) (mu_Oc cex_rec).
Proof. Admitted.

Lemma mu_fix24 : ∅; Emp ⊢ₓ ret merge_fix_value ⋮ mu_T24.
Proof.
  mu_unroll.
  eapply EXT_LamNamedErased with (τx := mu_Oc (2%nat :: nil)) (τ := mu_T4); [reflexivity | m2_wf | ].
  eapply EXT_LamNamedErased with (τx := mu_Oc (4%nat :: nil)) (τ := mu_Oc cex_rec);
    [reflexivity | m2_wf | ].
  fold GA0. unfold rec_body_with.
  (* introduce the pattern variables [h1, t1] of the outer match *)
  eapply EXT_CtxSub with (Γ2 := GA1); [m2_wf | | mu_use_sub mu_A_obl_pat1].
  eapply EXT_ListMatchConsOnlyNamed.
  { m2_wf. }
  { eapply EXT_Sub with (τ1 := list_cons_precise_ty (vfvar h1) (vfvar t1)).
    - m2_wf.
    - eapply EXT_ListCons; [m2_wf | mu_proj_top h1 TNat | mu_proj_top t1 TList].
    - exact mu_A_obl_eq1. }
  (* introduce the pattern variables [h2, t2] of the inner match *)
  eapply EXT_CtxSub with (Γ2 := GA2); [m2_wf | | mu_use_sub mu_A_obl_pat2].
  eapply EXT_ListMatchConsOnlyNamed.
  { m2_wf. }
  { eapply EXT_Sub with (τ1 := list_cons_precise_ty (vfvar h2) (vfvar t2)).
    - m2_wf.
    - eapply EXT_ListCons; [m2_wf | mu_proj_top h2 TNat | mu_proj_top t2 TList].
    - exact mu_A_obl_eq2. }
  eapply EXT_LetNamed with (τ1 := mu_Oc nil).
  { m2_wf. }
  { unfold call2_tm, tapp_tm, case_app.
    eapply EXT_Let with (L := merge_fixed_atoms) (τ1 := mu_T0).
    - m2_wf.
    - replace mu_T0 with (cty_open 0 t1 mu_T0) by (apply mu_closed_open; m2_wf_type).
      eapply EXT_AppFun with (τx := mu_Oc nil).
      + m2_wf.
      + rewrite !mu_closed_fv by m2_wf_type. vm_compute. set_solver.
      + eapply EXT_CtxSub with (Γ2 := Emp).
        * m2_wf.
        * exact mu_fix00.
        * apply mu_ctx_sub_emp; [m2_wf_ctx | mu_fv_empty].
      + eapply EXT_CtxSub with (Γ2 := t1 ∷ mu_Oc nil).
        * m2_wf.
        * eapply EXT_Var. m2_wf.
        * exact mu_A_obl_proj_t1.
    - intros f Hf.
      cbn [open_one open_tm_atom_inst open_tm open_value value_shift].
      rewrite decide_True by reflexivity.
      replace (mu_Oc nil) with (cty_open 0 t2 (mu_Oc nil))
        by (apply mu_closed_open; m2_wf_type).
      eapply EXT_AppFun with (τx := mu_Oc nil).
      + m2_wf.
      + rewrite !mu_closed_fv by m2_wf_type. cbn [fv_value].
        intros Hin. apply Hf. unfold merge_fixed_atoms. set_solver.
      + change (mu_Oc nil → mu_Oc nil) with mu_T0. eapply EXT_VarComma. m2_wf.
      + eapply EXT_CtxSub with (Γ2 := t2 ∷ mu_Oc nil).
        * m2_wf.
        * eapply EXT_Var. m2_wf.
        * exact (mu_A_obl_proj_t2 f Hf). }
  fold GA3. unfold merge_step_tm.
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_lt (vfvar h1) (vfvar h2)).
  { m2_wf. }
  { eapply EXT_BinOp. m2_wf. }
  fold GA4. unfold if_named.
  eapply EXT_MatchTrueOnly.
  { m2_wf. }
  { eapply EXT_CtxSub with (Γ2 := lt12 ∷ bool_precise_ty true).
    - m2_wf.
    - eapply EXT_Var. m2_wf.
    - exact mu_A_obl_lt_true. }
  eapply EXT_LetNamed with (τ1 := list_cons_precise_ty (vfvar h2) (vfvar t)).
  { m2_wf. }
  { eapply EXT_ListCons; [m2_wf | mu_proj_top h2 TNat | mu_proj_top t TList]. }
  fold GA5.
  eapply EXT_Sub with (τ1 := list_cons_precise_ty (vfvar h1) (vfvar tail12)).
  { m2_wf. }
  { eapply EXT_ListCons; [m2_wf | mu_proj_top h1 TNat | mu_proj_top tail12 TList]. }
  exact mu_A_obl_leaf.
Qed.

(** ** Level O: the outer call [merge [1;2] [3;4]]

    Derived at [mu_cex_arrow_ty = l1:[1;2] → l2:[3;4] -∗ {¬sorted} ⊕ {⊤}]
    (unrolling needs an arrow on top), so the first parameter is bound with
    [,,] and the second with [∗]. *)

Definition GO0 : ctx := (Emp ,, (xs ∷ mu_Pc cex_l1)) ∗ (ys ∷ mu_Pc cex_l2).
Definition GO1 : ctx := (GO0 ,, (h1 ∷ mu_On 1)) ,, (t1 ∷ mu_Oc (2%nat :: nil)).
Definition GO2 : ctx := (GO1 ,, (h2 ∷ mu_On 3)) ,, (t2 ∷ mu_Oc (4%nat :: nil)).
Definition GO3 : ctx := GO2 ,, (t ∷ mu_Oc cex_rec).
Definition GO4 : ctx := GO3 ,, (lt12 ∷ binop_precise_ty bop_lt (vfvar h1) (vfvar h2)).
Definition GO5 : ctx := GO4 ,, (tail12 ∷ list_cons_precise_ty (vfvar h2) (vfvar t)).

Ltac mu_ctx_hook ::= repeat progress unfold GB0, GA0, GA1, GA2, GA3, GA4, GA5,
  GO0, GO1, GO2, GO3, GO4, GO5 in *.

(** Semantic obligations of level O.  [GO0] is [(Emp ,, xs ∷ P[1;2]) ∗
    ys ∷ P[3;4]] with closed precise singleton bindings
    ([P c = {ν = c} ⊓ [ν = c]]); star elimination gives [m1 × m2 ⊑ r] with
    [m1 ⊨ Emp ,, xs ∷ P[1;2]] and [m2 ⊨ ys ∷ P[3;4]], so every store of a
    model has [xs = [1;2]], [ys = [3;4]] (over parts, closed qualifiers);
    the closed pattern bindings give [h1 = 1], [t1 = [2]], [h2 = 3],
    [t2 = [4]], [t = [2;4]].  Every fibering below has a single fiber.

    [mu_O_obl_pat1] / [mu_O_obl_pat2] (PROVED, instances of [mu_pat_intro]):
    pattern introduction with [h1 ↦ 1], [t1 ↦ [2]], resp. [h2 ↦ 3],
    [t2 ↦ [4]]; correctness of the chosen values is checked by
    [mu_O_obl_eq1] / [mu_O_obl_eq2].

    [mu_O_obl_eq1] (Admitted): on the single [(h1, t1)] fiber every result is
    [1 :: [2] = [1;2] = xs], and it is reached; this is
    [{ν = xs} ⊓ [ν = xs]] on the single [xs]-fiber. *)
Lemma mu_O_obl_pat1 :
  ctx_sub_under ∅ ({[xs]} ∪ {[ys]}) GO0 GO1.
Proof. unfold GO1. mu_pat_tac. Qed.
Lemma mu_O_obl_pat2 :
  ctx_sub_under ∅ ({[xs]} ∪ {[ys]} ∪ {[h1]} ∪ {[t1]}) GO1 GO2.
Proof. unfold GO2. mu_pat_tac. Qed.
Lemma mu_O_obl_eq1 :
  sub_type_under ∅ GO1 (list_cons_precise_ty (vfvar h1) (vfvar t1)) (list_match_eq_ty (vfvar xs)).
Proof. Admitted.
(** Admitted: as [mu_O_obl_eq1] with [h2 = 3], [t2 = [4]], [ys = [3;4]]. *)
Lemma mu_O_obl_eq2 :
  sub_type_under ∅ GO2 (list_cons_precise_ty (vfvar h2) (vfvar t2)) (list_match_eq_ty (vfvar ys)).
Proof. Admitted.
Lemma mu_O_obl_proj_t1 :
  ctx_sub_under ∅ (fv_tm (ret (vfvar t1)) ∪ fv_cty (mu_Oc (2%nat :: nil))) GO2
    (t1 ∷ mu_Oc (2%nat :: nil)).
Proof.
  mu_proj_closed.
  unfold GO2 in Hr. apply mu_den_comma_l, mu_den_comma_l in Hr.
  unfold GO1 in Hr. apply mu_den_comma_r in Hr. exact Hr.
Qed.
Lemma mu_O_obl_proj_t2 (f : atom) :
  f ∉ merge_fixed_atoms ->
  ctx_sub_under ∅ (fv_tm (ret (vfvar t2)) ∪ fv_cty (mu_Oc (4%nat :: nil))) (GO2 ,, (f ∷ mu_T4))
    (t2 ∷ mu_Oc (4%nat :: nil)).
Proof.
  intros Hf. mu_proj_closed.
  apply mu_den_comma_l in Hr.
  unfold GO2 in Hr. apply mu_den_comma_r in Hr. exact Hr.
Qed.
(** Admitted: as [mu_A_obl_lt_true] with the single fiber [(h1, h2) = (1, 3)];
    [1 <? 3 = true]. *)
Lemma mu_O_obl_lt_true :
  ctx_sub_under ∅ (fv_tm (ret (vfvar lt12)) ∪ fv_cty (bool_precise_ty true)) GO4
    (lt12 ∷ bool_precise_ty true).
Proof. Admitted.
(** Admitted.  In [GO5], [tail12 = h2 :: t = [3;2;4]] (single fiber
    [(3, [2;4])]).  The over part of the source on the single fiber
    [(h1, tail12) = (1, [3;2;4])] makes every result of [e] equal to
    [[1;3;2;4] = cex_out], which is unsorted ([cex_out_not_sorted]); totality
    makes the result-extended world [mν] non-empty.  The split
    [m1 = m2 = mν] witnesses [{ν | ¬sorted ν} ⊕ {ν | ⊤}]: [m1] satisfies the
    closed over qualifier [¬sorted ν], [m2] satisfies [O[List]], and
    [res_sum m1 m2 = mν].  This is exactly the bug of Fig. 8, line 7. *)
Lemma mu_O_obl_unsorted :
  sub_type_under ∅ GO5 (list_cons_precise_ty (vfvar h1) (vfvar tail12)) merge_result_ty.
Proof. Admitted.

Theorem merge_cex_extended_arrow_type : ∅; Emp ⊢ₓ merge_program ⋮ mu_cex_arrow_ty.
Proof.
  rewrite merge_program_unfold.
  mu_unroll.
  eapply EXT_LamNamedErased with (τx := mu_Pc cex_l1) (τ := mu_Pc cex_l2 -∗ merge_result_ty);
    [reflexivity | m2_wf | ].
  eapply EXT_LamDNamedErased with (τx := mu_Pc cex_l2) (τ := merge_result_ty);
    [reflexivity | m2_wf | ].
  fold GO0. unfold rec_body_with.
  eapply EXT_CtxSub with (Γ2 := GO1); [m2_wf | | mu_use_sub mu_O_obl_pat1].
  eapply EXT_ListMatchConsOnlyNamed.
  { m2_wf. }
  { eapply EXT_Sub with (τ1 := list_cons_precise_ty (vfvar h1) (vfvar t1)).
    - m2_wf.
    - eapply EXT_ListCons; [m2_wf | mu_proj_top h1 TNat | mu_proj_top t1 TList].
    - exact mu_O_obl_eq1. }
  eapply EXT_CtxSub with (Γ2 := GO2); [m2_wf | | mu_use_sub mu_O_obl_pat2].
  eapply EXT_ListMatchConsOnlyNamed.
  { m2_wf. }
  { eapply EXT_Sub with (τ1 := list_cons_precise_ty (vfvar h2) (vfvar t2)).
    - m2_wf.
    - eapply EXT_ListCons; [m2_wf | mu_proj_top h2 TNat | mu_proj_top t2 TList].
    - exact mu_O_obl_eq2. }
  eapply EXT_LetNamed with (τ1 := mu_Oc cex_rec).
  { m2_wf. }
  { unfold call2_tm, tapp_tm, case_app.
    eapply EXT_Let with (L := merge_fixed_atoms) (τ1 := mu_T4).
    - m2_wf.
    - replace mu_T4 with (cty_open 0 t1 mu_T4) by (apply mu_closed_open; m2_wf_type).
      eapply EXT_AppFun with (τx := mu_Oc (2%nat :: nil)).
      + m2_wf.
      + rewrite !mu_closed_fv by m2_wf_type. vm_compute. set_solver.
      + eapply EXT_CtxSub with (Γ2 := Emp).
        * m2_wf.
        * exact mu_fix24.
        * apply mu_ctx_sub_emp; [m2_wf_ctx | mu_fv_empty].
      + eapply EXT_CtxSub with (Γ2 := t1 ∷ mu_Oc (2%nat :: nil)).
        * m2_wf.
        * eapply EXT_Var. m2_wf.
        * exact mu_O_obl_proj_t1.
    - intros f Hf.
      cbn [open_one open_tm_atom_inst open_tm open_value value_shift].
      rewrite decide_True by reflexivity.
      replace (mu_Oc cex_rec) with (cty_open 0 t2 (mu_Oc cex_rec))
        by (apply mu_closed_open; m2_wf_type).
      eapply EXT_AppFun with (τx := mu_Oc (4%nat :: nil)).
      + m2_wf.
      + rewrite !mu_closed_fv by m2_wf_type. cbn [fv_value].
        intros Hin. apply Hf. unfold merge_fixed_atoms. set_solver.
      + change (mu_Oc (4%nat :: nil) → mu_Oc cex_rec) with mu_T4. eapply EXT_VarComma. m2_wf.
      + eapply EXT_CtxSub with (Γ2 := t2 ∷ mu_Oc (4%nat :: nil)).
        * m2_wf.
        * eapply EXT_Var. m2_wf.
        * exact (mu_O_obl_proj_t2 f Hf). }
  fold GO3. unfold merge_step_tm.
  eapply EXT_LetNamed with (τ1 := binop_precise_ty bop_lt (vfvar h1) (vfvar h2)).
  { m2_wf. }
  { eapply EXT_BinOp. m2_wf. }
  fold GO4. unfold if_named.
  eapply EXT_MatchTrueOnly.
  { m2_wf. }
  { eapply EXT_CtxSub with (Γ2 := lt12 ∷ bool_precise_ty true).
    - m2_wf.
    - eapply EXT_Var. m2_wf.
    - exact mu_O_obl_lt_true. }
  eapply EXT_LetNamed with (τ1 := list_cons_precise_ty (vfvar h2) (vfvar t)).
  { m2_wf. }
  { eapply EXT_ListCons; [m2_wf | mu_proj_top h2 TNat | mu_proj_top t TList]. }
  fold GO5.
  eapply EXT_Sub with (τ1 := list_cons_precise_ty (vfvar h1) (vfvar tail12)).
  { m2_wf. }
  { eapply EXT_ListCons; [m2_wf | mu_proj_top h1 TNat | mu_proj_top tail12 TList]. }
  exact mu_O_obl_unsorted.
Qed.

(** ** From [→] to the paper's [-∗] at the outer parameter

    [mu_cex_obl_arrow_wand] (PROVED): an instance of the generic
    [mu_sub_arrow_to_wand] ([τx → τ <: τx -∗ τ] in every context, see the
    helper section above).  The argument does not even need the precise
    singleton argument types: the wand only quantifies over argument worlds
    [m'] whose product with the function world [m] adds exactly the fresh
    argument coordinate; world compatibility forces the shared coordinates
    to be constant, so [m' × m] is a full-world extension of [m] and the
    arrow's (stronger, extension-quantified) premise applies to it. *)
Lemma mu_cex_obl_arrow_wand :
  sub_type_under ∅ Emp mu_cex_arrow_ty mu_cex_ty.
Proof.
  unfold mu_cex_arrow_ty, mu_cex_ty.
  apply mu_sub_arrow_to_wand; [m2_wf_ctx | m2_wf_type | m2_wf_type].
Qed.

Theorem merge_cex_extended_type : ∅; Emp ⊢ₓ merge_program ⋮ mu_cex_ty.
Proof.
  eapply EXT_Sub with (τ1 := mu_cex_arrow_ty).
  - m2_wf.
  - exact merge_cex_extended_arrow_type.
  - exact mu_cex_obl_arrow_wand.
Qed.
