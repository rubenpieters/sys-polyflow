Require Import sysf1.
Require Import infra.
Require Import lemmas.

Require Export Metalib.Metatheory.
Require Export String.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_tt_exp x) in
  let D := gather_atoms_with (fun x : exp => fv_ee_exp x) in
  let E := gather_atoms_with (fun x : typ => fv_tt_typ x) in
  let F := gather_atoms_with (fun x : ctx => dom x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F).

Hint Resolve subst_tt_type subst_te_expr subst_ee_expr : core.

Hint Resolve open_ee_body_e : core.

Hint Extern 1 (binds _ (?F (Tsubst_typ ?U ?X ?T)) _) =>
  unsimpl (Tsubst_binding U X (F T)) : core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end : core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end : core.

Hint Extern 1 (lc_typ ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end : core.

Hint Extern 1 (lc_exp ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end : core.
  
Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof with eauto.
  intros E T Ok Wf.
  induction Wf...
  pick fresh Y and apply sub_forall...
Qed.

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G' Ok EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar (G' ++ F ++ E) X T2 T1)...
  Case "sub_all".
    pick fresh Y and apply sub_forall...
    rewrite <- app_assoc.
    apply H0...
Qed.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_trans_tvar P); [ eauto using fresh_mid_head | ].
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ Z ~ bind_sub P) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        analyze_binds_uniq H.
        injection BindsTacVal; intros; subst...
    SCase "X <> Z".
      apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.