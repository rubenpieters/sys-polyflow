Require Import sysf1.
Require Import infra.

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

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> lc_typ T.
Proof.
  intros E T H; induction H; eauto.
Qed.

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G' Hok Heq; subst...
  Case "typ_forall".
    pick fresh Y and apply wf_typ_forall...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (sysf1.empty ++ F ++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "typ_all".
    pick fresh Y and apply wf_typ_forall...
    rewrite <- app_assoc.
    apply H0...
  Case "wf_typ_var".
    analyze_binds H...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 wf_typ (F ++ x ~ bind_typ U ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_forall...
    rewrite <- app_assoc.
    apply H1...
  Case "wf_typ_var".
    analyze_binds H...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (Tsubst_binding P Z) F ++ E) ->
  wf_typ (map (Tsubst_binding P Z) F ++ E) (Tsubst_typ P Z T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl Tsubst_typ...
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_forall...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (Tsubst_binding P Z) (Y ~ bind_sub T1 ++ F) ++ E).
    apply H0...
  - Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_typ_var (map (Tsubst_binding P Z) F ++ E) X (Tsubst_typ P Z T))...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  uniq E ->
  wf_typ E (typ_forall T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (Tsubst_binding U X) nil ++ E).
  eapply wf_typ_subst_tb...
Qed.

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Hint Resolve uniq_from_wf_env : core.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env (x ~ bind_sub T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ X ~ bind_sub V ++ E) ->
  wf_typ E U ->
  wf_env (F ++ X ~ bind_sub U ++ E).
Proof with eauto using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  wf_typ E P ->
  wf_env (map (Tsubst_binding P Z) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl Tsubst_binding...
Qed.

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt_typ (open_tt T (typ_tvar_f Y)) ->
  X `notin` fv_tt_typ T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt_typ T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
  Case "wf_typ_var".
    assert (X0 `in` (dom G))...
    eapply binds_In; eauto.
    assert (X <> X0) by fsetdec. fsetdec.
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (Tsubst_binding P Z) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E S T H.
  induction H...
  Case "sub_trans_tvar".
    intuition eauto.
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_forall...
      destruct (H1 Y)...
      rewrite_env (nil ++ Y ~ bind_sub S1 ++ G).
      apply (wf_typ_narrowing T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_forall...
      destruct (H1 Y)...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ lc_exp e /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E e T H; induction H...
  Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  Case "typing_abs".
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    SCase "Second of original three conjuncts".
      pick fresh x and apply lc_abs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
        destruct (H0 x)...
    SCase "Third of original three conjuncts".
      apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
      rewrite_env (nil ++ G).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ K]].
    inversion K...
  Case "typing_tabs".
    pick fresh Y.
    destruct (H0 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X and apply lc_tabs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        destruct (H0 X)...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_forall...
      destruct (H0 Z)...
  Case "typing_tapp".
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    SCase "Second of original three conjuncts".
      apply lc_tapp...
      eauto using type_from_wf_typ.
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' R3']].
      eapply wf_typ_open; eauto.
  Case "typing_sub".
    repeat split...
    destruct (sub_regular _ _ _ H0)...
Qed.

Lemma value_regular : forall e,
  value e ->
  lc_exp e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  lc_exp e /\ lc_exp e'.
Proof with try solve [auto | intuition auto].
  intros e e' H.
  induction H; assert(J := value_regular); split...
  - Case "red_abs".
    inversion H0. pick fresh y. rewrite (subst_ee_intro y)...
  - Case "red_tabs".
    inversion H0. pick fresh Y. rewrite (subst_te_intro Y); auto.
    apply subst_te_expr; auto.
    assert (e1 = open_te e1 (typ_tvar_f Y)).
    apply open_te_rec_expr; auto.
    symmetry in H7.
    rewrite H7.
    auto.
Qed.

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
