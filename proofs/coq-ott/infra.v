Require Import sysf1.

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

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_typ_wrt_typ_rec j V T = open_typ_wrt_typ_rec i U (open_typ_wrt_typ_rec j V T) ->
  T = open_typ_wrt_typ_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_tt_rec_type : forall T U k,
  lc_typ T ->
  T = open_typ_wrt_typ_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (typ_tvar_f X))...
    apply H0...
Qed.

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt_typ T ->
   T = Tsubst_typ U Z T.
Proof with auto.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (X == Z)...
    contradict H; fsetdec.
Qed.

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  lc_typ P ->
  Tsubst_typ P X (open_typ_wrt_typ_rec k T2 T1) =
    open_typ_wrt_typ_rec k (Tsubst_typ P X T2) (Tsubst_typ P X T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (X0 == X); subst... apply open_tt_rec_type...
Qed.

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  lc_typ P ->
  Tsubst_typ P X (open_tt T1 T2) = open_tt (Tsubst_typ P X T1) (Tsubst_typ P X T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

Lemma test3 : forall X Y (Z1 Z2:typ),
  Y <> X ->
  (if Y == X then Z1 else Z2) = Z2.
intros.
destruct (Y == X).
- subst. destruct H. auto.
- auto.
Qed.

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  lc_typ P ->
  open_tt (Tsubst_typ P X T) (typ_tvar_f Y) = Tsubst_typ P X (open_tt T (typ_tvar_f Y)).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  rewrite (test3 X Y)...
Qed.

Lemma test4 : forall X Y (Z1 Z2:typ),
  Y = X ->
  (if Y == X then Z2 else Z1) = Z2.
intros.
destruct (Y == X).
- auto.
- contradict H. auto.
Qed.

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt_typ T2 ->
  open_typ_wrt_typ_rec k U T2 = Tsubst_typ U X (open_typ_wrt_typ_rec k (typ_tvar_f X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst... simpl. rewrite test4...
  Case "typ_fvar".
    destruct (X0 == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt_typ T2 ->
  open_tt T2 U = Tsubst_typ U X (open_tt T2 (typ_tvar_f X)).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_exp_wrt_exp_rec j u e = open_exp_wrt_typ_rec i P (open_exp_wrt_exp_rec j u e) ->
  e = open_exp_wrt_typ_rec i P e.
Proof with congruence || eauto.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_exp_wrt_typ_rec j Q e = open_exp_wrt_typ_rec i P (open_exp_wrt_typ_rec j Q e) ->
  e = open_exp_wrt_typ_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  lc_exp e ->
  e = open_exp_wrt_typ_rec k U e.
Proof.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    unfold open_exp_wrt_exp in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := var_f x);
    auto
  | unfold open_exp_wrt_typ in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_tvar_f X);
    auto
  ].
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_tt_exp e ->
  e = Tsubst_exp U X e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  lc_typ U ->
  Tsubst_exp U X (open_exp_wrt_typ_rec k T e) =
  open_exp_wrt_typ_rec k (Tsubst_typ U X T) (Tsubst_exp U X e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  lc_typ U ->
  Tsubst_exp U X (open_te e T) = open_te (Tsubst_exp U X e) (Tsubst_typ U X T).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  lc_typ U ->
  open_te (Tsubst_exp U X e) (typ_tvar_f Y) = Tsubst_exp U X (open_te e (typ_tvar_f Y)).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  rewrite (test3 X Y)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_tt_exp e ->
  open_exp_wrt_typ_rec k U e = Tsubst_exp U X (open_exp_wrt_typ_rec k (typ_tvar_f X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X `notin` fv_tt_exp e ->
  open_te e U = Tsubst_exp U X (open_te e (typ_tvar_f X)).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_exp_wrt_exp_rec j v e = open_exp_wrt_exp_rec i u (open_exp_wrt_exp_rec j v e) ->
  e = open_exp_wrt_exp_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_exp_wrt_typ_rec j V e = open_exp_wrt_exp_rec i u (open_exp_wrt_typ_rec j V e) ->
  e = open_exp_wrt_exp_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
  lc_exp e ->
  e = open_exp_wrt_exp_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_exp_wrt_exp in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := var_f x);
    auto
  | unfold open_exp_wrt_typ in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_tvar_f X);
    auto
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee_exp e ->
  e = tsubst_exp u x e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (x0==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  lc_exp u ->
  tsubst_exp u x (open_exp_wrt_exp_rec k e2 e1) =
    open_exp_wrt_exp_rec k (tsubst_exp u x e2) (tsubst_exp u x e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (x0 == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  lc_exp u ->
  tsubst_exp u x (open_ee e1 e2) =
    open_ee (tsubst_exp u x e1) (tsubst_exp u x e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma test5 : forall X Y (Z1 Z2:exp),
  Y <> X ->
  (if Y == X then Z1 else Z2) = Z2.
intros.
destruct (Y == X).
- subst. destruct H. auto.
- auto.
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  lc_exp u ->
  open_ee (tsubst_exp u x e) (var_f y) = tsubst_exp u x (open_ee e (var_f y)).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  rewrite (test5 x y)...
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
  Tsubst_exp Z P (open_exp_wrt_exp_rec k e2 e1) =
    open_exp_wrt_exp_rec k (Tsubst_exp Z P e2) (Tsubst_exp Z P e1).
Proof with auto.
  induction e1; intros e2 Z P k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
  Tsubst_exp Z P (open_ee e1 e2) = open_ee (Tsubst_exp Z P e1) (Tsubst_exp Z P e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
  open_ee (Tsubst_exp Z P e) (var_f x) = Tsubst_exp Z P (open_ee e (var_f x)).
Proof with auto.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u k,
  lc_exp u ->
  tsubst_exp u z (open_exp_wrt_typ_rec k P e) = open_exp_wrt_typ_rec k P (tsubst_exp u z e).
Proof with auto.
  induction e; intros P z u k H; simpl; f_equal...
  Case "exp_fvar".
    destruct (x == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
  lc_exp u ->
  tsubst_exp u z (open_te e P) = open_te (tsubst_exp u z e) P.
Proof with auto.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u e,
  lc_exp u ->
  open_te (tsubst_exp u z e) (typ_tvar_f X) = tsubst_exp u z (open_te e (typ_tvar_f X)).
Proof with auto.
  intros z X u e H.
  rewrite subst_ee_open_te...
Qed.

Lemma test6 : forall X Y (Z1 Z2:exp),
  Y = X ->
  (if Y == X then Z1 else Z2) = Z1.
intros.
destruct (Y == X).
- auto.
- destruct n. auto.
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee_exp e ->
  open_exp_wrt_exp_rec k u e = tsubst_exp u x (open_exp_wrt_exp_rec k (var_f x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. rewrite (test6 x x); auto.
  Case "exp_fvar".
    destruct (x0 == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee_exp e ->
  open_ee e u = tsubst_exp u x (open_ee e (var_f x)).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.

Lemma subst_tt_type : forall Z P T,
  lc_typ T ->
  lc_typ P ->
  lc_typ (Tsubst_typ P Z T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_fvar".
    destruct (X == Z)...
  Case "type_all".
    pick fresh Y and apply lc_typ_forall...
    rewrite subst_tt_open_tt_var...
Qed.

Lemma subst_te_expr : forall Z P e,
  lc_exp e ->
  lc_typ P ->
  lc_exp (Tsubst_exp P Z e).
Proof with eauto using subst_tt_type.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_tt_type;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_te_open_ee_var;
    try rewrite subst_te_open_te_var;
    instantiate;
    eauto using subst_tt_type
  ].
Qed.

Lemma subst_ee_expr : forall z e1 e2,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (tsubst_exp e2 z e1).
Proof with auto.
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    instantiate;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
Qed.

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> lc_exp (open_ee e (var_f x)).

Lemma open_ee_body_e : forall e1 e2,
  body_e e1 -> lc_exp e2 -> lc_exp (open_ee e1 e2).
Proof.
  intros e1 e2 [L H] J.
  pick fresh x.
  rewrite (subst_ee_intro x); auto using subst_ee_expr.
Qed.

Hint Resolve subst_tt_type subst_te_expr subst_ee_expr : core.

Hint Resolve open_ee_body_e : core.

Hint Extern 1 (binds _ (?F (Tsubst_typ ?U ?X ?T)) _) =>
  unsimpl (Tsubst_binding U X (F T)) : core.