sig lang.

kind     tm, ty          type.
kind     temode          type.
kind     condinfo        type.

%% Types

% Top
type     top             ty.
% True
type     tytrue          ty.
% False
type     tyfalse         ty.
% A => B
type     arrow           ty -> ty -> ty.
% ∀(X <: TX) . T
type     all             ty -> (ty -> ty) -> ty.
% L ∨ R
type     or              ty -> ty -> ty.
% { true: TT, false: TF }[T]
type     rcd             ty -> ty -> ty -> ty.

%% Terms

% true
type     tmtrue          tm.
% false
type     tmfalse         tm.
% x : T
% type     ann             tm -> ty -> tm.
% λx . t : A -> B
type     abs             (tm -> tm) -> ty -> ty -> tm.
% t t
type     app             tm -> tm -> tm.
% Λ(X <: T) . t
type     tabs            ty -> (ty -> tm) -> tm.
% t [ T ]
type     tapp            tm -> ty -> tm.
% if cond then tt else tf
type     ite             tm -> tm -> tm -> tm.
% x == y
type     eq              tm -> tm -> tm.
% x && y
type     and             tm -> tm -> tm.

%% Type Evaluation Mode

type     read            temode.
type     write           temode.

%% Condition Information

type     s_empty         condinfo.
type     s_true          condinfo.
type     s_false         condinfo.
type     s_true_false    condinfo.

%% Relations

type     sub             ty -> ty -> o.
type     c_sub           condinfo -> ty -> ty -> o.
type     subt, subf      ty -> o.
type     checks, infers  tm -> ty -> o.
type     c_of            tm -> ty -> o.
type     value           tm -> o.
type     step            tm -> tm -> o.
type     teval           ty -> temode -> ty -> o.
type     veq             tm -> tm -> o.
type     sim             ty -> ty -> o.
type     wft             ty -> o.

