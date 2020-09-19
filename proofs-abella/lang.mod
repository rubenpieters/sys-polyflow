module lang.

%% Well-Formed Type

% WF-Top
wft top.

% WF-True
wft tytrue.

% WF-False
wft tyfalse.

% WF-Var
wft X :-
  c_sub X TX.

% WF-Arrow
wft (arrow A B) :-
  wft A,
  wft B.

% WF-All
wft (all TX T) :-
  wft TX,
  pi X\ c_sub X TX => wft (T X).

% WF-Or
wft (or L R) :-
  wft L,
  wft R.

% WF-Rcd
wft (rcd TT TF T) :-
  wft TT,
  wft TF,
  wft T.

%% Subtyping

% SA-Top
sub T top.

% SA-ReflTrue
sub tytrue tytrue.

% SA-ReflFalse
sub tyfalse tyfalse.

% SA-ReflTVar
sub X X :-
  c_sub X TX.

% SA-TransTVar
sub X T :-
  c_sub X TX,
  sub TX T,
  wft TX.

% SA-Arrow
sub (arrow SA SB) (arrow TA TB) :-
  sub TA SA,
  sub SB TB,
  wft SA,
  wft TA,
  wft SB,
  wft TB.

% SA-All
sub (all U (X\ S X)) (all U (X\ T X)) :-
  pi X\ c_sub X U => sub (S X) (T X),
  wft U.

% SA-UnionL
sub T (or L R) :-
  sub T L,
  wft T,
  wft L,
  wft R.

% SA-UnionR
sub T (or L R) :-
  sub T R,
  wft T,
  wft L,
  wft R.

% SA-UnionM
sub (or L R) T :-
  sub L T,
  sub R T,
  wft T,
  wft L,
  wft R.

% SA-ReflMap
sub (rcd TT TF T) (rcd TT TF T) :-
  wft TT,
  wft TF,
  wft T.

% SA-TEvalRead
sub (rcd TT TF T) A :-
%  sub X B,
  teval (rcd TT TF T) read A, % <- TODO: transitive closure
  wft TT,
  wft TF,
  wft T,
  wft X.

% SA-TEvalWrite
sub A (rcd TT TF T) :-
%  sub A X,
  teval (rcd TT TF T) write A, % <- TODO: transitive closure
  wft TT,
  wft TF,
  wft T,
  wft X.

%% Type Evaluation

% TE-MapTrue
teval (rcd TT TF tytrue) A TT :-
  wft TT,
  wft TF.

% TE-MapFalse
teval (rcd TT TF tyfalse) A TF :-
  wft TT,
  wft TF.

% TE-MapUnion
teval (rcd TT TF (or L R)) read (or (rcd TT TF L) (rcd TT TF R)) :-
  wft L,
  wft R,
  wft TT,
  wft TF.

% TE-TVarRead
teval X read U :-
  c_sub X U.

% TE-TVarWrite
%teval X write U :-
%  .

% TE-Map
teval (rcd TT TF T1) A (rcd TT TF T2) :-
  teval T1 A T2.

% TE-Union
teval (or L1 R1) A (or L2 R2) :-
  teval L1 A L2,
  teval R1 A R2.

%% Typing

%- Checking

% BT-Abs
checks (abs A E) (arrow A B) :-
  pi x\ c_of x A => checks (E x) B,
  wft T,
  wft A,
  wft B.

% BT-Sub
checks E T :-
  infers E S,
  sub S T,
  wft S,
  wft T.

%- Inferring

% BT-App
infers (app E1 E2) B :-
  infers E1 (arrow A B),
  checks E2 A,
  wft A,
  wft B.

% BT-TAbs
infers (tabs TX E) (all TX T) :-
  pi X\ c_sub X TX => infers (E X) (T X).

% BT-Tapp
infers (tapp E SX) (T SX) :-
  infers E (all TX T),
  sub SX TX.

% BT-True
infers tmtrue tytrue.

% BT-False
infers tmfalse tyfalse.

% BT-IfTrue
infers (ite (eq X tmtrue) ET EF) (or TT TF) :-
  subt TX => infers ET TT,
  subf TX => infers EF TF,
  c_of X SX,
  c_sub SX TX,
  sub TX (or tytrue tyfalse),
  wft TT,
  wft TF,
  wft TX.

% BT-If
infers (ite C ET EF) (or TT TF) :-
  infers ET TT,
  infers EF TF,
  checks C (or tytrue tyfalse),
  wft TT,
  wft TF,
  wft TC.

% BT-Eq
infers (eq E1 E2) (or tytrue tyfalse).

% BT-Var
infers X TX :-
  c_of X TX,
  wft TX.

% BT-Ann
infers (ann E T) T :-
  checks E T,
  wft T.

%% Condition Information



%% Values

% V-True
value tmtrue.

% V-False
value tmfalse.

% V-Abs
value (abs T E).

% V-Tabs
value (tabs T E).

%% Value Equality

veq tmtrue tmtrue.
veq tmfalse tmfalse.

%% Sim

sim A B :-
  sub A B,
  sub B A.

%% Evaluation

% E-AppAbs
step (app (abs T E1) V2) (E1 V2) :-
  wft T,
  value V2.

% E-App1
step (app E1 E2) (app E1' E2) :-
  step E1 E1'.

% E-App2
step (app V1 E2) (app V1 E2') :-
  value V1,
  step E2 E2'.

% E-TappTabs
step (tapp (tabs T1 E) T2) (E T2).

% E-Tapp
step (tapp E T) (tapp E' T) :-
  step E E'.

% E-IfTrue
step (ite tmtrue ET EF) ET.

% E-IfFalse
step (ite tmfalse ET EF) EF.

% E-If
step (ite E ET EF) (ite E' ET EF).

% E-EqL
step (eq E1 E2) (eq E1' E2).

% E-EqR
step (eq V1 E2) (eq V1 E2') :-
  value V1.

% E-EqTrue
step (eq V1 V2) tmtrue :-
  veq V1 V2.

% E-EqFalse
step (eq V1 V2) tmfalse.

% E-AndFalseL
step (and tmfalse E2) tmfalse.

% E-AndFalseR
step (and E1 tmfalse) tmfalse.

% E-AndTrue
step (and tmtrue tmtrue) tmtrue.

% E-AndL
step (and E1 E2) (and E1' E2):-
  step E1 E1'.

% E-AndR
step (and V1 E2) (and V1 E2') :-
  step E2 E2'.

