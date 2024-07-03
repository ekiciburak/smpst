From SST Require Export aux.unscoped aux.expressions process.processes process.sessions.
Require Import List String Relations ZArith.
Require Import Setoid Morphisms Coq.Program.Basics.
Import ListNotations.
Require Import Coq.Init.Datatypes.

Inductive betaP: relation session :=
  | r_comm  : forall p q xs l e Q M,
              betaP ((p <-- Some (p_recv q xs)) ||| (q <-- Some (p_send p l e Q)) ||| M)
                    ((p <-- subst_expr_proc (p_recv q xs) l e) ||| (q <-- Some Q) ||| M)
  | rt_ite  : forall p P Q M,
              betaP ((p <-- Some (p_ite (e_val (vbool true)) P Q)) ||| M) ((p <-- Some P) ||| M)
  | rf_ite  : forall p P Q M,
              betaP ((p <-- Some (p_ite (e_val (vbool false)) P Q)) ||| M) ((p <-- Some Q) ||| M)
  | r_struct: forall M1 M1' M2 M2', scong M1 M1' -> scong M2' M2 -> betaP M1' M2' -> betaP M1 M2.

Declare Instance Equivalence_beta : Equivalence betaP.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Definition beta_multistep := multi betaP.

#[global] Declare Instance RW_scong3: Proper (scong ==> scong ==> impl) betaP.
#[global] Declare Instance RW_scong4: Proper (scong ==> scong ==> impl) beta_multistep.

Definition PAlice: process := 
  p_send "Bob" 1 (e_val (vint 50)) (p_recv "Carol" [(3,p_inact)]).

Definition PBob: process :=
  p_recv "Alice" [(1, p_send "Carol" 2 (e_val (vint 100)) p_inact);
                  (4, p_send "Carol" 2 (e_val (vint 2)) p_inact)
                 ].

Definition PCarol: process :=
  p_recv "Bob" [(2, p_send "Alice" 3 (e_plus (e_var 0) (e_val (vint 1))) p_inact)].

Definition MS: session := ("Alice" <-- Some PAlice) ||| ("Bob" <-- Some PBob) ||| ("Carol" <-- Some PCarol).

Definition MS': session := ("Alice" <-- Some p_inact) ||| ("Bob" <-- Some p_inact) ||| ("Carol" <-- Some p_inact).

Eval compute in (eval_expr (e_plus (e_val (vint 100)) (e_val (vint 5)))).

Example redMS: beta_multistep MS MS'.
Proof. unfold beta_multistep, MS, MS', PAlice, PBob.

       setoid_rewrite sc_par3.
       setoid_rewrite sc_par2.
       setoid_rewrite sc_par4.
       setoid_rewrite <- sc_par3.

       apply multi_step with
       (y := ((("Bob" <-- Some (p_send "Carol" 2 (e_val (vint 100)) p_inact)) |||
              ("Alice" <-- Some (p_recv "Carol" [(3, p_inact)]))) ||| ("Carol" <-- Some PCarol))
       ).
       apply r_comm.
       unfold PCarol.

       setoid_rewrite sc_par2.
       setoid_rewrite <- sc_par3.
       apply multi_step with
       (y := ((("Carol" <-- Some (p_send "Alice" 3 (e_plus (e_val (vint 100)) (e_val (vint 1)))  p_inact)) |||
              ("Bob" <-- Some p_inact)) ||| ("Alice" <-- Some (p_recv "Carol" [(3, p_inact)])))
       ).
       apply r_comm.

       setoid_rewrite sc_par2.
       setoid_rewrite <- sc_par3.
       apply multi_step with
       (y := ((("Alice" <-- Some p_inact) |||
              ("Carol" <-- Some p_inact)) ||| ("Bob" <-- Some p_inact))
       ). simpl.
       apply r_comm.
       apply multi_refl.
Qed.


