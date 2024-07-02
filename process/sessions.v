From SST Require Export aux.unscoped aux.expressions process.processes type.global tree.global.
Require Import List String Relations.
Require Import List String Relations ZArith.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Inductive session: Type :=
  | s_ind : part   -> option process -> session
  | s_par: session -> session -> session.
  

(* Inductive pcong: relation process :=
  | pc_rec  : forall p, pcong (p_rec p) (subst_process ((p_rec p) .: p_var) p). *)

Notation "p '<--' P"   :=  (s_ind p P) (at level 50, no associativity).
Notation "s1 '|||' s2" :=  (s_par s1 s2) (at level 50, no associativity).

Inductive scong: relation session :=
  | sc_multi: forall p P Q M, scongP P Q -> scong (p <-- Some P ||| M) (p <-- Some Q ||| M) 
  | sc_par1 : forall p M, scong (p <-- Some p_inact ||| M) M
  | sc_par2 : forall M M', scong (M ||| M') (M' ||| M)
  | sc_par3 : forall M M' M'', scong ((M ||| M') ||| M'') (M ||| (M' ||| M''))
  | sc_par4 : forall M M' M'', scong ((M ||| M') ||| M'') (M ||| (M'' ||| M')).

(* Declare Instance Equivalence_pcong : Equivalence pcong. *)
Declare Instance Equivalence_scong : Equivalence scong.

Inductive sForall (P: session -> Prop): session -> Prop :=
  | fsind: forall p proc, sForall P (p <-- proc)
  | fspar: forall (S R: session), P S -> P R -> sForall P (S ||| R).
