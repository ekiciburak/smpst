From mathcomp Require Import all_ssreflect.
From SST Require Import aux.unscoped aux.expressions type.global tree.global tree.local process.processes. 
Require Import List String Datatypes ZArith Relations Setoid Morphisms.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat. 
Require Import JMeq.

Definition P := (p_rec (p_ite (e_var 0) (p_var 0) (p_var 1))).

Example subst1 : substitutionP 0 0 0 P (p_ite (e_var 2) (p_rec (p_ite (e_var 1) (p_var 0) (p_var 1))) (p_var 0)) 
                                       (p_ite (e_var 2) (p_rec (p_ite (e_var 1) (p_var 0) (p_rec (p_ite (e_var 0) (p_var 0) (p_var 2))))) P).
Proof.
  unfold P.
  repeat (constructor; try easy).
Qed.