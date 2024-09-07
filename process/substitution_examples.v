From mathcomp Require Import all_ssreflect.
From SST Require Import src.unscoped src.expressions type.global tree.global tree.local process.processes. 
Require Import List String Datatypes ZArith Relations Setoid Morphisms.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat. 
Require Import JMeq.

Definition E := e_var 0.
Definition P := (p_ite E (p_var 0) (p_ite E (p_var 1) (p_rec (p_ite E (p_var 0) (p_ite E (p_var 1) (p_var 2)))))).

Example subst2 : forall T, substitutionP 0 0 0 (p_rec P) P T -> False.
Proof.
  intros.
  inversion H; subst. 
  inversion H8; subst; try easy.
  inversion H9; subst; try easy.
  inversion H10; subst; try easy.
  inversion H11; subst; try easy.
  inversion H7; subst; try easy.
  inversion H15; subst; try easy.
  inversion H16; subst; try easy.
  inversion H18; subst; try easy.
  inversion H19; subst; try easy.
  clear H9 H11 H15 H16 H7 H18 H19.
  simpl in H.
  
  
  
  

Example subst1 : substitutionP 0 0 0 P (p_ite (e_var 2) (p_rec (p_ite (e_var 1) (p_var 0) (p_var 1))) (p_var 0)) 
                                       (p_ite (e_var 2) (p_rec (p_ite (e_var 1) (p_var 0) (p_rec (p_ite (e_var 0) (p_var 0) (p_var 2))))) P).
Proof.
  unfold P.
  repeat (constructor; try easy).
Qed.