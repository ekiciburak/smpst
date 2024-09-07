From SST Require Export src.unscoped src.expressions process.processes process.typecheck type.global type.local tree.global tree.local process.beta process.sessions process.inversion.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.



Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H. subst. inversion H1. subst. clear H1. inversion H4. subst. clear H4.
  inversion H3. subst. clear H3. inversion H6. subst. clear H6.
  - destruct H2. destruct H1. destruct H1. destruct H2. inversion H2. subst. clear H2.
    destruct H3. destruct H2. destruct H2. destruct H3. inversion H3. subst. clear H3.
  - specialize(_a23_a q xs (p_recv q xs) nil nil x H4 (eq_refl (p_recv q xs))); intros.
    destruct H3. destruct H3. destruct H7. destruct H8. 
  - specialize(_a23_bf p l e Q (p_send p l e Q) nil nil x0 H6 (eq_refl (p_send p l e Q))); intros.
    destruct H10. destruct H10. destruct H10. destruct H11. 
  - 
  
  admit.
  
  (* T-COND *)
  inversion H. subst. 
  inversion H1. subst. clear H1.
  inversion H4. subst. clear H4. destruct H2. destruct H1. destruct H1. destruct H2.
  inversion H2. subst. clear H2.
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x. exists P.
  split; try easy. split; try easy.
  specialize(_a23_c (p_ite (e_val (vbool true)) P Q) (e_val (vbool true)) P Q x nil nil H3 (eq_refl (p_ite (e_val (vbool true)) P Q))); intros.
  destruct H2. destruct H2. destruct H2. destruct H4. destruct H6.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H3); try easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H. subst. 
  inversion H1. subst. clear H1.
  inversion H4. subst. clear H4. destruct H2. destruct H1. destruct H1. destruct H2.
  inversion H2. subst. clear H2.
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x. exists Q.
  split; try easy. split; try easy.
  specialize(_a23_c (p_ite (e_val (vbool false)) P Q) (e_val (vbool false)) P Q x nil nil H3 (eq_refl (p_ite (e_val (vbool false)) P Q))); intros.
  destruct H2. destruct H2. destruct H2. destruct H4. destruct H6. destruct H7.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H3); try easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(_a22_2 M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(_a22_2 M2' M2 x H4 H0); intros. easy.
  
Admitted.