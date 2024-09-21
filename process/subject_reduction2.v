From SST Require Export src.unscoped src.expressions process.processes process.typecheck type.global type.local tree.global tree.local process.beta process.sessions process.inversion.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.

Lemma _a_20_sp : forall G p q l e xs M Q,
  typ_sess (((p <-- p_recv q xs) ||| (q <-- p_send p l e Q)) ||| M) G -> 
  exists ys S G', typ_sess (((p <-- p_recv q xs) ||| (q <-- p_send p l e Q)) ||| M) (gtt_send p q ys) /\ onth l ys = Some (S, G').
Admitted.

Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  specialize(_a_20_sp G p q l e xs M Q H1); intros. 
  - destruct H2. destruct H2. destruct H2. destruct H2.
  exists x1.
  - inversion H2. subst. 
    - inversion H6. subst. clear H6. inversion H9. subst. clear H9.
    - inversion H8. subst. clear H8. destruct H7. destruct H6.
    - inversion H11. subst. clear H11. destruct H9. destruct H8.
  
  split.
  
  
  apply multiC_step with (G2 := x6) (p := q) (q := p) (n := l). easy. apply multiC_refl.
  
  (* T-COND *)
  inversion H0. subst. 
  inversion H3. subst. clear H3.
  inversion H6. subst. clear H6. destruct H4. destruct H3. 
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H4 (eq_refl (p_ite e P Q))); intros.
  destruct H5. destruct H5. destruct H5. destruct H6. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H4); try easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. 
  inversion H3. subst. clear H3.
  inversion H6. subst. clear H6. destruct H4. destruct H3. 
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H4 (eq_refl (p_ite e P Q))); intros.
  destruct H5. destruct H5. destruct H5. destruct H6. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H4); try easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(_a22_2 M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(_a22_2 M2' M2 x H4 H0); intros. easy.
  
Admitted.