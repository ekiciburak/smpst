From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck process.inversion type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Lemma _typ_consistency_ : forall em Gs Gt P T, typ_proc em Gs Gt P T -> (consistent_ctxS Gs /\ consistent_ctxT Gt).
intros.
  induction H; intros; try easy.
  destruct IHtyp_proc.
  split; try easy.
  simpl in H1. destruct H1. easy.
  destruct IHtyp_proc.
  simpl in H4. destruct H4.
  split. easy. easy.
Qed.

Lemma trivial_type_inact : forall em Gs Gt T, typ_proc em Gs Gt p_inact T -> T = ltt_end.
Proof.
  intros. 
  specialize(_a23_f p_inact em T Gs Gt H (eq_refl p_inact)); intros.
  easy.
Qed.

Lemma remove_unusedT_inact : forall em Gs Gt X T T',
  typ_proc em Gs (extendT Gt X T) p_inact T' -> typ_proc em Gs Gt p_inact T'.
Proof.
  intros.
  specialize(trivial_type_inact em Gs (extendT Gt X T) T' H); intros. subst.
  specialize(tc_inact em Gs Gt); intros.
  specialize(_typ_consistency_ em Gs (extendT Gt X T) p_inact ltt_end H); intros.
  destruct H1. simpl in H2. destruct H2.
  specialize(H0 H1 H3); intros.
  easy.
Qed.

Lemma remove_unusedT_var : forall em Gs Gt X Y T T',
  Y <> X -> typ_proc em Gs (extendT Gt X T) (p_var Y) T' -> typ_proc em Gs Gt (p_var Y) T'.
Proof.
  intros.
  specialize(_a23_e (p_var Y) em Y T' Gs (extendT Gt X T) H0 (eq_refl (p_var Y))); intros.
  destruct H1. destruct H1. destruct H1.
  unfold eq_ctxT in H1.
  specialize(H1 Y); intros. simpl in H1.
  destruct H1. destruct H1. destruct H3. destruct H3.
  specialize(Nat.eqb_refl Y); intros.
  replace (Y =? Y)%nat with true in H5.
  specialize(Nat.eqb_neq Y X); intros. destruct H8. specialize(H9 H); intros.
  replace (Y =? X)%nat with false in H5.
  
  specialize(tc_var em Gs Gt Y x); intros.
  specialize(_typ_consistency_ em Gs (extendT Gt X T) (p_var Y) T' H0); intros.
  destruct H11. simpl in H12. destruct H12.
  specialize(H10 H11 H13 H5); intros.
  specialize(tc_sub em Gs Gt (p_var Y) x T' H10 H2); intros.
  easy.
Qed.

Lemma _a21: forall P Q em T Gs Gt X Q',
  typ_proc em Gs (extendT Gt X T) P T -> typ_proc em Gs Gt Q T 
  -> substitutionP (p_var X) Q P Q'
  -> typ_proc em Gs Gt Q' T.
Proof. 
  intro P.
  induction P.
  (* var *)
  intros.
  inversion H1. subst. easy. subst. 
  specialize(_a23_e (p_var n) em n T Gs (extendT Gt X T) H (eq_refl (p_var n))); intros.
  specialize(not_eq_sym H5); intros.
  specialize(remove_unusedT_var em Gs Gt X n T T H3 H); intros. easy.
  subst. inversion H3.
  
  (* inact *) 
  intros.
  specialize (_a23_f p_inact em T Gs (extendT Gt X T) H (eq_refl p_inact)); intros.
  subst.
  inversion H1; intros; try easy.
  subst.
  specialize(_typ_consistency_ em Gs Gt Q ltt_end H0); intros.
  destruct H2.
  specialize(tc_inact em Gs Gt H2 H3); intros. easy.
    
  (* send *)
  intros. 
  specialize(_a23_b em s n e P (p_send s n e P) Gs (extendT Gt X T) T H (eq_refl (p_send s n e P))); intros.
  destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. destruct H4.
  
(*   inversion H1; intros; try easy. 
  
  subst.
  specialize(tc_send); intros. *)
  
  
  
  
  admit.
  (* recv *) 
  admit.
  
  (* ite *)
  intros.   
  admit.
  
  (* mu *)
  intros. 
  specialize(_a23_d); intros.
  
  admit.
   
Admitted.

