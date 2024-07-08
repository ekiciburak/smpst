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
  simpl in H2. destruct H2. easy.
  destruct IHtyp_proc. simpl in H4. destruct H4. easy. 
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

Lemma alphaP_typ_eq {P Q : process} {em : fin} {Gs : ctxS} {Gt : ctxT} {T : ltt} :
      alphaP P Q -> typ_proc em Gs Gt P T -> typ_proc em Gs Gt Q T.
      intros.
      induction H; intros; try easy.
Admitted.

Lemma alphaP_sym {P Q : process} : alphaP P Q -> alphaP Q P.
Proof.
  intros.
  induction H; intros; try easy.
Admitted.
(* 
Theorem typ_proc_ind:
  forall {em:fin} (P:list X -> Prop),
    P nil ->
    (forall x l, P l -> P (rcons l x)) ->
    forall l, P l.
Proof. Admitted.

 *)
 
(* https://proofassistants.stackexchange.com/questions/1520/strong-induction-for-nat-in-coq *)
Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
    forall n, P n.
Proof.
  intros H n; enough (H0: forall p, p <= n -> P p).
    - apply H0, le_n. 
    - induction n.
      + intros. inversion H0. apply H. intros. inversion H2.
      + intros. apply H. intros. apply IHn.  inversion H0. 
        * rewrite H2 in H1. apply PeanoNat.lt_n_Sm_le in H1. assumption.
        * specialize (PeanoNat.Nat.lt_le_trans k p n H1 H3). apply PeanoNat.Nat.lt_le_incl.
Qed.

Fixpoint process_size (P : process) : fin := 
  match P with 
    | p_var n => 0 
    | p_inact => 0
    | p_send pt lb e p => 1 + process_size p 
    | p_recv pt lb p llb lp => 
      let fix mx_siz lis := 
        match lis with 
          | x::xs => max (process_size x) (mx_siz xs)
          | [] => 0
        end
      in 1 + max (process_size p) (mx_siz lp)
    | p_ite e p1 p2 => 1 + max (process_size p1) (process_size p2)
    | p_rec n p => 1 + (process_size p)
  end.

Lemma psize_exists : forall P, exists n, process_size P = n.
Proof.
  intro P. 
  exists (process_size P). easy.
Qed.

Lemma psize_smaller_rec : forall P n Q k, (P = p_rec n Q) -> (process_size P = k) -> exists l, (process_size Q = l /\ l < k).
Proof.  
  intros. 
  subst.
  specialize(psize_exists Q); intros. destruct H.
  exists x. split. easy.
  simpl. subst.
  specialize(Nat.lt_succ_diag_r (process_size Q)); intros. easy.
Qed.

Lemma subst_inv_rec : forall P n Q X Qb Qa, (P = p_rec n Q) -> substitutionP (p_var X) Qb P Qa -> exists m Q', (Qa = p_rec m Q').
Proof.
  intros.
  

Lemma _a21: forall n P Q em T T' Gs Gt X Q',
  process_size P = n
  -> subtypeC T T'
  -> typ_proc em Gs (extendT Gt X T) P T' -> typ_proc em Gs Gt Q T' 
  -> substitutionP (p_var X) Q P Q'
  -> typ_proc em Gs Gt Q' T'.
Proof. 

  intros n.
  induction n using @strong_ind.
  
  intros.
  induction P.
  admit.
  admit.
  admit.
  admit.
  admit.
  clear IHP.
  specialize(psize_smaller_rec (p_rec n0 P) n0 P n (eq_refl (p_rec n0 P)) H0); intros.
  destruct H5. 
  pose proof H as Hrec.
  destruct H5.
  specialize(_a23_d (p_rec n0 P) em n0 P T' Gs (extendT Gt X T) H2 (eq_refl (p_rec n0 P))); intros.
  destruct H7. destruct H7. destruct H7. destruct H8.
  unfold extendT in *.
  specialize(Hrec x H6); intros.
  specialize(Hrec P Q em); intros.
  
  
  
  specialize(psize_exists P); intro. 
  destruct H.
  
 

  
  intros.
  
  
  
  
  
  
  
  
  (* inact *) 
  intros.
  specialize (_a23_f p_inact em T Gs (extendT Gt X T) H (eq_refl p_inact)); intros.
  subst.
  inversion H1; intros; try easy.
  subst.
  specialize(_typ_consistency_ em Gs Gt Q ltt_end H0); intros.
  destruct H2.
  specialize(tc_inact em Gs Gt H2 H3); intros. easy.
    
  
  (* var *)
  intros.
  specialize(_a23_e (p_var n) em n T Gs (extendT Gt X T) H (eq_refl (p_var n))); intros.
  inversion H1. subst. easy. subst. 
  specialize(not_eq_sym H6); intros.
  specialize(remove_unusedT_var em Gs Gt X n T T H3 H); intros. easy.
  subst. inversion H4.

  (* send *)
  intros. 
  specialize(_a23_b em s n e P (p_send s n e P) Gs (extendT Gt X T) T H (eq_refl (p_send s n e P))); intros.
  destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. destruct H4.
  
  
  
(*   inversion H1; intros; try easy. 
  
  subst.
  specialize(tc_send); intros. *)
  
  
  
  
  admit.
  (* recv *)
  intros. 
  admit.
  
  (* ite *)
  intros.
  
  specialize(_a23_c (p_ite e P1 P2) em e P1 P2 T Gs (extendT Gt X T) H (eq_refl (p_ite e P1 P2))); intros.
  destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5.  

  (* -> want better inversion for subst that doesn't use the alpha case *)
  inversion H1. subst.
  specialize(IHP2 Q em T Gs Gt X Q2); intros.
  specialize(tc_sub em Gs (extendT Gt X T) P2 x0 T H3 H5); intros.
  specialize(IHP2 H7 H0 H14); intros. 
  specialize(IHP1 Q em T Gs Gt X Q1); intros.
  specialize(tc_sub em Gs (extendT Gt X T) P1 x T H2 H4); intros.
  specialize(IHP1 H8 H0 H13); intros.
  specialize(tc_ite em Gs Gt e Q1 Q2 T H6 IHP1 IHP2); intros.
  easy.
  
  inversion H8. subst.
  specialize(alphaP_typ_eq (alphaP_sym H16) H2); intros.
  specialize(alphaP_typ_eq (alphaP_sym H18) H3); intros.
  
  specialize(IHP2 Q em T Gs Gt X P5); intros.
  specialize(tc_sub em Gs (extendT Gt X T) P2 x0 T H3 H5); intros.
  specialize(IHP2 H11 H0 H14); intros. 
  specialize(IHP1 Q em T Gs Gt X Q1); intros.
  specialize(tc_sub em Gs (extendT Gt X T) P1 x T H2 H4); intros.
  specialize(IHP1 H8 H0 H13); intros.
  specialize(tc_ite em Gs Gt e Q1 Q2 T H6 IHP1 IHP2); intros.
  
  
  
  (* mu *)
  intros. 
  specialize(_a23_d); intros.
  
  admit.
   
Admitted.

