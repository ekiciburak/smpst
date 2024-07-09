From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck process.inversion type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Lemma _typ_consistency_ : forall em Gs Gt P T, typ_proc em Gs Gt P T -> (consistent_ctxS Gs /\ consistent_ctxT Gt).
intros.
  induction H using typ_proc_ind_ref; intros; try easy.
  destruct IHtyp_proc.
  split; try easy. simpl in H1. destruct H1. easy. 
  destruct H2. 
  - simpl in H. specialize(eq_trans H H0); intros. specialize(eq_trans H2 H1); intros. clear H0 H1.
    specialize(positive_list_length_dst ST 0 (eq_sym H)); intros.
    specialize(positive_list_length_dst Pr 0 (eq_sym H2)); intros.
    specialize(positive_list_length_dst T 0 (eq_sym H4)); intros.
    destruct H0. destruct H0. destruct H1. destruct H1. destruct H5. destruct H5. subst.
    specialize(Forall2_cons_iff (fun (_ : process) (v : sort * ltt) =>
        consistent_ctxS (extendS cs em (fst v)) /\ consistent_ctxT ct) x1 (x,x3) x2 (zip x0 x4)); intros.
    destruct H0. clear H1. specialize(H0 H3); intros. clear H3. destruct H0. destruct H0. 
    simpl in H0. destruct H0. easy.
  - simpl in H. specialize(eq_trans H H0); intros. specialize(eq_trans H5 H1); intros. clear H0 H1.
    specialize(positive_list_length_dst ST (S (length l)) (eq_sym H)); intros.
    specialize(positive_list_length_dst Pr (S (length l)) (eq_sym H5)); intros.
    specialize(positive_list_length_dst T (S (length l)) (eq_sym H6)); intros.
    destruct H0. destruct H0. destruct H1. destruct H1. destruct H7. destruct H7. subst.
    specialize(Forall2_cons_iff (fun (_ : process) (v : sort * ltt) =>
        consistent_ctxS (extendS cs em (fst v)) /\ consistent_ctxT ct) x1 (x,x3) x2 (zip x0 x4)); intros.
    destruct H0. clear H1. specialize(H0 H3); intros. clear H3. destruct H0. destruct H0. 
    simpl in H0. destruct H0. easy.    
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

(* Lemma alphaP_typ_eq {P Q : process} {em : fin} {Gs : ctxS} {Gt : ctxT} {T : ltt} :
      alphaP P Q -> typ_proc em Gs Gt P T -> typ_proc em Gs Gt Q T.
      intros.
      induction H; intros; try easy.
Admitted.
 *)
(* 
Theorem typ_proc_ind:
  forall {em:fin} (P:list X -> Prop),
    P nil ->
    (forall x l, P l -> P (rcons l x)) ->
    forall l, P l.
Proof. Admitted.

 *)

Lemma inv_subst_var : forall x P Q1 Q2 n, wtyped P -> wtyped Q1 -> wtyped Q2 -> substitutionP x P Q1 Q2 -> Q1 = (p_var n)
                 -> (x = n /\ alphaP P Q2) \/ (x <> n /\ Q2 = p_var n).
Proof.
  intros x P Q1 Q2 n WP WQ1 WQ2 H.
  induction H using substitutionP_ind_ref; intros; try easy.
  inversion H. subst. left. split. easy. 
  specialize(alphaP_refl Pr WQ2); intros. easy.
  right. inversion H0. subst. split. easy. easy.
  specialize(IHsubstitutionP WP); intros.
  
Admitted.
 
Lemma inv_subst_inact : forall x P Q1 Q2, substitutionP x P Q1 Q2 -> (Q1 = p_inact) -> Q2 = p_inact.
Proof.
  intros x P Q1 Q2 Hs.
  induction Hs using substitutionP_ind_ref; intros; try easy.
  induction H using alphaP_ind_ref; intros; try easy. 
  specialize(IHHs H1); intros; try easy.
  subst. 
  specialize(inv_alphaP_inact Q2); intros. 
  specialize(alphaP_sym p_inact Q2 H0); intros.
  specialize(H H2); intros; try easy.
Qed.

Lemma inv_subst_rec : forall P X Qb Qa, wtyped Qa -> wtyped Qb -> (exists n Q, P = (p_rec n Q)) -> substitutionP X Qb P Qa -> exists m Q', (Qa = p_rec m Q').
Proof.
  intros. revert H.  
  induction H2 using substitutionP_ind_ref; intros; try easy.
  destruct H1. destruct H1. easy.
  destruct H1. destruct H1. easy.
  destruct H1. destruct H1. easy.
  destruct H1. destruct H1. easy.
  
  destruct H1. destruct H1. 
  exists Y. exists Q1. easy.
  
  destruct H1. destruct H1. subst. 
  specialize(inv_alphaP_rec P1 x x0 H); intros. destruct H1. destruct H1. destruct H1. destruct H1. 
  destruct H4. destruct H5. 
  destruct IHsubstitutionP. easy. exists x1. exists x3. easy. 
  specialize(wtyped_alphaP Q2 Q1 (alphaP_sym Q1 Q2 H2) H3); intros. easy.
  
  destruct H7. subst.  
  specialize(inv_alphaP_rec Q2 x4 x5 (alphaP_sym (p_rec x4 x5) Q2 H2)); intros.
  destruct H1. destruct H1. destruct H1. destruct H1.
  exists x6. exists x8. easy.
Qed.

Lemma typable_implies_wtyped [em : fin] [Gs : ctxS] [Gt : ctxT] [P : process] [T : ltt] : typ_proc em Gs Gt P T -> wtyped P.
Proof.
  intros. induction H using typ_proc_ind_ref.
  apply wp_inact.
  apply wp_var.
  apply wp_rec. easy.
  apply wp_ite; try easy. easy.
  apply wp_recv; try easy. 
  - specialize(eq_trans H H0); intros; try easy.
  - admit.
  apply wp_send; try easy.
Admitted.

Lemma typable_after_subst_list [xs ys : list process] [Pr : process] : wtyped Pr -> Forall2 (fun Q1 Q2 : process => wtyped Pr -> wtyped Q1 -> wtyped Q2) xs ys -> Forall wtyped xs -> Forall wtyped ys.
Proof.
  revert ys.
  induction xs.
  - intros. specialize(Forall2_length H0); intros. 
    simpl in H2.
    specialize(length_zero_iff_nil ys); intros. destruct H3.
    specialize(H3 (eq_sym H2)). subst. easy.
  - intros. 
    specialize(Forall2_length H0); intros. simpl in H2.
    specialize(positive_list_length_dst ys (length xs) (eq_sym H2)); intros.
    destruct H3. destruct H3. subst.
    specialize(Forall2_cons_iff (fun Q1 Q2 : process => wtyped Pr -> wtyped Q1 -> wtyped Q2) a x xs x0); intros.
    destruct H3. specialize(H3 H0). clear H4. destruct H3.
    specialize(Forall_cons_iff wtyped a xs); intros. destruct H5.
    specialize(H5 H1); intros. destruct H5. clear H6. 
    specialize(H3 H H5); intros.
    specialize(IHxs x0 H H4 H7); intros.
    apply Forall_cons. easy. easy.
Qed.

Lemma typable_after_subst [X : fin] [P Q1 Q2 : process] : substitutionP X P Q1 Q2 -> wtyped P -> wtyped Q1 -> wtyped Q2.
Proof.
  intro H. induction H using substitutionP_ind_ref; intros; try easy.
  - inversion H0. subst.
    specialize(IHsubstitutionP H H2); intros.
    apply wp_send. easy.
  - inversion H4. subst.
    apply wp_recv; try easy.
    specialize(typable_after_subst_list H3 H2 H10); intros. easy.
  - inversion H0. subst.
    apply wp_ite. 
    specialize(IHsubstitutionP H H3); intros; try easy.
    specialize(IHsubstitutionP0 H H5); intros; try easy.
  - inversion H2. subst.
    apply wp_rec. 
    specialize(IHsubstitutionP H1 H4); intros; try easy.
  - specialize(wtyped_alphaP P2 P1 (alphaP_sym P1 P2 H) H2); intros.
    specialize(IHsubstitutionP H1 H3); intros.
    specialize(wtyped_alphaP Q1 Q2 H0 IHsubstitutionP); intros. easy.
Qed.

Lemma typable_alpha [em : fin] [Gs : ctxS] [Gt : ctxT] [P1 P2 : process] [T : ltt] :
      alphaP P1 P2 -> typ_proc em Gs Gt P1 T -> typ_proc em Gs Gt P2 T.
Proof.
  intros.
  induction H0 using typ_proc_ind_ref.
Admitted.
  

Lemma _a21: forall P Q em T T' Gs Gt X Q', wtyped Q -> subtypeC T T'
  -> typ_proc em Gs (extendT Gt X T) P T' -> typ_proc em Gs Gt Q T' 
  -> substitutionP X Q P Q'
  -> typ_proc em Gs Gt Q' T'.
Proof. 

  intros P. induction P using process_ind_ref.
  
  (* var *)
  
  intros.
  specialize(inv_subst_var X Q (p_var n) Q' n); intros.
  specialize(typable_implies_wtyped H1); intros.
  specialize(typable_after_subst H3 H H5); intros.
  specialize(H4 H H5 H6 H3); intros.
  destruct H4. easy.
  destruct H4. 
  specialize(typable_alpha H7 H2); intros; try easy.
  destruct H4. subst.
  specialize(remove_unusedT_var em Gs Gt X n T T' (not_eq_sym H4) H1); intros. easy.  
  
  (* inact *)
  intros.
  specialize(inv_subst_inact X Q p_inact Q' H3 (eq_refl p_inact)); intros. subst.
  specialize(remove_unusedT_inact em Gs Gt X T T' H1); intros. easy.
  
  (* send *)
  intros.
  
  (* recv *)
  
  
  (* ite *)
  
  
  (* rec *)
  
  
   
Admitted.

