From mathcomp Require Import all_ssreflect.
From SST Require Import aux.unscoped aux.expressions process.processes_bruijn process.typecheck_bruijn process.inversion_bruijn type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.


Fixpoint RemoveT (n : fin) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: RemoveT m xs
        | 0   => None :: xs 
      end
    | [] => []
  end.

Fixpoint extendT (n : fin) (T : ltt) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: extendT m T xs
        | 0   => Some T :: xs 
      end 
    | [] =>
      match n with 
        | S m => None :: extendT m T [] 
        | 0   => [Some T]
      end 
  end.
  
Lemma onth_nil : forall n, @onth ltt n [] = None.
Proof.
  intros. induction n. easy. easy.
Qed.

Lemma remove_var : forall X n T Gt x, X <> n -> onth n (extendT X T Gt) = Some x -> onth n Gt = Some x.
Proof.
  intros X n T Gt. revert X T Gt. induction n; intros; try easy.
  destruct X; try easy. destruct Gt. easy. simpl in H0. simpl. easy.
  destruct X. destruct Gt; try easy. simpl in H0. simpl. 
  specialize(onth_nil n); intros.
  specialize(eq_trans (ssrfun.esym H1) H0); intros. easy.
  specialize(Nat.succ_inj_wd_neg X n); intros. destruct H1. 
  specialize(H1 H); intros. clear H2.
  destruct Gt. 
  - simpl in H0.
    specialize(IHn X T [] x H1 H0); intros.
    specialize(onth_nil n); intros.
    specialize(eq_trans (ssrfun.esym H2) IHn); intros. easy.
  - simpl in *. 
    apply IHn with (X := X) (T := T); try easy.
Qed.

Lemma extend_extract : forall n (T : ltt) Gt, onth n (extendT n T Gt) = Some T.
Proof.
  intro n. induction n using strong_ind.
  intros t gt. revert t. induction gt.
  - intros. destruct n. easy.
    simpl. apply H; try easy. apply Nat.lt_succ_diag_r.
  - intros. destruct n. easy.
    simpl. apply H; try easy. apply Nat.lt_succ_diag_r.
Qed.

Lemma positive_list_length_dst {A} : forall (xs : list A) n, length xs = S(n) -> exists y ys, y::ys = xs.
Proof.
  intros.
  induction xs. easy.
  exists a. exists xs. easy.
Qed.

Lemma positive_list_length_dst_zip {A B} : forall (xs : list A) (ys : list B) n, length (zip xs ys) = S n -> exists t ts u us, (t,u) :: zip ts us = zip xs ys.
Proof.
  intros. 
  specialize(positive_list_length_dst (zip xs ys) n H); intros.
  destruct H0. destruct H0.
  exists x.1. exists (list_map fst x0). exists x.2. exists (list_map snd x0).
  specialize(unzip_zip x0); intros. 
  replace (zip (list_map fst x0) (list_map snd x0)) with x0.
  specialize(surjective_pairing x); intros. 
  replace (x.1, x.2) with x. easy.
Qed.

Lemma slideT : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc Gs (tm :: Gt) (incr_free 0 0 X.+1 m Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(_a23_e (p_var (n + X)%coq_nat) (n + X)%coq_nat T Gs Gt H (erefl (p_var (n + X)%coq_nat))); intros.
    destruct H0. destruct H0.
    apply tc_sub with (t := x); intros; try easy.
    apply tc_var. 
    specialize(Nat.add_succ_r n X); intros. 
    replace ((n + X.+1)%coq_nat) with ((n + X)%coq_nat.+1). easy.
  - simpl in *. 
    specialize(_a23_f p_inact T Gs Gt H (erefl p_inact)); intros. subst.
    apply tc_inact.
  - simpl in *.
    specialize(_a23_bf pt lb (incr_freeE 0 m ex) (incr_free 0 0 X m Q) (p_send pt lb (incr_freeE 0 m ex) (incr_free 0 0 X m Q)) Gs Gt T H (erefl (p_send pt lb (incr_freeE 0 m ex) (incr_free 0 0 X m Q)))); intros.
    destruct H0. destruct H0. destruct H0. destruct H1. 
    apply tc_sub with (t := (ltt_send pt [(lb, (x, x0))])).
    apply tc_send; try easy.
    apply IHQ. easy. easy.
  - simpl in *.
    specialize(_a23_a pt llb (list_map (incr_free 0 1 X m) llp) (p_recv pt llb (list_map (incr_free 0 1 X m) llp)) Gs Gt T H0 (erefl (p_recv pt llb (list_map (incr_free 0 1 X m) llp)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
    apply tc_sub with (t := (ltt_recv pt (zip llb (zip x0 x)))); try easy.
    apply tc_recv; try easy.
    

Admitted.

Lemma slideS : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc (tm :: Gs) Gt (incr_free 0 0 X m.+1 Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.

Admitted.

Lemma _a21_recv_helper : forall llp X m n Q T Gs Gt x x0 ys,
  wtyped Q ->
  onth X Gt = None ->
  typ_proc Gs Gt (incr_free 0 0 m n Q) T ->
  Forall
      (fun P : process =>
       forall (Q : process) (T T' : ltt) (Gs : ctxS) (Gt : ctxT) 
         (X : fin) (Q' : process) (m n : fin),
       wtyped Q ->
       typ_proc Gs (extendT X T Gt) P T' ->
       onth X Gt = None ->
       substitutionP X m n Q P Q' ->
       typ_proc Gs Gt (incr_free 0 0 m n Q) T -> typ_proc Gs Gt Q' T') llp ->
  Forall2
        (fun (u : process) (v : sort * ltt) =>
         typ_proc (Some v.1 :: Gs) (extendT X T Gt) u v.2) llp 
        (zip x0 x) ->
  Forall2 (substitutionP X m n.+1 Q) llp ys ->
  Forall2 (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gs) Gt u v.2) ys
  (zip x0 x).
Proof.
  intro llp. induction llp; intros; try easy.
  specialize(Forall2_length H3); intros. simpl in H5.
  specialize(Forall2_length H4); intros. simpl in H6.
  specialize(length_zero_iff_nil (zip x0 x)); intros. destruct H7. specialize(H7 (esym H5)); intros.
  specialize(length_zero_iff_nil ys); intros. destruct H9. specialize(H9 (esym H6)); intros.
  subst. replace (zip x0 x) with (@nil (sort * ltt)). easy.
  
  specialize(Forall2_length H3); intros. simpl in H5.
  specialize(positive_list_length_dst_zip x0 x (length llp) (esym H5)); intros.
  destruct H6. destruct H6. destruct H6. destruct H6.
  replace (zip x0 x) with ((x1, x3) :: zip x2 x4) in *. simpl in *.
  specialize(Forall2_length H4); intros. simpl in H7.
  specialize(positive_list_length_dst ys (length llp) (esym H7)); intros.
  destruct H8. destruct H8. subst. clear H5 H6 H7.
  specialize(Forall2_cons_iff (fun (u : process) (v : sort * ltt) =>
       typ_proc (Some v.1 :: Gs) (extendT X T Gt) u v.2) a (x1,x3) llp (zip x2 x4)); intros.
  destruct H5. specialize(H5 H3); intros. clear H6 H3. destruct H5.
  specialize(Forall2_cons_iff (substitutionP X m n.+1 Q) a x5 llp x6); intros.
  destruct H6. specialize(H6 H4); intros. clear H7 H4. destruct H6.
  specialize(Forall_cons_iff (fun P : process =>
        forall (Q : process) (T T' : ltt) (Gs : ctxS) (Gt : ctxT) 
          (X : fin) (Q' : process) (m n : fin),
        wtyped Q ->
        typ_proc Gs (extendT X T Gt) P T' ->
        onth X Gt = None ->
        substitutionP X m n Q P Q' ->
        typ_proc Gs Gt (incr_free 0 0 m n Q) T -> typ_proc Gs Gt Q' T') a llp); intros.
  destruct H7. specialize(H7 H2); intros. clear H8 H2. destruct H7.
  specialize(H2 Q T (x1, x3).2 (Some (x1, x3).1 :: Gs) Gt X x5 m n.+1 H H3 H0 H4); intros.
  specialize(IHllp X m n Q T Gs Gt x4 x2 x6 H H0 H1 H7 H5 H6); intros.
  apply Forall2_cons; try easy.
  apply H2.
  apply slideS; try easy.
Qed. 

Lemma _a21: forall P Q T T' Gs Gt X Q' m n, wtyped Q 
  -> typ_proc Gs (extendT X T Gt) P T' -> onth X Gt = None 
  -> substitutionP X m n Q P Q' -> typ_proc Gs Gt (incr_free 0 0 m n Q) T
  -> typ_proc Gs Gt Q' T'.
Proof. 

  intros P. induction P using process_ind_ref.
  
  (* var *)
  
  intros.
  inversion H2. subst.
  specialize(_a23_e (p_var n) n T' Gs (extendT n T Gt) H0 (erefl (p_var n))); intros.
  destruct H4. destruct H4.
  specialize(extend_extract n T Gt); intros.
  specialize(eq_trans (esym H4) H6); intros. inversion H7. subst.
  apply tc_sub with (t := T); intros; try easy.
  
  subst.
  specialize(_a23_e (p_var n) n T' Gs (extendT X T Gt) H0 (erefl (p_var n))); intros.
  destruct H4. destruct H4.
  apply tc_sub with (t := x); try easy.
  apply tc_var.
  apply ssrfun.esym. apply remove_var with (X := X) (T:= T); try easy.
  
  (* inact *)
  intros.
  inversion H2. subst.
  specialize(_a23_f p_inact T' Gs (extendT X T Gt) H0 (erefl p_inact)); intros. subst.
  apply tc_inact.
  
  (* send *)
  intros. 
  inversion H2. subst.
  specialize(_a23_bf pt lb ex P (p_send pt lb ex P) Gs (extendT X T Gt) T' H0 (erefl (p_send pt lb ex P))); intros. 
  destruct H4. destruct H4. destruct H4. destruct H5. 
  specialize(IHP Q T x0 Gs Gt X Q'0 m n H H5 H1 H13 H3); intros.
  apply tc_sub with (t := (ltt_send pt [(lb, (x, x0))])); try easy.
  apply tc_send; try easy.
  
  (* recv *)
  intros.
  inversion H3. subst.
  specialize(_a23_a pt llb llp (p_recv pt llb llp) Gs (extendT X T Gt) T' H1 (erefl (p_recv pt llb llp))); intros.
  destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H9. destruct H10.
  apply tc_sub with (t := (ltt_recv pt (zip llb (zip x0 x)))); try easy.
  specialize(eq_trans (esym H5) H6); intros.
  specialize(eq_trans (esym H12) H13); intros.
  specialize(eq_trans H5 H13); intros.
  apply tc_recv; try easy.
  apply _a21_recv_helper with (llp := llp) (m := m) (n := n) (Q := Q) (X := X) (T := T); try easy.
  
  (* ite *)
  intros. 
  inversion H2. subst.
  specialize(_a23_c (p_ite e P1 P2) e P1 P2 T' Gs (extendT X T Gt) H0 (erefl (p_ite e P1 P2))); intros.
  destruct H4. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. 
  specialize(IHP1 Q T x Gs Gt X Q1 m n H H4 H1 H12 H3); intros.
  specialize(IHP2 Q T x0 Gs Gt X Q2 m n H H5 H1 H13 H3); intros.
  apply tc_ite; intros; try easy.
  apply tc_sub with (t := x); intros; try easy.
  apply tc_sub with (t := x0); intros; try easy. 
    
  (* rec *)
  intros.
  inversion H2. subst.
  specialize(_a23_d (p_rec P) P T' Gs (extendT X T Gt) H0 (erefl (p_rec P))); intros.
  destruct H4. destruct H4. destruct H4. destruct H5.
  specialize(IHP Q T x0 Gs (Some x :: Gt) X.+1 Q'0 m.+1 n H H4 H1 H9); intros.
  apply tc_sub with (t := x0); try easy.
  apply tc_mu with (t := x); try easy.
  apply IHP.
  apply slideT; try easy. 
Qed.

Lemma typable_implies_wtyped [Gs : ctxS] [Gt : ctxT] [P : process] [T : ltt] : typ_proc Gs Gt P T -> wtyped P.
Proof.
  intros. induction H using typ_proc_ind_ref.
  apply wp_inact.
  apply wp_var.
  apply wp_rec. easy.
  apply wp_ite; try easy. easy.
  apply wp_recv; try easy. 
  - specialize(eq_trans H H0); intros; try easy. 
(*     apply (Forall2_to_Forall H3).
  apply wp_send; try easy.
Qed. *)
Admitted.

Lemma trivial_incr : forall m n Q, (incr_free m n 0 0 Q) = Q.
Proof.
  intro. induction Q using process_ind_ref; intros; simpl; try easy.
  - destruct (m <= n0); try easy.
     
Admitted.

Lemma _a21f : forall P Q T T' Gs Gt X Q',
     typ_proc Gs (extendT X T Gt) P T' -> onth X Gt = None 
  -> substitutionP X 0 0 Q P Q' -> typ_proc Gs Gt Q T
  -> typ_proc Gs Gt Q' T'.
Proof.
  intros.
  apply _a21 with (P := P) (Q := Q) (T := T) (X := X) (m := 0) (n := 0); try easy.
  apply typable_implies_wtyped with (Gs := Gs) (Gt := Gt) (T := T). easy.
  specialize(trivial_incr 0 0 Q); intros. 
  replace (incr_free 0 0 0 0 Q) with Q. easy.
Qed.
