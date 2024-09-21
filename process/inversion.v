From SST Require Import src.expressions process.processes process.typecheck type.global type.local type.isomorphism.
From mathcomp Require Import ssreflect.seq.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Import ListNotations.
From Paco Require Import paco.


Lemma mon_lttT : monotone2 lttT.
Proof.
  unfold monotone2. intros. induction IN; intros; try easy.
  - apply lttT_end.
  - apply lttT_send; try easy.
    - revert H LE. revert r r' p ys.
      induction xs; intros; try easy.
      destruct ys; try easy.
      destruct ys; try easy.
      inversion H. subst.
      constructor.
      - destruct H3. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x0. exists x1. split; try easy. split; try easy.
        apply LE; try easy.
      - apply IHxs with (r := r); try easy.
  - apply lttT_recv; try easy.
    - revert H LE. revert r r' p ys.
      induction xs; intros; try easy.
      destruct ys; try easy.
      destruct ys; try easy.
      inversion H. subst.
      constructor.
      - destruct H3. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x0. exists x1. split; try easy. split; try easy.
        apply LE; try easy.
      - apply IHxs with (r := r); try easy.
  - apply lttT_rec with (Q := Q); try easy.

Qed.

Lemma triad_le :  forall m t',
                  is_true (ssrnat.leq m t') ->
                  is_true (ssrnat.leq (S t') m) -> False.
Proof.
Admitted.
  

Lemma subst_injL : forall m n G G1 Q Q0, subst_local m n G G1 Q0 -> subst_local m n G G1 Q -> Q = Q0.
Proof.
  intros m n G G1.
  revert m n G. induction G1 using local_ind_ref; intros; try easy.
  inversion H. subst. 
  - inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy.
    subst. specialize(triad_le m t' H6 H8); try easy.
  - subst. inversion H0; try easy. 
    subst. specialize(triad_le m t' H8 H6); try easy.
  
  inversion H. subst. inversion H0. subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H8 H9. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H8 H9. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H. subst. inversion H0. subst.
  specialize(IHG1 (S m) (S n) G Q1 Q0 H6 H5). subst. easy.
Qed.

Lemma wfL_after_incr : forall G1 m n,
     wfL G1 -> wfL (incr_freeL m n G1).
Proof.
  induction G1 using local_ind_ref; intros; try easy.
  - simpl in *.
    constructor.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H5. subst.
      specialize(SList_f a lis H2); intros.
      destruct H.
      - assert (wfL (incr_freeL m n (l_send p lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst. inversion H5. subst.
          constructor; try easy.
        }
        destruct H6. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H2 H7 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          constructor; try easy. left. easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeL m n x0). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H6. destruct H6. destruct H6. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H2 H8 H7 H1. clear x x0 p.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeL m n x0).
          split; try easy.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst. 
          apply H6; try easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x1. exists (incr_freeL m n x2). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H. destruct H1. subst.
          destruct H6; try easy. destruct H. destruct H. destruct H. subst.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. 
          replace (Some x) with (Some (x2, x3)) in *. inversion H. subst. clear H H3 H4 H7 H5.
          constructor; try easy. constructor; try easy.
          right. exists x0. exists (incr_freeL m n x1).
          split; try easy. apply H6; try easy.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H5. subst.
      specialize(SList_f a lis H2); intros.
      destruct H.
      - assert (wfL (incr_freeL m n (l_recv p lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst. inversion H5. subst.
          constructor; try easy.
        }
        destruct H6. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H2 H7 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          constructor; try easy. left. easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeL m n x0). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H6. destruct H6. destruct H6. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H2 H8 H7 H1. clear x x0 p.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeL m n x0).
          split; try easy.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst. 
          apply H6; try easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x1. exists (incr_freeL m n x2). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H. destruct H1. subst.
          destruct H6; try easy. destruct H. destruct H. destruct H. subst.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. 
          replace (Some x) with (Some (x2, x3)) in *. inversion H. subst. clear H H3 H4 H7 H5.
          constructor; try easy. constructor; try easy.
          right. exists x0. exists (incr_freeL m n x1).
          split; try easy. apply H6; try easy.
  - inversion H. subst.
    constructor; try easy. apply IHG1; try easy.
Qed.
        
  
Lemma wfL_after_subst : forall Q G1 G2 m n,
    wfL G1 -> wfL G2 -> subst_local m n G1 G2 Q -> wfL Q.
Proof.
  induction Q using local_ind_ref; intros; try easy.
  - apply wfl_var.
  - apply wfl_end.
  - inversion H2; try easy. 
    - subst.
      apply wfL_after_incr. easy.
    - subst.
      inversion H1. subst.
      revert H H0 H1 H2 H8 H5 H6.
      revert p G1 m n xs.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H5); intros. clear H5.
        inversion H8. subst. clear H8. inversion H6. subst. clear H6.
        destruct H3.
        - constructor; try easy. apply SList_b.
          {
            clear IHlis H H0 H1 H2 H9 H7 H8. revert H11 H3. revert xs.
            induction lis; intros; try easy.
            destruct xs; try easy.
            inversion H11. subst.
            specialize(SList_f x l H3); intros. destruct H. 
            - apply SList_b. apply IHlis with (xs := l); try easy.
            - destruct H. destruct H0. subst. destruct lis; try easy.
              destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst. easy.
          } 
        - inversion H. subst. clear H.
          assert (wfL (l_send p lis)). 
          {
            apply IHlis with (G1 := G1) (m := m) (n := n) (xs := xs); try easy.
            inversion H1. subst. inversion H12. subst. clear H12.
            constructor; try easy.
            inversion H2. subst. inversion H13. subst. clear H13.
            constructor; try easy.
          }
          inversion H. subst. constructor; try easy.
          clear H11 H8 H10 H12 H13 IHlis.
          destruct H6.
          - left. easy.
          - right. destruct H4. destruct H4. destruct H4. subst.
            destruct H9; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H6. inversion H6. subst.
            exists x1. exists x3. split; try easy.
            destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
            specialize(H5 G1 x0 m n). apply H5; try easy.
        - destruct H3. destruct H4. subst.
          destruct H9; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
          destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
          destruct lis; try easy.
          constructor; try easy. constructor; try easy. right.
          exists x. exists x2. split; try easy.
          inversion H. subst. clear H. destruct H10; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          specialize(H7 G1 x3 m n). apply H7; try easy.
  - inversion H2; try easy. 
    - subst.
      apply wfL_after_incr. easy.
    - subst.
      inversion H1. subst.
      revert H H0 H1 H2 H8 H5 H6.
      revert p G1 m n xs.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H5); intros. clear H5.
        inversion H8. subst. clear H8. inversion H6. subst. clear H6.
        destruct H3.
        - constructor; try easy. apply SList_b.
          {
            clear IHlis H H0 H1 H2 H9 H7 H8. revert H11 H3. revert xs.
            induction lis; intros; try easy.
            destruct xs; try easy.
            inversion H11. subst.
            specialize(SList_f x l H3); intros. destruct H. 
            - apply SList_b. apply IHlis with (xs := l); try easy.
            - destruct H. destruct H0. subst. destruct lis; try easy.
              destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst. easy.
          } 
        - inversion H. subst. clear H.
          assert (wfL (l_recv p lis)). 
          {
            apply IHlis with (G1 := G1) (m := m) (n := n) (xs := xs); try easy.
            inversion H1. subst. inversion H12. subst. clear H12.
            constructor; try easy.
            inversion H2. subst. inversion H13. subst. clear H13.
            constructor; try easy.
          }
          inversion H. subst. constructor; try easy.
          clear H11 H8 H10 H12 H13 IHlis.
          destruct H6.
          - left. easy.
          - right. destruct H4. destruct H4. destruct H4. subst.
            destruct H9; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H6. inversion H6. subst.
            exists x1. exists x3. split; try easy.
            destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
            specialize(H5 G1 x0 m n). apply H5; try easy.
        - destruct H3. destruct H4. subst.
          destruct H9; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
          destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
          destruct lis; try easy.
          constructor; try easy. constructor; try easy. right.
          exists x. exists x2. split; try easy.
          inversion H. subst. clear H. destruct H10; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          specialize(H7 G1 x3 m n). apply H7; try easy.
  - inversion H1. subst.
    apply wfL_after_incr; try easy.
    subst.
    specialize(IHQ G1 P (S m) (S n)). 
    constructor. apply IHQ; try easy.
    inversion H0. easy.
Qed.
  
Lemma guard_break : forall x, (forall n, exists m, guardL n m (l_rec x)) -> exists T, multiS betaL (l_rec x) T /\  (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
  intros.
  pose proof H as H1.
  specialize(H1 1). destruct H1.
  assert (exists T, multiS betaL (l_rec x) T /\
  (T = l_end \/
   (exists
      (p : string) (lis : seq.seq (option (sort * local))),
      T = l_send p lis \/ T = l_recv p lis))).
  {
    clear H. revert H0. revert x. induction x0; intros; try easy.
    inversion H0. subst.
    destruct Q; try easy.
    - exists l_end.
      split. apply multi_sing. constructor; try easy.
      left. easy.
    - exists (l_send s l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists l. left. easy.
    - exists (l_recv s l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists l. right. easy.
    - specialize(IHx0 Q H4). 
      destruct IHx0. destruct H. exists x1. split; try easy.
      apply multi_step with (y := (l_rec Q)).
      constructor; try easy.
      easy.
  }
  destruct H1. destruct H1. exists x1.
  split; try easy. split; try easy.
  clear H0 H2. clear x0.
  revert H. induction H1; intros; try easy.
  - inversion H. subst.
    specialize(H0 n). destruct H0. 
    inversion H0. subst.
    - exists 0. apply gl_nil.
    - subst. exists m.
      specialize(subst_injL 0 0 (l_rec G) G y Q H3 H1); intros. subst. easy.
  - inversion H. subst.
    apply IHmultiS; try easy.
    intros. specialize(H0 n0). destruct H0.
    inversion H0. subst. exists 0. apply gl_nil.
    subst. exists m.
    specialize(subst_injL 0 0 (l_rec G) G y Q H4 H2); intros. subst. easy.
Qed.

Lemma typable_implies_wfC_helper_p2 : forall x T',
      lttTC (l_rec x) T' ->
      wfL (l_rec x) -> 
      (forall n, exists m, guardL n m (l_rec x)) ->
      exists T, lttTC T T' /\ wfL T /\ (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
      intros.
      specialize(guard_break x H1); intros.
      destruct H2. exists x0. destruct H2.
      split.
      - clear H0 H1 H3.
        revert H. revert T'. induction H2; intros; try easy.
        inversion H. subst. 
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H3); intros. subst.
        unfold lttTC. pfold. easy.
        apply mon_lttT.
      - apply IHmultiS; try easy.
        inversion H. subst.
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H4); intros. subst.
        unfold lttTC. pfold. easy.
        apply mon_lttT.
      split; try easy.
      - clear H H1 H3.
        revert H0. revert T'. induction H2; intros; try easy.
        inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H2; try easy.
      - apply IHmultiS; try easy.
         inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H3; try easy.
Qed.

Lemma typable_implies_wfC_helper_recv : forall x p STT,
      lttTC x (ltt_recv p STT) ->
      wfL x -> 
      (forall n, exists m, guardL n m x) ->
      exists T, lttTC (l_recv p T) (ltt_recv p STT) /\ wfL (l_recv p T) /\ (forall n, exists m, guardL n m (l_recv p T)).
Proof.
  induction x using local_ind_ref; intros; try easy.
  - pinversion H.
    apply mon_lttT.
  - pinversion H.
    apply mon_lttT.
  - exists lis. 
    pinversion H0. subst. 
    apply mon_lttT.
  - exists lis.
    pinversion H0. subst.
    split.
    pfold. easy. easy.
    apply mon_lttT.
  - pinversion H. subst.
    
    specialize(typable_implies_wfC_helper_p2 x (ltt_recv p STT)); intros.
    unfold lttTC in H2 at 1. 
    assert (exists T : local,
       lttTC T (ltt_recv p STT) /\
       wfL T /\
       (forall n : fin, exists m : fin, guardL n m T) /\
       (T = l_end \/
        (exists
           (p : string) (lis : seq.seq (option (sort * local))),
           T = l_send p lis \/ T = l_recv p lis))).
    {
      apply H2; try easy.
      pfold. easy.
    }
    clear H2. destruct H5. destruct H2. destruct H5. destruct H6.
    pinversion H2. subst.
    - destruct H7; try easy. destruct H7. destruct H7. destruct H7. easy.
      inversion H7. subst. exists x1. unfold lttTC. split. pfold. easy. easy.
    - subst. destruct H7; try easy. destruct H7. destruct H7. destruct H7; try easy.
    apply mon_lttT.
    apply mon_lttT.
Qed.


Lemma typable_implies_wfC_helper_recv2 : forall STT Pr p,
    SList Pr ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wfC t)) Pr STT ->
    wfC (ltt_recv p STT).
Proof.
  induction STT; intros; try easy.
  - destruct Pr; try easy.
  - destruct Pr; try easy.
    inversion H0. subst.
    unfold wfC. destruct H4.
    - destruct H1. subst. 
      specialize(IHSTT Pr p H H6).
      unfold wfC in IHSTT. destruct IHSTT. destruct H1. destruct H2.
      specialize(typable_implies_wfC_helper_recv x p STT H1 H2 H3); intros.
      destruct H4. destruct H4. destruct H5. 
      exists (l_recv p (None :: x0)).
      split.
      - pinversion H4. subst.
        unfold lttTC. pfold. constructor. constructor; try easy. left. easy.
        apply mon_lttT.
      split; try easy.
      - inversion H5. subst. constructor; try easy. constructor; try easy.
        left. easy. 
        intros. specialize(H7 n). destruct H7. inversion H7. subst. exists 0. apply gl_nil.
        subst. exists x1. constructor; try easy. constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. clear H0.
      unfold wfC in H3. destruct H3. destruct H0. destruct H1.
      specialize(SList_f (Some x) Pr H); intros. destruct H3.
      - specialize(IHSTT Pr p H3 H6). 
        unfold wfC in IHSTT. destruct IHSTT. destruct H4. destruct H5.
        specialize(typable_implies_wfC_helper_recv x3 p STT H4 H5 H7); intros.
        destruct H8. destruct H8. destruct H9.
        exists (l_recv p (Some (x0, x2) :: x4)).
        split.
        - pfold. constructor.
          pinversion H8. subst. constructor; try easy.
          right. exists x0. exists x2. exists x1. split. easy. split. easy.
          left. easy.
          apply mon_lttT.
        split.
        - constructor; try easy.
          specialize(SList_f (Some x) Pr H); intros.
          {
            clear H4 H5 H7 H H0 H1 H2 H3 H9 H10.
            destruct H11.
            apply SList_b. pinversion H8. subst. clear H8. clear p x3 x x0 x1 x2. 
            revert H6 H1 H. revert Pr x4. induction STT; intros; try easy.
            - destruct Pr; try easy.
            - destruct Pr; try easy.
              destruct x4; try easy.
              inversion H6. subst. clear H6. inversion H1. subst. clear H1.
              specialize(SList_f o Pr H); intros. destruct H0.
              - apply SList_b. apply IHSTT with (Pr := Pr); try easy.
              - destruct H0. destruct H1. subst.
                destruct STT; try easy. destruct x4; try easy.
                destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H0. subst.
                destruct H5; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H3. inversion H3. subst. easy.
                apply mon_lttT.
            - destruct H. subst. destruct STT; try easy.
              pinversion H8. subst. destruct x4; try easy.
              apply mon_lttT.
          }
        - pinversion H8. subst. constructor.
          right. exists x0. exists x2. split; try easy.
          inversion H9. subst. easy.
          apply mon_lttT.
        - clear H4 H5 H7 H H0 H1 H6 H3 H8 H9.
          clear STT x3 Pr x x1.
          intros.
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). specialize(H10 (S n)). destruct H2. destruct H10.
          exists (ssrnat.maxn x1 x). apply gl_recv.
          constructor.
          - right. exists x0. exists x2. split; try easy.
            specialize(guardL_more n x); intros. apply H1; try easy.
            specialize(ssrnat.leq_maxr x1 x); intros. easy.
          - inversion H0. subst. clear H0 H. clear p x0 x2. revert H4. revert n x x1.
            induction x4; intros; try easy.
            inversion H4. subst.
            constructor; try easy.
            destruct H1.
            - left. easy.
            - right. destruct H. destruct H. destruct H. subst. exists x0. exists x2.
              split; try easy.
              specialize(guardL_more n x1 (ssrnat.maxn x1 x) x2 H0); intros.
              apply H.
              specialize(ssrnat.leq_maxl x1 x); intros. easy.
            apply IHx4; try easy.
      - destruct H3. destruct H4. subst.
        destruct STT; try easy. inversion H4. subst.
        exists (l_recv p [Some (x0, x2)]).
        split.
        - unfold lttTC. pfold. constructor.
          constructor. right. exists x0. exists x2. exists x1.
          split. easy. split. easy.
          left. easy.
        - easy.
        split.
        - constructor. easy.
          constructor. right. exists x0. exists x2. split; try easy.
        - easy.
        - intro. 
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). destruct H2.
          exists x. apply gl_recv. constructor; try easy.
          right. exists x0. exists x2. split. easy. easy.
Qed.
  
Lemma typable_implies_wfC [P : process] [Gs : ctxS] [Gt : ctxT] [T : ltt] :
  typ_proc Gs Gt P T -> wfC T.
Proof.
  intros. induction H using typ_proc_ind_ref; try easy.
  - unfold wfC. exists l_end. split. pfold. constructor. 
    split. apply wfl_end.
    intros. exists 0. apply gl_end.
  - apply typable_implies_wfC_helper_recv2 with (Pr := Pr); try easy.
  - unfold wfC.
    inversion IHtyp_proc. 
    destruct H0. destruct H1.
    exists (l_send p (extendLis l (Some (S, x)))).
    unfold wfC in IHtyp_proc. destruct IHtyp_proc. destruct H3. destruct H4.
    split.
    - unfold lttTC. pfold. constructor.
      induction l; intros; try easy.
      simpl in *.
      - constructor; try easy.
        right. exists S. exists x. exists T. split. easy. split. easy.
        unfold lttTC in H0. left. easy.
      - simpl. constructor; try easy.
        left. easy.
    split.
    - induction l; intros; try easy.
      simpl in *.
      - constructor; try easy.
      - constructor; try easy. right. exists S. exists x. split; try easy.
      - inversion IHl. subst.
        constructor; try easy.
        constructor; try easy. left. easy.
      - intros.
        destruct n; try easy.
        - exists 0. apply gl_nil.
        - specialize(H2 n). destruct H2.
          exists x1. apply gl_send; try easy.
          induction l; intros; try easy.
          - simpl in *. constructor; try easy.
            right. exists S. exists x. split; try easy.
          - simpl. constructor; try easy. left. easy.
Qed.

Lemma _a23_a: forall p Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_recv p Q) -> 
  (exists STT, length Q = length STT /\ subtypeC (ltt_recv p STT) T /\ 
  List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) Gt p t)) Q STT /\ SList Q).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H3. destruct H4. 
       exists x.
       split; try easy. split; try easy.
       specialize(stTrans (ltt_recv p x) t t' H4 H1); intros.
       easy.
       inversion H0. subst. exists STT.
       split. easy. split. apply stRefl. easy.
Qed.
(* 
Lemma _a23_b: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S S' T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,(S',T'))]) T.
Proof. intros p l e Q P Gs Gt T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H1).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split.
       specialize(sc_sub cs e S S); intro HSS.
       apply HSS. easy. apply srefl. 
       split.
       specialize(tc_sub cs ct Q T' T'); intro HTS.
       apply HTS. easy.
       apply stRefl. split. easy.
       destruct Ha as (Ha,(Hb,(Hc,Hd))).
       specialize(stTrans (ltt_send p [(l, (S', T'))]) t t' Hd H0); intro HT.
       apply HT.
       exists S. exists S. exists T.
       inversion H1. subst.
       split. easy. split. easy.
       split. apply srefl.
       apply stRefl. 
Qed.
 *)
Lemma _a23_bf: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\  subtypeC (ltt_send p (extendLis l (Some (S,T')))) T.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H2); intros. destruct IHtyp_proc. destruct H3. destruct H3. destruct H4.
  exists x. exists x0. split; try easy. split; try easy.
  specialize(stTrans (ltt_send p (extendLis l (Some (x, x0)))) t t' H5 H0); intros; try easy.
  inversion H1. subst.
  exists S. exists T. split; try easy. split; try easy. apply stRefl. 
Qed.
(* 
Lemma _a23_bs: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> forall S T', subtypeC (ltt_send p [(l,(S,T'))]) T -> 
  typ_expr Gs e S /\ typ_proc Gs Gt Q T'.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H1); intros. 
  specialize(stTrans (ltt_send p [(l, (S, T'))]) t t' IHtyp_proc H0); intros; try easy.
  inversion H3. subst.
  exists S. exists T. split; try easy. 
Qed.
 *)
Lemma _a23_c: forall P e Q1 Q2 T Gs Gt,
  typ_proc Gs Gt P T ->
  P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc Gs Gt Q1 T1 /\ typ_proc Gs Gt Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T /\ typ_expr Gs e sbool.
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
       exists T. exists T.
       split. easy. split. easy. split. apply stRefl. split. apply stRefl. easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T1,(T2,(Ha,(Hb,(Hc,Hd))))).
       exists T1. exists T2.
       split.
       specialize(tc_sub cs ct Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. specialize(typable_implies_wfC Ha); easy.
       split. easy. split. 
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       split. destruct Hd.
       specialize(stTrans T2 t t' H3 H1); intro HT. easy.
       destruct Hd. easy.
Qed.

Lemma _a23_d: forall P Q T' Gs Gt,
  typ_proc Gs Gt P T' ->
  P = (p_rec Q)   -> exists T, (typ_proc Gs (Some T :: Gt) Q T /\ subtypeC T T').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. 
       split. easy. apply stRefl.
              
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H3.  
       exists x. 
       split. easy. 
       specialize(stTrans x t t' H4 H1); intros. easy.
Qed. 


Lemma _a23_e: forall P X T Gs Gt,
  typ_proc Gs Gt P T ->
  (P = (p_var X) -> exists T', onth X Gt = Some T' /\ subtypeC T' T /\ wfC T').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. split. easy. split. apply stRefl. easy.
       
       specialize(IHtyp_proc H0); intros. destruct IHtyp_proc.
       destruct H3.
       exists x. split. easy. split. destruct H4.
       specialize(stTrans x t t' H4 H1); intros; try easy. easy.
Qed.
       

Lemma _a23_f: forall P T Gs Gt,
  typ_proc Gs Gt P T ->
  P = p_inact -> T = ltt_end.
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc eq_refl).
       subst.
       punfold H1. inversion H1. easy.
       apply subtype_monotone; try easy.
Qed.
