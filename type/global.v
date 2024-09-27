From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header.
Require Import List String Coq.Arith.PeanoNat Relations. 
Import ListNotations. 

Notation part := string (only parsing).
Notation label := nat (only parsing).

Section gtt.

(* global session trees *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (option (sort*gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.


Inductive global  : Type :=
  | g_var : fin -> global 
  | g_end : global 
  | g_send : part -> part -> list (option (sort * global)) -> global 
  | g_rec : global -> global.
  
Section global_ind_ref.
  Variable P : global -> Prop.
  Hypothesis P_var : forall n, P (g_var n).
  Hypothesis P_end : P (g_end).
  Hypothesis P_send : forall p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (g_send p q lis).
  Hypothesis P_rec : forall g, P g -> P (g_rec g).
  
  Fixpoint global_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_var.
    - apply P_end.
    - apply P_send.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s1. exists g. split; try easy.
      left. easy.
    - apply P_rec. easy.
  Qed.
End global_ind_ref.


Fixpoint incr_freeG (fv m : fin) (G : global) := 
  match G with 
    | g_var n        => g_var (if fv <= n then (n + m) else n)
    | g_end          => g_end 
    | g_send p q lis => g_send p q (map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeG fv m g)
            | None        => None
          end) lis)
    | g_rec g        => g_rec (incr_freeG (S fv) m g)
  end.

Inductive subst_global : fin -> fin -> global -> global -> global -> Prop := 
  | subg_var_is   : forall G t m,                            subst_global t m G (g_var t) (incr_freeG 0 m G)
  | subg_var_notz : forall G t m, t <> 0 ->                  subst_global t m G (g_var 0) (g_var 0)
  | subg_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_global t m G (g_var (S t')) (g_var (t'))
  | subg_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_global t m G (g_var (S t')) (g_var (S t'))
  | subg_end      : forall G t m,                            subst_global t m G g_end g_end
  | subg_send     : forall G t m p q xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_global t m G g g')
                                                  ) xs ys -> subst_global t m G (g_send p q xs) (g_send p q ys)
  | subg_rec      : forall G t m P Q, subst_global (S t) (S m) G P Q -> subst_global t m G (g_rec P) (g_rec Q). 


Inductive betaG : relation global := 
  | lttS : forall G G', subst_global 0 0 (g_rec G) G G' -> betaG (g_rec G) G'.

Inductive gttT (R : global -> gtt -> Prop) : global -> gtt -> Prop := 
  | gttT_end  : gttT R g_end gtt_end
  | gttT_send : forall p q xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> gttT R (g_send p q xs) (gtt_send p q ys)
  | gttT_rec  : forall G Q G', subst_global 0 0 (g_rec G) G Q -> R Q G' -> gttT R (g_rec G) G'.

Definition gttTC G G' := paco2 gttT bot2 G G'.

Inductive wfG : global -> Prop := 
  | wfg_var : forall n, wfG (g_var n)
  | wfg_end : wfG g_end
  | wfg_send : forall p q lis, SList lis -> p <> q -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) lis -> wfG (g_send p q lis)
  | wfg_rec : forall g, wfG g -> wfG (g_rec g).

Inductive guardG : fin -> fin -> global -> Prop :=  
  | gg_nil : forall m G, guardG 0 m G
  | gg_end : forall n m, guardG n m g_end
  | gg_send : forall n m p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardG n m g)) lis -> guardG (S n) m (g_send p q lis)
  | gg_rec : forall n m g Q, subst_global 0 0 (g_rec g) g Q -> guardG n m Q -> guardG n (S m) (g_rec g).



Lemma guardL_more : forall n m k G, guardG n m G -> m <= k -> guardG n k G.
Proof.
  induction n; intros; try easy.
  - apply gg_nil.
  - revert IHn H H0. revert n k G. induction m; intros; try easy.
    inversion H. subst. 
    - apply gg_end.
    - subst. apply gg_send; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - destruct G.
      - inversion H.
      - apply gg_end.
      - apply gg_send.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gg_send. easy.
      - inversion H. subst.
        destruct k; try easy.
        apply gg_rec with (Q := Q); try easy.
        apply IHm; try easy.
Qed.

 
Lemma subst_injG : forall m n G G1 Q Q0, subst_global m n G G1 Q0 -> subst_global m n G G1 Q -> Q = Q0.
Proof.
  intros m n G G1. revert m n G.
  induction G1 using global_ind_ref; intros; try easy.
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
    clear H0 H1. revert H H9 H10. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H9. subst. clear H9.
    inversion H10. subst. clear H10.
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

Lemma wfG_after_incr : forall G1 m n,
     wfG G1 -> wfG (incr_freeG m n G1).
Proof.
  induction G1 using global_ind_ref; intros; try easy.
  - simpl in *.
    constructor.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H7. subst. clear H7.
      specialize(SList_f a lis H5); intros.
      destruct H.
      - assert (wfG (incr_freeG m n (g_send p q lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst.
          constructor; try easy.
        }
        destruct H2. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H6 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy. inversion H8. easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          easy.
          {
            clear IHlis H3 H0 H5 H1 H6. 
            revert H H4 H8. revert m n. clear q p.
            induction lis; intros; try easy. constructor. left. easy.
            - specialize(SList_f a lis H); intros.
              inversion H4. subst. clear H4. inversion H8. subst. clear H8.
              destruct H0. specialize(IHlis m n H0 H5 H6). inversion IHlis. subst. clear IHlis.
              constructor; try easy. clear H8. clear H7 H6 H5.
              destruct H3. subst. left. easy.
              destruct H1. destruct H1. destruct H1. subst. right.
              exists x. exists (incr_freeG m n x0). split; try easy.
              destruct H4; try easy. apply H2; try easy.
              destruct H1. destruct H1. destruct H1. inversion H1. subst. easy.
              
            - destruct H0. destruct H1. subst. constructor; try easy.
              right. destruct x. exists s. 
              destruct H3; try easy. destruct H0. destruct H0. destruct H0. inversion H0. subst.
              destruct H4; try easy. destruct H2. destruct H2. destruct H2. inversion H2. subst.
              exists (incr_freeG m n x2). split; try easy. apply H1; try easy.
          }
        - destruct H2. destruct H2. destruct H2. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H6 H7 H8 H1. clear x x0 p q.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeG m n x0).
          split; try easy.
          destruct H3; try easy. destruct H2. destruct H2. destruct H2. inversion H2. subst. 
          apply H3; try easy.
          {
            clear IHlis H3 H0 H5 H6 H7 H1 H. clear p q.
            revert H4 H8. revert m n. clear x x0. induction lis; intros; try easy. 
            inversion H4. inversion H8. subst. clear H4 H8.
            specialize(IHlis m n H2 H7). constructor; try easy. clear IHlis H2 H7.
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeG m n x0). split; try easy.
              apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
          }
        - destruct H. destruct H1. subst.
          destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          destruct H3; try easy. destruct H2. destruct H2. destruct H2. inversion H2. subst. 
          constructor; try easy. constructor; try easy.
          right. exists x. exists (incr_freeG m n x2).
          split; try easy. apply H3; try easy.
  - inversion H. subst.
    constructor; try easy. apply IHG1; try easy.
Qed.
  
Lemma wfG_after_subst : forall Q G1 G2 m n,
    wfG G1 -> wfG G2 -> subst_global m n G1 G2 Q -> wfG Q.
Proof.
  induction Q using global_ind_ref; intros; try easy.
  - apply wfg_var.
  - apply wfg_end.
  - inversion H2; try easy. 
    - subst.
      apply wfG_after_incr. easy.
    - subst. 
      inversion H1. subst. clear H1 H2.
      revert H H0 H8 H6 H7 H9.
      revert p G1 m n xs q.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H6); intros. clear H6.
        inversion H8. subst. clear H8.
        inversion H. subst. clear H. inversion H9. subst. clear H9.
        destruct H1.
        specialize(IHlis p G1 m n xs q H6 H0 H10 H H7 H8).
        inversion IHlis; subst.
        constructor; try easy. apply SList_b. easy.
        constructor; try easy.
        clear H12 H11 H8 H6 H10 H H7. 
        destruct H4. left. easy.
        destruct H. destruct H. destruct H. subst.
        destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
        inversion H2. subst. right. exists x1. exists x3. split; try easy. 
        destruct H3; try easy. destruct H. destruct H. destruct H. inversion H. subst.
        specialize(H1 G1 x0 m n). apply H1;try easy.
      - destruct H. destruct H1. subst.
        destruct lis; try easy. clear IHlis H10 H6 H8.
        destruct H3; try easy. destruct H. destruct H. destruct H. inversion H. subst.
        destruct H5; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
        inversion H2. subst.
        destruct H4; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst.
        constructor; try easy. constructor; try easy. right.
        exists x0. exists x1. specialize(H4 G1 x2 m n). split; try easy. apply H4; try easy.
  - inversion H1. subst.
    apply wfG_after_incr; try easy.
    subst.
    specialize(IHQ G1 P (S m) (S n)). 
    constructor. apply IHQ; try easy.
    inversion H0. easy.
Qed.
  
Lemma guard_breakG : forall x, (forall n, exists m, guardG n m (g_rec x)) -> exists T, multiS betaG (g_rec x) T /\  (forall n, exists m, guardG n m T) /\ (T = g_end \/ (exists p q lis, T = g_send p q lis)).
Proof.
  intros.
  pose proof H as H1.
  specialize(H1 1). destruct H1.
  assert (exists T, multiS betaG (g_rec x) T /\
  (T = g_end \/
   (exists
      (p q : string) (lis : seq.seq (option (sort * global))),
      T = g_send p q lis))).
  {
    clear H. revert H0. revert x. induction x0; intros; try easy.
    inversion H0. subst.
    destruct Q; try easy.
    - exists g_end.
      split. apply multi_sing. constructor; try easy.
      left. easy.
    - exists (g_send s s0 l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists s0. exists l. easy.
    - specialize(IHx0 Q H4). 
      destruct IHx0. destruct H. exists x1. split; try easy.
      apply multi_step with (y := (g_rec Q)).
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
    - exists 0. apply gg_nil.
    - subst. exists m.
      specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst. easy.
  - inversion H. subst.
    apply IHmultiS; try easy.
    intros. specialize(H0 n0). destruct H0.
    inversion H0. subst. exists 0. apply gg_nil.
    subst. exists m.
    specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst. easy.
Qed.


End gtt.








