From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.merge.
Require Import List String Coq.Arith.PeanoNat Relations.
Import ListNotations. 

Inductive isgParts : part -> global -> Prop := 
  | pa_sendp : forall p q l, isgParts p (g_send p q l)
  | pa_sendq : forall p q l, isgParts q (g_send p q l)
  | pa_mu    : forall p g,   isgParts p g -> isgParts p (g_rec g)
  | pa_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> isgParts r g -> isgParts r (g_send p q lis).

Definition isgPartsC (pt : part) (G : gtt) : Prop := 
    exists G', gttTC G' G /\ isgParts pt G'.

Inductive isgPartsG (R: part -> gtt -> Prop): part -> gtt -> Prop := 
  | g_sendp : forall p q l, isgPartsG R p (gtt_send p q l)
  | g_sendq : forall p q l, isgPartsG R q (gtt_send p q l)
  | g_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> isgPartsG R r g -> isgPartsG R r (gtt_send p q lis).

Definition isgPartsGC r G := paco2 isgPartsG bot2 r G.

Inductive ishParts : part -> gtth -> Prop := 
  | ha_sendp : forall p q l, ishParts p (gtth_send p q l)
  | ha_sendq : forall p q l, ishParts q (gtth_send p q l)
  | ha_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> ishParts r g -> ishParts r (gtth_send p q lis).

Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, 
               (isgPartsC r g -> False) -> 
               projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g l, u = Some(s, g) /\ v = Some l /\ R g r l)) xs ys ->
               isMerge t ys ->
               projection R (gtt_send p q xs) r t.

Definition projectionC g r t := paco3 projection bot3 g r t.

Lemma proj_mon: monotone3 projection.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor. easy.
       - constructor. easy. 
         revert ys H0.
         induction xs; intros.
         + subst. inversion H0. constructor.
         + subst. inversion H0. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - constructor. easy.
         revert ys H0.
         induction xs; intros.
         + subst. inversion H0. constructor.
         + subst. inversion H0. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - apply proj_cont with (ys := ys); try easy.
         revert ys H2 H3.
         induction xs; intros.
         + subst. inversion H2. constructor.
         + subst. inversion H2. constructor.
           destruct H6 as [(H6a, H6b) | (s,(g,(t2,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t2.
           split. easy. split. easy. apply LE. easy.
           subst.
           apply IHxs. easy.
           subst.
           destruct H6 as [(H6a, H6b) | (s,(g,(t2,(Ht1,(Ht2,Ht3)))))].
           subst. inversion H3. easy.
           subst.
           admit.
Admitted.

Variant gttstep (R: gtt -> gtt -> part -> part -> nat -> Prop): gtt -> gtt -> part -> part -> nat -> Prop :=
  | steq : forall p q xs s gc n,
                  p <> q ->
                  Datatypes.Some (s, gc) = onth n xs ->
                  gttstep R (gtt_send p q xs) gc p q n
  | stneq: forall p q r s xs ys n,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) xs ->
                  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g' p q n)) xs ys ->
                  gttstep R (gtt_send r s xs) (gtt_send r s ys) p q n.

Definition gttstepC g1 g2 p q n := paco5 gttstep bot5 g1 g2 p q n. 

Lemma step_mon : monotone5 gttstep.
Proof. unfold monotone5.
       intros.
       induction IN; intros.
       - apply steq with (s := s). easy. easy.
       - constructor; try easy. 
         revert ys H6.
         induction xs; intros.
         + subst. inversion H6. constructor.
         + subst. inversion H6. constructor.
           subst.
           destruct H9 as [(H9a, H9b) | (s1,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s1. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs.
           rewrite Forall_forall.
           intros u Hu.
           subst. rewrite Forall_forall in H5.
           specialize(H5 u).
           assert(In u (a :: xs)) by (simpl; right; easy).
           apply H5 in H7.
           easy.
           easy.
Qed.

Lemma gttTC_after_subst : forall G G' G1,
    multiS betaG G G' -> 
    gttTC G G1 <->
    gttTC G' G1.
Proof. split.
       intros. revert H0. revert G1. induction H; intros.
       - inversion H. subst.
         pinversion H0. subst.
         specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst.
     (*     pfold. *)
         easy.
         apply gttT_mon.
       - apply IHmultiS. inversion H. subst.
         pinversion H1. subst.
         specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst.
     (*     pfold. *)
         easy.
         apply gttT_mon.
         intros.
         revert H0. revert G1. induction H; intros.
       - inversion H. subst.
         pinversion H0. subst.
         pfold.
         apply gttT_rec with (Q := g_end). easy.
         left. pfold. easy.
         subst.
         inversion H. subst.
         pfold.
         apply gttT_rec with (Q := (g_send p q xs)). easy.
         left. pfold. easy.
         subst.
         pfold.
         apply gttT_rec with (Q := (g_rec G0)). easy.
         left. pfold. easy.
         apply gttT_mon.

         inversion H.
         subst.
         pfold.
         apply gttT_rec with (Q := y). easy.
         left.
         apply IHmultiS.
         easy.
Qed.

Lemma triv_pt_p : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC p (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.


Lemma triv_pt_q : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC q (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Definition nonVac4 (G: gtt) (r: part) (T: ltt) :=
  { _ : projectionC G r T | 
    exists p q xs ys,
      G = (gtt_send p q xs) /\
      p <> q /\
      q <> r /\
      p <> r /\
      (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g l, u = Some(s, g) /\ v = Some l /\ projectionC g r l)) xs ys) /\
      isMerge T ys
  }.

Definition nonVac1 (G: gtt) (r: part) (T: ltt) :=
{ _ : projectionC G r T | 
    G = (gtt_end) /\
    (isgPartsC r G -> False) /\
    T = ltt_end
}.

Definition nonVac2 (G: gtt) (r: part) (T: ltt) :=
  { _ : projectionC G r T | 
    exists p xs ys,
      G = (gtt_send p r xs) /\
      p <> r /\
      (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some (s,t) /\ projectionC g r t)) xs ys) /\
      T = (ltt_recv p ys)
  }.

Definition nonVac3 (G: gtt) (r: part) (T: ltt) :=
  { _ : projectionC G r T | 
    exists p xs ys,
      G = (gtt_send r p xs) /\
      p <> r /\
      (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some (s, t) /\ projectionC g r t)) xs ys) /\
      T = (ltt_send p ys)
  }.

Lemma unf_ph: forall l p q r s g,
  p <> r -> q <> r ->
  isgParts r (g_send p q (Some (s, g) :: l)) <->
  isgParts r g \/ (exists n s' g', onth n l = Some (s', g') /\ isgParts r g').
Proof. split. intros.
       inversion H1. subst. easy. subst. easy.
       subst.
       case_eq n; intros. subst. simpl in H8. inversion H8. subst.
       left. easy.
       subst. simpl in H8.
       right. exists n0. exists s0. exists g0.
       split. easy. easy.
       intros.
       destruct H1.
       specialize(pa_sendr p q r 0 s g (Some (s, g) :: l) H H0); intro HH.
       apply HH. simpl. easy. easy.
       destruct H1 as (n,(s1,(g1,(Hg1,Hg2)))).
       specialize(pa_sendr p q r (S n) s1 g1 (Some (s, g) :: l) H H0); intro HH.
       simpl in HH. apply HH; easy.
Qed.

Lemma unf_phA: forall l p q r s g,
  p <> r -> q <> r ->
  isgParts r (g_send p q (Some (s, g) :: l)) <->
  isgParts r g \/ isgParts r (g_send p q l).
Proof. split. intros.
       inversion H1. subst. easy. subst. easy.
       subst.
       case_eq n; intros. subst. simpl in H8. inversion H8. subst.
       left. easy.
       subst. simpl in H8.
       right.
       specialize(pa_sendr p q r n0 s0 g0 l H5 H7 H8 H9); intro HH. easy.
       intros.
       destruct H1.
       specialize(pa_sendr p q r 0 s g (Some (s, g) :: l) H H0); intro HH.
       apply HH. simpl. easy. easy.
       inversion H1. constructor. constructor. subst.
       specialize(pa_sendr p q r (S n) s0 g0  (Some (s, g) :: l) H5 H7); intro HH.
       simpl in HH. apply HH; easy.
Qed.

Lemma unf_ph2: forall ys p q r ,
  isgParts r (g_send p q (None :: ys)) <->
  isgParts r (g_send p q ys).
Proof. split. intros.
       inversion H. constructor. constructor.
       subst.
       case_eq n; intros. subst. simpl in H6. easy.
       subst. simpl in H6.  
       specialize(pa_sendr p q r n0 s g ys H3 H5); intro HH.
       apply HH; easy.
       intros.
       inversion H. constructor. constructor. subst.
       specialize(pa_sendr p q r (S n) s g (None::ys) H3 H5); intro HH.
       apply HH; easy.
Qed.

Lemma subst_none: forall l ys p q t m g1,
  subst_global t m g1 (g_send p q (None :: l)) (g_send p q (None :: ys)) ->
  subst_global t m g1 (g_send p q l) (g_send p q ys).
Proof. intros.
       inversion H. subst.
       inversion H4.
       subst.
       constructor. easy. 
Qed.

Lemma subst_some: forall l ys p q t m g1 g2 g3 s,
  subst_global t m g1 (g_send p q (Some (s, g2) :: l)) (g_send p q (Some (s, g3) :: ys)) ->
  subst_global t m g1 (g_send p q l) (g_send p q ys).
Proof. intros.
       inversion H. subst.
       inversion H4.
       subst.
       constructor. easy. 
Qed.

Lemma onth_in: forall {A: Type} n (l: list (option A)) a,
  onth n l = Some a ->
  In (Some a) l.
Proof. intros A n.
       induction n; intros.
       - case_eq l; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. simpl. left. easy.
       - case_eq l; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. simpl.
           right. apply IHn. easy.
Qed.

Lemma subst_preserve_part: forall G g1 g2 r t m,
  isgParts r G ->
  subst_global t m g1 G g2 ->
  isgParts r g2.
Proof. intro G.
       induction G using global_ind_ref; intros; try easy.
       - rewrite Forall_forall in H.
         inversion H1; subst; try easy.
         revert H1 H9 H H0.
         revert p q r lis.
         induction ys; intros.
         - inversion H1. subst.
           inversion H6. subst. easy.
         - inversion H9. subst.
           destruct H5 as [(H5a, H5b) | H5].
           subst.
           apply unf_ph2.
           apply IHys with (lis := l).
           apply subst_none in H1. easy.
           easy.
           intros. specialize(H x).
           assert(In x (None :: l)). simpl. right. easy.
           specialize(H H3). destruct H. left. easy.
           right. easy.
           apply -> unf_ph2 in H0. easy.
           destruct H5 as (s1,(g2,(g3,(Hg1,(Hg2,Hg3))))).
           subst.
           inversion H0. constructor. constructor.
           subst.
           pose proof H as HHH.
           specialize(H (Some(s,g))).
           assert(In (Some (s, g)) (Some (s1, g2) :: l)).
           { apply onth_in in H10. easy. }
           specialize(H H2).
           destruct H. easy.
           destruct H as (s2,(g4,(Hg4,Hg5))).
           inversion Hg4. subst.
           case_eq n; intros. subst. simpl in H10.
           inversion H10. subst.
           apply unf_phA. easy. easy.
           apply -> unf_phA in H0.
           destruct H0. left.
           apply Hg5 with (g1 := g1) (t := t) (m := m). easy. easy.
           right. 
           apply IHys with (lis := l).
           apply subst_some in H1. easy. easy.
           intros. 
           specialize(HHH x).
           assert(In x (Some (s2, g4) :: l)). simpl. right. easy.
           specialize(HHH H3).
           destruct HHH. subst. left. easy.
           right.
           destruct H4 as (s1,(g2,(Hg1,Hg2))).
           exists s1. exists g2. split. easy. easy.
           easy. easy. easy.
           subst. simpl in H10.
           specialize(pa_sendr p q r (S n0) s2 g4 (Some (s1, g3)::l) H5 H8); intro HH.
           simpl in HH.
           specialize(HH H10 H11).

           apply unf_phA. easy. easy.
           apply -> unf_phA in HH.
           destruct HH. left. easy.
           right. 
           apply IHys with (lis := l).
           apply subst_some in H1. easy. easy.
           
           intros. 
           specialize(HHH x).
           assert(In x (Some (s1, g2) :: l)). simpl. right. easy.
           specialize(HHH H4).
           destruct HHH. subst. left. easy.
           right.
           destruct H7 as (s3,(g5,(Hg1,Hg2))).
           exists s3. exists g5. split. easy. easy.
           easy. easy. easy.

           inversion H.
           subst.
           inversion H0. subst.
           constructor.
           apply IHG with (g1 := g1) (t := S t) (m := S m). easy. easy.
Qed.

Lemma multi_preserve_part: forall G g2 r,
  isgParts r G ->
  multiS betaG G g2 ->
  isgParts r g2.
Proof. intros.
       revert H. revert r. 
       induction H0; intros.
       - inversion H. subst.
         apply subst_preserve_part with (G := G) (g1 := (g_rec G)) (t := 0) (m := 0).
         inversion H0. subst. easy.
         easy.
       - inversion H. subst.
         apply IHmultiS.
         apply subst_preserve_part with (G := G) (g1 := (g_rec G)) (t := 0) (m := 0).
         inversion H1. subst. easy.
         easy.
Qed.

Derive Inversion gtt_inv with (forall G Q G', gttT G Q G') Sort Prop.

Lemma unfold_grec: forall (r: global -> gtt -> Prop) g q G,
  (forall g' q' G', multiS betaG g' q' -> r g' G' -> paco2 gttT r q' G') ->
  multiS betaG g q ->
  paco2 gttT r g G <-> paco2 gttT r q G.
Proof. split. intros.
       induction H0; intros.
       - pinversion H1. subst.
         inversion H0.
         subst. 
         inversion H0.
         subst. inversion H0. subst.
         unfold upaco2 in H3. destruct H3.
         admit.

         apply H with (g' := y). constructor. admit. admit.
         admit.
         
       - pinversion H1. subst. inversion H0.
         subst. inversion H0.
         subst.
         unfold upaco2 in H4. destruct H4.
         inversion H0. subst. apply IHmultiS. admit.
         apply IHmultiS. 
         inversion H0. subst.
         apply H with (g' := y). admit. admit.
         admit.
         
       intros.
       induction H0; intros.
       - pinversion H1. subst.
         inversion H0.
         subst. inversion H2.
         subst. 
         pfold.
         apply gttT_rec with (Q := g_end). constructor.
         left. pfold. constructor.
         subst.
         inversion H0. subst. pfold.
         apply gttT_rec with (Q := (g_send p q xs)). easy.
         left. pfold. easy.
         subst.
         unfold upaco2 in H3. destruct H3.
         inversion H0. subst.
         pfold. apply gttT_rec with (Q := (g_rec G0)). easy.
         left. pfold. easy.
         inversion H0. subst.
         pfold. apply gttT_rec with (Q := (g_rec G0)). easy.
         left. pfold. easy.
         admit.

       - pose proof IHmultiS as HH.
         specialize(HH H1).
         pinversion HH. subst.
         inversion H0. subst.
         pfold. apply gttT_rec with (Q := g_end). easy.
         left. pfold. constructor.
         
         subst. inversion H0. subst.
         pfold.
         apply gttT_rec with (Q := (g_send p q xs)). easy.
         left. pfold. easy.
         subst.

         unfold upaco2 in H4. destruct H4.
         inversion H0. subst.
         pfold. 
         apply gttT_rec with (Q := (g_rec G0)). easy.
         left. apply IHmultiS. easy.
         
         inversion H0. subst.
         pfold. apply gttT_rec with (Q := (g_rec G0)). easy.
         left. pfold. easy.
         admit.
Admitted.

(* same as gttTC_after_subst *)
Lemma unfold_grec_lift: forall g q G,
  multiS betaG g q ->
  gttTC g G <-> gttTC q G.
Proof. intros. apply unfold_grec. easy.
       easy.
Qed.

Lemma send_inv: forall Q, 
  gttT (upaco2 gttT bot2) Q gtt_end ->
  (forall p q xs, Q = g_send p q xs -> False).
Proof. intro Q.
       induction Q using global_ind_ref; intros; try easy.
Qed.

Lemma send_inv2: forall Q,
  gttT (upaco2 gttT bot2) Q gtt_end ->
  (forall p q xs, subst_global 0 0 (g_rec Q) Q (g_send p q xs) (* multiS betaG Q (g_send p q xs) *) -> False).
Proof. intro Q.
       induction Q using global_ind_ref; intros; try easy.
Qed.

Lemma subst_end_inv: forall g g' m n, 
  subst_global m n g g' g_end <->
  (g' = g_var m /\ g = g_end) \/ (g' = g_end).
Proof. split. 
       induction g using global_ind_ref; intros; try easy.
       - inversion H. subst. right. easy.
       - inversion H. subst. left. easy.
       - subst. right. easy.
       - inversion H0. subst. right. easy.
       - inversion H. subst. right. easy.
       intros. destruct H as [(Ha,Hb) | H].
       subst. constructor. subst.
       constructor. 
Qed.

Lemma subst_multi: forall g,
  closedG 0 0 g ->
  subst_global 0 0 (g_rec g) g g.
Proof. Admitted.

Lemma unroll_guarded g Q:
  closedG 0 0 g ->
  guardG 0 0 g ->
  multiS betaG g Q ->
  forall g', Q <> g_rec g'.
Admitted.

Lemma multi_preserve_part_rev: forall y G r,
  isgParts r y ->
  multiS betaG G y ->
  isgParts r G.
Proof. Admitted.

Lemma part_send_inv: forall g p q r xs,
  gttTC g (gtt_send p q xs) ->
  r = p \/ r = q ->
  isgParts r g.
Proof. induction g; intros; try easy.
       - pinversion H. apply gttT_mon.
       - pinversion H. apply gttT_mon.
       - pinversion H. subst.
         destruct H0 as [H0 | H0].
         + subst. constructor. 
         + subst. constructor.
           apply gttT_mon.
       - pinversion H. subst.
         constructor.
         apply IHg with (p := p) (q := q) (xs := xs).

         specialize(gttTC_after_subst g Q (gtt_send p q xs)); intro HH.
         apply HH. constructor. 
         admit.
         pfold. punfold H3. 
         apply gttT_mon.
         easy.
         apply gttT_mon.
Admitted.

Lemma proj_inj_p [G p T T' ctxG q Gl] :  
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) ctxG ->
  (ishParts p Gl -> False) ->
  typ_gtth ctxG Gl G ->
  projectionC G p T -> projectionC G p T' -> T = T'.
Proof.
Admitted.

Lemma proj_inj_q [G p T T' ctxG q Gl] :  
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg))
       ctxG ->
  (ishParts q Gl -> False) -> 
  typ_gtth ctxG Gl G ->
  projectionC G q T -> projectionC G q T' -> T = T'.
Admitted.


Lemma _a_29_10 : forall G p q PT S T n,
    projectionC G p PT ->
    subtypeC (ltt_send q (extendLis n (Some (S, T)))) PT ->
    exists (xs : list (option (sort * ltt))) (Sk : sort) (Tk : ltt), projectionC G p (ltt_send q xs) /\ 
    onth n xs = Some(Sk, Tk) /\ subsort S Sk /\ subtypeC T Tk.
Proof.
  intros.
  specialize(subtype_send PT q (extendLis n (Some (S, T))) H0); intros.
  destruct H1. subst.
  specialize(subtype_send_inv q (extendLis n (Some (S,T))) x H0); intros.
  exists x.
  assert (exists Sk Tk, onth n x = Some (Sk, Tk) /\ subsort S Sk /\ subtypeC T Tk).
  {
    clear H0. clear H. revert G p q S T x H1.
    induction n; intros; try easy.
    - destruct x; try easy.
      simpl in *. inversion H1. subst. destruct H3; try easy.
      destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2.
      inversion H. subst.
      exists x1. exists x3. try easy.
    - destruct x; try easy. apply IHn; try easy.
      inversion H1; try easy.
  }
  destruct H2. destruct H2. destruct H2. destruct H3.
  exists x0. exists x1. try easy.
Qed.

Lemma _a_29_11_helper : forall G p q x, 
    wfgC G -> 
    projectionC G p (ltt_send q x) -> 
    exists G' ctxJ,
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg)) ctxJ.
Proof.
  intros.
  unfold wfgC in H. destruct H as [G' H1].
  destruct H1. destruct H1. destruct H2. 
  revert H H1 H2 H3 H0. revert G p q x.
  induction G' using global_ind_ref; intros; try easy.
  
Admitted.

Lemma _a_29_11 : forall G p q x,
    wfgC G ->
    projectionC G p (ltt_send q x) ->
    exists G' ctxJ, 
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t g', u = Some(s, g') /\ v = Some(s, t) /\
          projectionC g' p t
        )) lsg x 
      )) ctxJ.
Proof.
    intros.
Admitted.

Lemma some_onth_implies_In {A} : forall n (ctxG : list (option A)) G,
    onth n ctxG = Some G -> In (Some G) ctxG.
Proof.
  induction n; intros; try easy.
  - destruct ctxG; try easy. simpl in *.
    left. easy.
  - destruct ctxG; try easy. simpl in *.
    right. apply IHn; try easy.
Qed.

Lemma _a_29_1314 : forall G G' p q QT xs ctxG x,
    Forall
        (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x))
        ctxG -> 
  typ_gtth ctxG G' G ->
  (ishParts p G' -> False) ->
  projectionC G q QT ->
  subtypeC (ltt_recv p xs) QT -> 
  exists ys, projectionC G q (ltt_recv p ys) /\ List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t'))) ys x.
Proof.
  
Admitted.


Lemma _a_29_part : forall ctxG G' G p q x ys,
    typ_gtth ctxG G' G -> 
    projectionC G p (ltt_send q x) ->
    projectionC G q (ltt_recv p ys) ->
    (ishParts p G' -> False) -> 
    (ishParts q G' -> False).
Proof.
    intros ctxG G'. revert ctxG.
    induction G' using gtth_ind_ref; intros; try easy.
    rename p into r. rename q into s. rename p0 into p. rename q0 into q.
    inversion H0. subst.
    inversion H4; try easy. 
    - subst.
      pinversion H2; try easy. subst.
      apply proj_mon.
    - subst. 
      pinversion H2; try easy. subst.
      apply H3. constructor.
      apply proj_mon.
    - subst.
      specialize(some_onth_implies_In n xs (s0, g) H13); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (x ys : seq.seq (option (sort * ltt))),
           typ_gtth ctxG g G ->
           projectionC G p (ltt_send q x) ->
           projectionC G q (ltt_recv p ys) ->
           (ishParts p g -> False) -> ishParts q g -> False))) xs); intros.
    destruct H6. specialize(H6 H). clear H H7.
    specialize(H6 (Some (s0, g)) H5).
    destruct H6; try easy.
    destruct H. destruct H. destruct H.
    inversion H. subst. clear H.
    case_eq (eqb p s); intros; try easy.
    - assert (p = s). apply eqb_eq; easy. subst. apply H3. constructor.
    case_eq (eqb p r); intros; try easy.
    - assert (p = r). apply eqb_eq; easy. subst. apply H3. constructor.
    assert (p <> s). apply eqb_neq; try easy.
    assert (p <> r). apply eqb_neq; try easy.
    assert (ishParts p x1 -> False). 
    {
      intros. apply H3.
      apply ha_sendr with (n := n) (s := x0) (g := x1); try easy.
    }
    assert (exists g', typ_gtth ctxG x1 g' /\ onth n ys0 = Some (x0, g')).
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H6 H H7 H9 H15 H16. clear p q r s.
      clear x ys.
      revert H11 H13. revert xs ctxG ys0 x0 x1.
      induction n; intros; try easy.
      - destruct xs; try easy. 
        destruct ys0; try easy.
        inversion H11. simpl in *. subst.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst.
        exists x3; try easy.
      - destruct xs; try easy.
        destruct ys0; try easy.
        apply IHn with (xs := xs) (ys0 := ys0) (x0 := x0); try easy.
        inversion H11. easy.
    }
    destruct H17. 
    specialize(H6 ctxG x2 p q).
    pinversion H2; try easy. subst.
    pinversion H1; try easy. subst. destruct H17.
    assert (exists t t', projectionC x2 p t /\ projectionC x2 q t' /\ onth n ys2 = Some t /\ onth n ys1 = Some t').
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H13 H6 H H7 H9 H15 H16 H17 H21 H22 H23 H24. clear H27 H25 H28 H32 H11.
      clear r s x1 x ys xs ctxG.
      revert H18 H26 H31. revert p q x0 x2 ys0 ys1 ys2.
      induction n; intros; try easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H26. subst. inversion H31. subst. clear H26 H31.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. inversion H0. subst.
        pclearbot. exists x4. exists x3. easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H26. subst. inversion H31. subst. clear H26 H31.
        apply IHn with (x0 := x0) (ys0 := ys0) (ys1 := ys1) (ys2 := ys2); try easy.
    }
    destruct H19. destruct H19. destruct H19. destruct H20. destruct H29.
    specialize(_a_29_part_helper_recv n ys1 x4 p ys H30 H27); intros. destruct H33. subst.
    specialize(_a_29_part_helper_send n ys2 x3 q x H29 H32); intros. destruct H33. subst.
    specialize(H6 x4 x5). apply H6; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _a_29_16 : forall G' ctxG G p q ys x, 
    projectionC G q (ltt_recv p ys) -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG ->
    (ishParts p G' -> False) ->
    (ishParts q G' -> False) -> 
    typ_gtth ctxG G' G -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x /\
              Forall2
                (fun u v => (u = None /\ v = None) \/ 
                 (exists s t g', u = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys
              )) ctxG.
Proof.
  
  
Admitted.

(* 
Lemma _a_29_helper : forall n x Sk Tk lsg p,
    onth n x = Some (Sk, Tk) ->
    Forall2 
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
    exists Glsg, onth n lsg = Some (Sk, Glsg) /\ projectionC Glsg p Tk.
Proof.
  induction n; intros; try easy.
  - destruct x; try easy.
    destruct lsg; try easy.
    simpl in *. subst.
    inversion H0. subst. destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H1. subst.
    exists x2. split; try easy.
  - destruct x; try easy. destruct lsg; try easy.
    inversion H0. subst.
    simpl in *. apply IHn with (x := x); try easy.
Qed.

Lemma _a_29_helper2 : forall lsg SI x p,
      Forall2
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
      Forall2
        (fun (u : option sort) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (t : ltt), u = Some s /\ v = Some (s, t))) SI x ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option sort) =>
         u = None /\ v = None \/
         (exists (s : sort) (g' : gtt), u = Some (s, g') /\ v = Some s)) lsg SI.
Proof.
  induction lsg; intros; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
    inversion H0. subst. clear H0. inversion H. subst. clear H.
    constructor.
    - destruct H4. left. destruct H. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
      destruct H. destruct H0. easy.
    - destruct H. destruct H. destruct H. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst. right.
      exists x2. exists x4. split; try easy.
  - apply IHlsg with (x := x) (p := p); try easy.
Qed.

Lemma _a_29_helper3 : forall n lsg x0 Sk ys q,
    onth n lsg = Some(Sk, x0) -> 
    Forall2
          (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
           u0 = None /\ v = None \/
           (exists (s : sort) (t : ltt) (g' : gtt),
              u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys ->
    exists Tq, onth n ys = Some(Sk, Tq) /\ projectionC x0 q Tq.
Proof.
  induction n; intros; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst. destruct H4; try easy. 
    destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H. subst.
    exists x1. split; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst.
    apply IHn with (lsg := lsg); try easy.
Qed.

Lemma _a_29_helper4 : forall n xs ys S' Sk T' x1,
    onth n xs = Some (S', T') ->
    onth n ys = Some (Sk, x1) ->
    Forall2R
        (fun u v : option (sort * ltt) =>
         u = None \/
         (exists (s s' : sort) (t t' : ltt),
            u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys xs -> 
    subtypeC T' x1.
Proof.
  induction n; intros.
  - destruct xs; try easy. destruct ys; try easy.
    inversion H1. subst. simpl in *. subst.
    destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2.
    inversion H0. inversion H. subst. easy.
  - destruct xs; try easy. destruct ys; try easy.
    inversion H1. subst. specialize(IHn xs ys S' Sk). apply IHn; try easy.
Qed. *)
(* 
Lemma _a_29 : forall G p q PT QT S T S' T' xs n, 
    wfgC G -> 
    projectionC G p PT -> 
    subtypeC (ltt_send q (extendLis n (Some (S, T)))) PT ->
    projectionC G q QT -> 
    onth n xs = Some (S', T') ->
    subtypeC (ltt_recv p xs) QT -> 
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ (* 1 *)
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ (* 2 *)
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ subtypeC T Tp /\ projectionC Gjk q Tq /\ subtypeC T' Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ (* 3 5 6 *)
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. (* 5 6 *)
Proof.
  intros.
  specialize(_a_29_10 G p q PT S T n H0 H1); intros.
  destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7.
  rename x0 into Sk. rename x1 into Tk.
  assert (PT = (ltt_send q x)).
  {
(*    specialize(proj_inj H0 H5); intros. *)
    admit.
  } 
  subst. clear H5. (* _a_29_10 *)
  
  specialize(_a_29_11 G p q x H H0); intros.
  destruct H5. destruct H5. destruct H5. destruct H9.
  
  rename x1 into ctxG. rename x0 into G'.
  exists G'. exists ctxG.
  assert (exists (SI : seq.seq (option sort)),
    List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t, u = Some s /\ v = Some (s, t))) SI x).
  {
    clear H H1 H0 H2 H3 H4 H8 H5 H6 H7 H9 H10. 
    clear G p q QT S' T' T xs G' ctxG S n Sk Tk.
    induction x; intros; try easy.
    - exists []. easy.
    - destruct IHx; try easy. destruct a.
      - destruct p. exists (Some s :: x0). constructor; try easy.
        right. exists s. exists l. easy.
      - exists (None :: x0). constructor; try easy.
        left. easy.
  }
  destruct H11 as [SI H11]. exists SI.
  exists Sk. split. easy.
  split. easy.
  assert (onth n SI = Some Sk /\ subsort S Sk).
  {
    clear H1 H0 H10 H3.
    revert H11 H6 H7. revert n x SI. induction n; intros; try easy.
    - destruct SI; try easy. destruct x; try easy.
      destruct x; try easy. inversion H11. subst.
      simpl in H6. subst.
      destruct H10; try easy. destruct H0. destruct H0. destruct H0. inversion H1. subst. easy.
    - destruct SI; try easy. destruct x; try easy.
      destruct x; try easy.
      inversion H11. subst. simpl.
      apply IHn with (x := x); try easy. 
  }
  specialize(_a_29_1314 G G' p q QT xs ctxG x H10 H5 H9 H2 H4); intros; try easy.
  destruct H13. destruct H13. rename x0 into ys.
  
  assert (ltt_recv p ys = QT).
  {
    admit.
(*     specialize(proj_inj H13 H2); intros. *)
  } 
 
  subst. clear H13.
  clear H7.
  
  specialize(_a_29_part ctxG G' G p q x ys H5 H0 H2 H9); intros.
  split. easy.
  assert (subsort Sk S').
  {
    clear H7 H12 H10 H9 H5 H8 H2 H0 H1 H.
    specialize(subtype_recv_inv p xs ys H4); intros. clear H4.
    revert H11 H14 H H3 H6. clear G p q S T G' ctxG.
    revert S' T' xs x ys Sk Tk SI.
    induction n; intros; try easy.
    - destruct xs; try easy.
      destruct x; try easy. 
      destruct SI; try easy. destruct ys; try easy.
      simpl in *.
      subst.
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
      inversion H. subst. clear H.
      destruct H4; try easy. destruct H. destruct H. destruct H. inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. inversion H1. subst.
      destruct H6; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H2. destruct H3. 
      inversion H. inversion H2. subst. easy.
    - destruct xs; try easy.
      destruct x; try easy.
      destruct SI; try easy. destruct ys; try easy.
      simpl in *. 
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
      inversion H. subst. clear H.
      specialize(IHn S' T' xs x ys Sk Tk SI). apply IHn; try easy.
  }
  split; try easy.
  
  specialize(subtype_recv_inv p xs ys H4); intros.
  specialize(subtype_send_inv q (extendLis n (Some (S, T))) x H1); intros.
  
  specialize(_a_29_16 G' ctxG G p q ys x H2 H10 H9 H7 H5); intros.
  
  specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys)) ctxG); intros.
  destruct H18. specialize(H18 H17). clear H17 H19 H10.
  
  apply Forall_forall; intros.
  specialize(H18 x0 H10). destruct H18. left. easy.
  destruct H17. destruct H17. destruct H17. destruct H18. destruct H19.
  right. exists (gtt_send p q x2). exists x2. subst.
  split. easy. split. easy. 
  rename x2 into lsg.
  specialize(_a_29_helper n x Sk Tk lsg p H6 H19); intros. 
  destruct H17. destruct H17.
  specialize(_a_29_helper2 lsg SI x p H19 H11); intros. 
  split; try easy. clear H21 H19.
  exists Sk. exists x0. exists Tk.
  specialize(_a_29_helper3 n lsg x0 Sk ys q H17 H20); intros.
  destruct H19. destruct H19. exists x1. split. easy.
  split. easy. split. easy. split. easy.
  specialize(_a_29_helper4 n xs ys S' Sk T' x1); intros. apply H22; try easy.
Admitted.
 *)

Lemma _a_29_s : forall G p q PT QT S T S' T' n, 
    wfgC G -> 
    projectionC G p (ltt_send q PT) -> 
    onth n PT = Some(S, T) ->
    projectionC G q (ltt_recv p QT) -> 
    onth n QT = Some (S', T') ->
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ (* 1 *)
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ (* 2 *)
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ (* 3 5 6 *)
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. (* 5 6 *)
Proof.
Admitted.


Lemma wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> wfgC G'.
Proof.
Admitted.


Lemma part_after_step : forall G G' q p pt l LP LQ,
        wfgC G ->
        gttstepC G G' q p l -> 
        projectionC G p (ltt_recv q LQ) ->
        projectionC G q (ltt_send p LP) ->
        isgPartsC pt G' -> 
        isgPartsC pt G.
Proof.
Admitted. (* probaly induction on Gl, base case ok, should be movable into everything later *)


Lemma pmergeCR: forall G r,
          wfgC G ->
          projectionC G r ltt_end ->
          (isgPartsC r G -> False).
Proof. intros.

 (*  wfgC G -> 
  isgPartsC r G -> 
  exists ctxG Gl, typ_gtth ctxG Gl G /\ ishPartsC r Gl.
  
 *)
  unfold isgPartsC in H1. destruct H1. 
  destruct H1. rename x into Gl. unfold wfgC in H. destruct H. destruct H. destruct H3. destruct H4. rename x into Gl'.
  

Admitted.






