From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 

Section ltt.

CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: part -> list (option(sort*ltt)) -> ltt
  | ltt_send: part -> list (option(sort*ltt)) -> ltt.

Definition ltt_id (s: ltt): ltt :=
  match s with
    | ltt_end      => ltt_end
    | ltt_recv p l => ltt_recv p l 
    | ltt_send p l => ltt_send p l
  end.
  
Lemma ltt_eq: forall s, s = ltt_id s.
Proof. intro s; destruct s; easy. Defined.

Inductive local  : Type :=
  | l_var : fin -> local 
  | l_end : local 
  | l_send : part -> list (option (sort * local)) -> local 
  | l_recv : part -> list (option (sort * local)) -> local 
  | l_rec : local -> local .
  
Section local_ind_ref.
  Variable P : local -> Prop.
  Hypothesis P_var : forall n, P (l_var n).
  Hypothesis P_end : P (l_end).
  Hypothesis P_send : forall p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (l_send p lis).
  Hypothesis P_recv : forall p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (l_recv p lis).
  Hypothesis P_rec : forall g, P g -> P (l_rec g).

  Fixpoint local_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_var.
    - apply P_end.
    - apply P_send.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s0. exists l0. split; try easy.
      left. easy.
    - apply P_recv.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s0. exists l0. split; try easy.
      left. easy.
    - apply P_rec; easy.
  Qed.
End local_ind_ref.


Fixpoint incr_freeL (fv m : fin) (T : local) := 
  match T with 
    | l_var n        => l_var (if fv <= n then (n + m) else n)
    | l_end          => l_end 
    | l_send p lis => l_send p (List.map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeL fv m g)
            | None        => None
          end) lis)
    | l_recv p lis => l_recv p (List.map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeL fv m g)
            | None        => None
          end) lis)
    | l_rec g        => l_rec (incr_freeL (S fv) m g)
  end.

Inductive subst_local : fin -> fin -> local -> local -> local -> Prop := 
  | subl_var_is   : forall G t m,                            subst_local t m G (l_var t) (incr_freeL 0 m G)
  | subl_var_notz : forall G t m, t <> 0 ->                  subst_local t m G (l_var 0) (l_var 0)
  | subl_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_local t m G (l_var (S t')) (l_var (t'))
  | subl_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_local t m G (l_var (S t')) (l_var (S t'))
  | subl_end      : forall G t m,                            subst_local t m G l_end l_end
  | subl_send     : forall G t m p xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_local t m G g g')
                                                  ) xs ys -> subst_local t m G (l_send p xs) (l_send p ys)
  | subl_recv     : forall G t m p xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_local t m G g g')
                                                  ) xs ys -> subst_local t m G (l_recv p xs) (l_recv p ys)
  | subl_rec      : forall G t m P Q, subst_local (S t) (S m) G P Q -> subst_local t m G (l_rec P) (l_rec Q). 

Inductive betaL : relation local := 
  | lttS : forall G G', subst_local 0 0 (l_rec G) G G' -> betaL (l_rec G) G'.

Inductive lttT (R : local -> ltt -> Prop) : local -> ltt -> Prop := 
  | lttT_end  : lttT R l_end ltt_end
  | lttT_send : forall p xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> lttT R (l_send p xs) (ltt_send p ys)
  | lttT_recv : forall p xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> lttT R (l_recv p xs) (ltt_recv p ys)
  | lttT_rec  : forall G Q G', subst_local 0 0 (l_rec G) G Q -> lttT R Q G' -> lttT R (l_rec G) G'.

Definition lttTC G G' := paco2 lttT bot2 G G'.

Inductive wfL : local -> Prop :=
  | wfl_var : forall n, wfL (l_var n)
  | wfl_end : wfL l_end
  | wfl_send : forall p lis, SList lis -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfL g)) lis -> wfL (l_send p lis)
  | wfl_recv : forall p lis, SList lis -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfL g)) lis -> wfL (l_recv p lis)
  | wfl_rec  : forall g, wfL g -> wfL (l_rec g).

Inductive guardL : fin -> fin -> local -> Prop := 
  | gl_nil  : forall m T, guardL 0 m T
  | gl_end  : forall n m, guardL n m l_end
  | gl_send : forall n m p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardL n m g)) lis -> guardL (S n) m (l_send p lis)
  | gl_recv : forall n m p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardL n m g)) lis -> guardL (S n) m (l_recv p lis)
  | gl_rec  : forall n m g Q, subst_local 0 0 (l_rec g) g Q -> guardL n m Q -> guardL n (S m) (l_rec g).


Lemma guardL_more : forall n m k T, guardL n m T -> m <= k -> guardL n k T.
Proof.
  induction n; intros; try easy.
  - apply gl_nil.
  - revert IHn H H0. revert n k T. induction m; intros; try easy.
    inversion H. subst. 
    - apply gl_end.
    - subst. apply gl_send; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - subst. apply gl_recv; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - destruct T.
      - inversion H.
      - apply gl_end.
      - apply gl_send.
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
        apply gl_send. easy.
      - apply gl_recv.
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
        apply gl_recv. easy.
      - inversion H. subst.
        destruct k; try easy.
        apply gl_rec with (Q := Q); try easy.
        apply IHm; try easy.
Qed.

Fixpoint wfrec (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfrec R1 R2 xs ys
    | (Datatypes.Some (s',t')::xs, Datatypes.Some (s,t)::ys) => R1 s' s /\ R2 t t' /\ wfrec R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s,t)::ys)          => wfrec R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfsend R1 R2 xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s',t')::ys)        => wfsend R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p xs ys,
                    wfrec subsort R ys xs ->
                    subtype R (ltt_recv p xs) (ltt_recv p ys)
  | sub_out : forall p xs ys,
                     wfsend subsort R xs ys ->
                     subtype R (ltt_send p xs) (ltt_send p ys).

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.


Lemma refl_recv: forall (l1:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfrec R1 R2 l1 l1.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. destruct a. destruct p.
         split. reflexivity.
         split. reflexivity.
         apply IHl1.
         easy. easy.
         apply IHl1.
         easy. easy.
Qed.

Lemma refl_send: forall (l1:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfsend R1 R2 l1 l1.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. destruct a. destruct p.
         split. reflexivity.
         split. reflexivity.
         apply IHl1.
         easy. easy.
         apply IHl1.
         easy. easy.
Qed.

Lemma stRefl: forall l, subtypeC l l.
Proof. pcofix CIH.
       intros.
       pfold.
       case_eq l; intros.
       constructor.
       constructor.
       apply refl_recv.
       constructor.

       repeat intro.
       unfold upaco2.
       right. apply CIH.

       constructor.
       apply refl_send.
       constructor.
       repeat intro.
       right. apply CIH.
Qed.


Lemma subtype_monotone : monotone2 subtype.
Proof.
  unfold monotone2.
  intros. induction IN; intros.
  - constructor.
  - constructor.
    revert H. revert ys. 
    induction xs. destruct ys; try easy.
    intros. destruct ys; try easy. simpl.
    simpl in H. destruct o; try easy. destruct p0. destruct a; try easy. destruct p0.
    destruct H. destruct H0. split; try easy. split; try easy. apply LE; try easy. apply IHxs; try easy.
    destruct a; try easy. destruct p0. apply IHxs; try easy. apply IHxs; try easy. 
  - constructor.
    revert H. revert ys.
    induction xs. destruct ys; try easy.
    intros. destruct ys; try easy. simpl in *.
    destruct a; try easy. destruct p0. destruct o; try easy. destruct p0. 
    destruct H. destruct H0. split; try easy. split. apply LE; try easy. apply IHxs; try easy.
    destruct o; try easy. destruct p0. apply IHxs; try easy. apply IHxs; try easy.
Qed.


Lemma subtype_end : forall H, subtypeC ltt_end H -> H = ltt_end.
Proof.
  intros. punfold H0. inversion H0. easy. 
  apply subtype_monotone.
Qed.

Lemma subtype_recv_inv_helper : forall pt s s0 l l0 xs ys,
    subtypeC (ltt_recv pt (Some (s, l) :: xs)) (ltt_recv pt (Some (s0, l0) :: ys)) -> 
    subtypeC l l0.
Proof.
  intros. 
  pinversion H. subst.
  simpl in H1.
  destruct H1. destruct H1.
  pclearbot.
  unfold subtypeC. easy.
  apply subtype_monotone.
Qed.

Lemma subtype_recv_inv : forall pt xs ys, subtypeC (ltt_recv pt xs) (ltt_recv pt ys) -> Forall2R (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t' t)) ys xs.
Proof.
  intros pt xs ys. revert pt xs.
  induction ys; intros. constructor.
  - destruct xs; try easy.
    pinversion H. subst. 
    simpl in H1. destruct a. destruct p. easy. easy.
    apply subtype_monotone.
  constructor.
  - destruct o. destruct a. destruct p0. destruct p. right.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split. 
    pinversion H. subst. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_recv_inv_helper pt s0 s l0 l xs ys H); intros. easy.
    left. easy.
    pinversion H. subst. 
    simpl in H1. destruct a; try easy.
    destruct p. easy.
    left. easy.
    apply subtype_monotone.
  - apply IHys with (pt := pt).
    pinversion H. subst. 
    pfold. constructor.
    simpl in H1. 
    destruct o. destruct p. destruct a. destruct p. destruct H1. destruct H1. easy. easy.
    destruct a. destruct p. easy. easy.
  - apply subtype_monotone.
Qed.

Lemma subtype_recv : forall H pt xs, subtypeC (ltt_recv pt xs) H -> (exists ys, 
                    H = ltt_recv pt ys).
Proof.
  induction xs; intros; try easy.
  - pinversion H0. subst. exists ys. easy.
    apply subtype_monotone.
  - destruct H.
    pinversion H0. apply subtype_monotone.
    pinversion H0. subst. exists l. easy. apply subtype_monotone.
    pinversion H0. apply subtype_monotone.
Qed.

Lemma subtype_send_inv_helper : forall pt s s0 l l0 xs ys,
    subtypeC (ltt_send pt (Some (s, l) :: xs)) (ltt_send pt (Some (s0, l0) :: ys)) -> 
    subtypeC l l0.
Proof.
  intros. 
  pinversion H. subst.
  simpl in H1.
  destruct H1. destruct H1.
  pclearbot.
  unfold subtypeC. easy.
  apply subtype_monotone.
Qed.

Lemma subtype_send_inv : forall pt xs ys, subtypeC (ltt_send pt xs) (ltt_send pt ys) -> Forall2R (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t t')) xs ys.
Proof.
  induction xs; intros.
  - constructor.
  - destruct ys; try easy.
    pinversion H. subst. simpl in H1. destruct a. destruct p. easy. easy.
    apply subtype_monotone.
  constructor.
  - destruct a. right. destruct p. destruct o. destruct p.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split.
    pinversion H. subst. simpl in H1. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_send_inv_helper pt s s0 l l0 xs ys H); intros. easy.
    pinversion H. subst. simpl in H1. easy.
  - apply subtype_monotone.
    left. easy.
  - apply IHxs.
    pinversion H. subst. 
    pfold. constructor.
    simpl in H1. 
    destruct o. destruct p. destruct a. destruct p. destruct H1. destruct H1. easy. easy.
    destruct a. destruct p. easy. easy.
  - apply subtype_monotone.
Qed.

Lemma subtype_send : forall H pt xs, subtypeC (ltt_send pt xs) H -> (exists ys, 
                    H = ltt_send pt ys).
Proof.
  induction xs; intros; try easy.
  - pinversion H0. subst. exists ys. easy.
    apply subtype_monotone.
  - destruct H.
    pinversion H0. apply subtype_monotone.
    pinversion H0. apply subtype_monotone.
    pinversion H0. subst. exists l. easy. apply subtype_monotone.
Qed.

Lemma stTrans_helper_recv : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2R
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) x0 x ->
      Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) x l ->
      wfrec subsort (upaco2 subtype r) x0 l.
Proof.
  induction x; intros; try easy.
  destruct x0; try easy. 
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    inversion H0.
    subst.
    split. apply sstrans with (s2 := x5); try easy.
    split. unfold upaco2. right. apply H with (l2 := x7); try easy. 
    apply IHx; try easy.
Qed. 

Lemma stTrans_helper_send : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2R
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) x x0 -> 
      Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) l x ->
      wfsend subsort (upaco2 subtype r) l x0.
Proof.
  induction x; intros; try easy.
  destruct l; try easy.
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. destruct H4. easy. destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct H0. destruct H1. easy.
    destruct o0. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4. subst. apply IHx; try easy. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    subst.
    inversion H1. subst.
    split. apply sstrans with (s2 := x6); try easy.
    split. unfold upaco2. right. apply H with (l2 := x8); try easy.
    apply IHx; try easy.
Qed. 

Lemma stTrans: forall l1 l2 l3, subtypeC l1 l2 -> subtypeC l2 l3 -> subtypeC l1 l3.
  Proof.
    pcofix CIH. intros.
    pfold. case_eq l1; intros.
    - subst. 
      specialize(subtype_end l2 H0); intros. subst.
      specialize(subtype_end l3 H1); intros. subst. apply sub_end.
    - subst.
      specialize(subtype_recv l2 s l H0); intros. destruct H. subst.
      specialize(subtype_recv l3 s x H1); intros. destruct H. subst.
      
      specialize(subtype_recv_inv s x x0 H1); intros.
      specialize(subtype_recv_inv s l x H0); intros.
      
      constructor.
      
      apply stTrans_helper_recv with (x := x); try easy.
      
    - subst.
      specialize(subtype_send l2 s l H0); intros. destruct H. subst.
      specialize(subtype_send l3 s x H1); intros. destruct H. subst.
      
      specialize(subtype_send_inv s x x0 H1); intros.
      specialize(subtype_send_inv s l x H0); intros.
      
      constructor.
      apply stTrans_helper_send with (x := x); try easy.
Qed.



End ltt.




