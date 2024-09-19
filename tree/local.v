From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From SST Require Import type.local.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations Datatypes.
Require Import Morphisms.
Require Import Lia.

(* coinduction by Pous *)
(* From Coinduction Require Import all. Import CoindNotations.
Set Implicit Arguments. *)

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

Fixpoint onth {A : Type} (n : fin) (lis : list (option A)) : option A :=
  match n with 
    | S m => 
      match lis with 
        | x::xs => onth m xs
        | []    => None 
      end
    | 0   =>
      match lis with 
        | x::xs => x 
        | []    => None
      end
  end.


Fixpoint ozip{A B: Type} (l1: list A) (l2: list B): list (option(A*B)) :=
  match (l1,l2) with
    | ([], [])       => []
    | (x::xs, y::ys) => Datatypes.Some (x, y):: ozip xs ys
    | _              => [Datatypes.None]
  end.

Fixpoint SList {A} (lis : list (option A)) : Prop := 
  match lis with 
    | Datatypes.Some x :: [] => True 
    | _ :: xs                => SList xs
    | []                     => False
  end.

Lemma SList_f {A} : forall x (xs : list (option A)), SList (x :: xs) -> SList xs \/ (xs = nil /\ exists a, x = Datatypes.Some a).
Proof.
  intros. unfold SList in H.
  destruct x. destruct xs. right. split. easy. exists a. easy. left. easy.
  left. easy.
Qed.

Lemma SList_b {A} : forall x (xs : list (option A)), SList xs -> SList (x :: xs).
Proof.
  intros. unfold SList.
  destruct x. destruct xs; try easy. easy.
Qed.

Inductive wf (R: ltt -> Prop): ltt -> Prop :=
  | wf_end : wf R ltt_end
  | wf_recv: forall p lis,
             SList lis ->
             Forall (fun u => u = Datatypes.None \/ (exists s t, u = Datatypes.Some (s,t) /\ R t)) lis ->
             wf R (ltt_recv p lis)
  | wf_send: forall p lis,
             SList lis ->
             Forall (fun u => u = Datatypes.None \/ (exists s t, u = Datatypes.Some (s,t) /\ R t)) lis ->
             wf R (ltt_send p lis).

Definition wfC (t: ltt) := paco1 wf bot1 t.

Fixpoint wfrec (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfrec R1 R2 xs ys
    | (Datatypes.Some (s',t')::xs, Datatypes.Some (s,t)::ys) => R1 s' s /\ R2 t t' /\ wfrec R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s,t)::ys)          => wfrec R1 R2 xs ys
    | (nil, nil)                                             => True
    | _                                                      => False
  end.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfsend R1 R2 xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s',t')::ys)        => wfsend R1 R2 xs ys
    | (nil, nil)                                             => True
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

Check gpaco2.

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.

(* Lemma monoR: forall xs ys R1 R,
  (forall a a0 : ltt, R1 a a0 -> R a a0) ->
   wfrec subsort R1 ys xs ->
   wfrec subsort R ys xs.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + simpl. easy.
         + subst. simpl in H0. easy.
       - case_eq ys; intros.
         + subst. easy.
         + subst. simpl in H0.
           destruct o. destruct p, a. destruct p.
           simpl. split. easy. split. apply H. easy.
           apply IHxs with (R1 := R1).
           easy. easy.
           easy.
           simpl. 
           destruct a. easy.
           apply IHxs with (R1 := R1). easy.
           easy.
Qed.
 *)
(* Lemma monoS: forall xs ys R1 R,
  (forall a a0 : ltt, R1 a a0 -> R a a0) ->
   wfsend subsort R1 xs ys ->
   wfsend subsort R xs ys.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + simpl. easy.
         + subst. simpl in H0. easy.
       - case_eq ys; intros.
         + subst. easy.
         + subst. simpl in H0.
           destruct o. destruct p, a. destruct p.
           simpl. split. easy. split. apply H. easy.
           apply IHxs with (R1 := R1).
           easy. easy.
           easy.
           simpl. 
           destruct a. easy.
           apply IHxs with (R1 := R1). easy.
           easy.
Qed.

Definition bst: mon (ltt -> ltt -> Prop).
Proof. unshelve econstructor.
       - intros R t1 t2.
         exact (subtype R t1 t2).
       - cbv. intros R1 R2 leqR x y HR1.
         induction HR1. 
         + constructor.
         + constructor. apply monoR with (R1 := R1); easy.
         + constructor. apply monoS with (R1 := R1); easy.
Defined.
 *)
(* Program Definition b: mon (ltt -> ltt -> Prop) :=
   {| body R s t := subtype R s t |}.
 Next Obligation.
  cbv. intros R1 R CIH a b H. 
  induction H. constructor. 
  constructor.
  apply monoR with (R1 := R1).
  easy. easy.
  
  constructor.
  apply monoS with (R1 := R1).
  easy. easy.
Qed. *)

(* Print mon.
Print gfp.
Print inf'.
Print mon.
Print CompleteLattice.

Infix "⩽" := (gfp bst) (at level 70).
Notation "x ⩽[ R ] y" := (`R x y) (at level 79).
(* Notation "x ≃ y" := (`_ x y) (at level 79). *)
Notation "x [⩽] y" := (bst `_ x y) (at level 79). *)

Lemma trans_recv: forall (l1 l2 l3:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Transitive R1 -> Transitive R2 ->
   wfrec R1 R2 l1 l2 -> wfrec R1 R2 l2 l3 -> wfrec R1 R2 l1 l3.
Proof. intro l1.
       induction l1; intros.
       - simpl. destruct l2; try easy.
       - case_eq l2; case_eq l3; intros.
         + subst. simpl in *. destruct a. easy.
         + easy.
         + subst. simpl in H1. destruct a. destruct p. easy.
         + easy.
         + subst. simpl in H2. destruct o. destruct p. easy.
         + easy.
         + simpl.
           destruct a. destruct p, o.
           destruct p.
           subst.
           simpl in H1.
           destruct o0. destruct p.
           simpl in H2.
           split. 
           transitivity s1. easy. easy.
           split.
           transitivity l2. easy. easy.
           apply IHl1 with (l2 := l0).
           easy. easy. easy. easy.
           easy.
           subst. simpl in *.
           destruct o0. destruct p. easy.
           easy.
           destruct o. subst.
           simpl in *.
           destruct o0. destruct p. destruct p0.
           destruct H2. destruct H3. apply IHl1 with (l2 := l0); intros; try easy.
           destruct p. apply IHl1 with (l2 := l0); intros; try easy. 
           subst. simpl in H2. destruct o0; try easy. destruct p. easy.
           simpl in H1. apply IHl1 with (l2 := l0); intros; try easy.
Qed.

Lemma trans_send: forall (l1 l2 l3:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Transitive R1 -> Transitive R2 ->
   wfsend R1 R2 l1 l2 -> wfsend R1 R2 l2 l3 -> wfsend R1 R2 l1 l3.
Proof. intro l1.
       induction l1; intros.
       - simpl. destruct l2; try easy.  
       - case_eq l2; case_eq l3; intros.
         + subst. simpl in *. destruct a. easy.
         + easy.
         + subst. simpl in H1. destruct a. destruct p. easy.
         + easy.
         + subst. simpl in H2. destruct o. destruct p. easy.
         + easy.
         + simpl.
           destruct a. destruct p, o.
           destruct p.
           subst.
           simpl in H1.
           destruct o0. destruct p.
           simpl in H2.
           split. 
           transitivity s1. easy. easy.
           split.
           transitivity l2. easy. easy.
           apply IHl1 with (l2 := l0).
           easy. easy. easy. easy.
           easy.
           subst. simpl in *.
           destruct o0. destruct p. easy.
           easy.
           destruct o. subst.
           simpl in *.
           destruct o0. destruct p.
           destruct p0. destruct H2. destruct H3.
           apply IHl1 with (l2 := l0); try easy.
           destruct p. apply IHl1 with (l2 := l0); try easy.
           subst. destruct o0. simpl in *. destruct p. easy.
           simpl in *. apply IHl1 with (l2 := l0); try easy.
Qed.

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

Lemma stTransH: forall l1 l2 l3 R, Transitive R -> subtype R l1 l2 -> subtype R l2 l3 -> subtype R l1 l3.
Proof. intros.
       
       induction H0.
       induction H1.
       constructor.
       constructor. easy.
       constructor. easy.
       
       case_eq l3; intros.
       subst. inversion H1. subst.
       inversion H1. subst.
       constructor.
       apply trans_recv with (l2 := ys).
       repeat intro.
       apply sstrans with (s2 := y); easy.
       easy. easy. easy.
       subst. inversion H1.
       
       case_eq l3; intros.
       subst. inversion H1.
       subst.
       inversion H1. subst.
       inversion H1. subst.
       
       
       constructor.
       apply trans_send with (l2 := ys). 
       repeat intro.
       apply sstrans with (s2 := y); easy.
       easy. easy. easy.
Qed.

#[export] Instance Transitive_st {R} {HR: Transitive R}: Transitive (subtype R).
Proof. repeat intro.
       induction H0.
       induction H.
       constructor.
       constructor. easy.
       constructor. easy.

       case_eq x; intros.
       subst. inversion H.
       subst. inversion H. subst.
       constructor.
       apply trans_recv with (l2 := xs).
       repeat intro.
       apply sstrans with (s2 := y); easy.
       easy. easy. easy.
       subst. inversion H.

       case_eq x; intros.
       subst. inversion H.
       subst. inversion H. 
       subst. inversion H. subst.

       constructor.
       apply trans_send with (l2 := xs). 
       repeat intro.
       apply sstrans with (s2 := y); easy.
       easy. easy. easy.
Qed.

(* #[export] Instance Transitive_t: forall {R: Chain bst}, Transitive `R.
Proof. apply Transitive_chain.
       intros R HR.
       assert (H: forall x y z, bst `R x y -> bst `R y z -> bst `R x z).
       { intros.
         case_eq x; case_eq y; case_eq z; intros; try (subst; easy).
         subst. inversion H. subst. inversion H0. subst.
         constructor.
         apply trans_recv with (l2 := l0).
         repeat intro.
         apply sstrans with (s2 := y); easy.
         easy. easy. easy.

         subst. inversion H. subst. inversion H0. subst.
         constructor.
         apply trans_send with (l2 := l0).
         repeat intro.
         apply sstrans with (s2 := y); easy.
         easy. easy. easy.
       }
       intros x y z xy yz.
       apply H with (y := y); easy.
Qed.

Lemma stTransPous: forall t1 t2 t3, t1 ⩽ t2 -> t2 ⩽ t3 -> t1 ⩽ t3.
Proof. intros.
    (* rewrite <- H0; exact H. *)
       apply transitivity with (y := t2); easy.
Qed. *)

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

Lemma subtype_recv_inv : forall pt xs ys, subtypeC (ltt_recv pt xs) (ltt_recv pt ys) -> Forall2 (fun u v => (v = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s' s /\ subtypeC t t')) xs ys.
Proof.
  induction xs; intros.
  - destruct ys; try easy.
    pinversion H. subst. simpl in H1. destruct o; try easy. destruct p; try easy.
  - apply subtype_monotone.
  - destruct ys; try easy.
    pinversion H. subst. simpl in H1. easy.
    apply subtype_monotone.
  constructor.
  - destruct o. right. destruct a. destruct p0. destruct p.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split. 
    pinversion H. subst. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_recv_inv_helper pt s s0 l l0 xs ys H); intros. easy.
    pinversion H. subst.
    simpl in H1. destruct p. easy.
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

Lemma subtype_send_inv : forall pt xs ys, subtypeC (ltt_send pt xs) (ltt_send pt ys) -> Forall2 (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t t')) xs ys.
Proof.
  induction xs; intros.
  - destruct ys; try easy.
    pinversion H. subst. simpl in H1. easy.
  - apply subtype_monotone.
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
      Forall2
      (fun u v : option (sort * ltt) =>
       v = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s' s /\ subtypeC t t')) x x0 ->
      Forall2
       (fun u v : option (sort * ltt) =>
        v = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s' s /\ subtypeC t t')) l x ->
      wfrec subsort (upaco2 subtype r) x0 l.
Proof.
  induction x; intros; try easy.
  destruct x0; try easy. destruct l; try easy.
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    subst.
    inversion H1. subst.
    split. apply sstrans with (s2 := x6); try easy.
    split. unfold upaco2. right. apply H with (l2 := x8); try easy.
    apply IHx; try easy.
Qed.

Lemma stTrans_helper_send : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) x x0 -> 
      Forall2
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) l x ->
      wfsend subsort (upaco2 subtype r) l x0.
Proof.
  induction x; intros; try easy.
  destruct x0; try easy. destruct l; try easy.
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

(* #[export]
Declare Instance stTrans: Transitive (subtypeC).
 *)
(* #[export]
Declare Instance stRefl: Reflexive (subtypeC). *)