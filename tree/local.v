From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From SST Require Import type.local.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.
Require Import Morphisms.
Require Import Lia.

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

Definition nonE {A: Type} (l: list A): Prop :=
  match l with
    | [] => False
    | x::xs => True
  end.

Definition wfL {A: Type} (l: list A) := NoDup l /\ nonE l.

Fixpoint ozip{A B: Type} (l1: list A) (l2: list B): list (option(A*B)) :=
  match (l1,l2) with
    | ([], [])       => []
    | (x::xs, y::ys) => Datatypes.Some (x, y):: ozip xs ys
    | _              => [Datatypes.None]
  end.

Inductive wf (R: ltt -> Prop): ltt -> Prop :=
  | wf_end : wf R ltt_end
  | wf_recv: forall p s t,
             length s = length t ->
             Forall R t -> 
             wf R (ltt_recv p (ozip s t))
  | wf_send: forall p s t,
             length s = length t ->
             Forall R t ->
             wf R (ltt_send p (ozip s t)).

Fixpoint wfrec (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfrec R1 R2 xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => R1 s' s /\ R2 t t' /\ wfrec R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfsend R1 R2 xs ys
    | (Datatypes.Some (s',t')::xs, Datatypes.Some (s,t)::ys) => R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
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

Lemma trans_recv: forall (l1 l2 l3:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Transitive R1 -> Transitive R2 ->
   wfrec R1 R2 l1 l2 -> wfrec R1 R2 l2 l3 -> wfrec R1 R2 l1 l3.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
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
           destruct o0. destruct p. easy.
           easy.
           subst.
           simpl in *.
           destruct o0. destruct p. easy.
           apply IHl1 with (l2 := l0).
           easy. easy. easy. easy.
Qed.

Lemma trans_send: forall (l1 l2 l3:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Transitive R1 -> Transitive R2 ->
   wfsend R1 R2 l1 l2 -> wfsend R1 R2 l2 l3 -> wfsend R1 R2 l1 l3.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
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
           destruct o0. destruct p. easy.
           easy.
           subst.
           simpl in *.
           destruct o0. destruct p. easy.
           apply IHl1 with (l2 := l0).
           easy. easy. easy. easy.
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
Proof. Admitted.

Lemma stTrans: forall l1 l2 l3, subtypeC l1 l2 -> subtypeC l2 l3 -> subtypeC l1 l3.
Proof. Admitted.
 

(* #[export]
Declare Instance stTrans: Transitive (subtypeC).
 *)
(* #[export]
Declare Instance stRefl: Reflexive (subtypeC). *)



