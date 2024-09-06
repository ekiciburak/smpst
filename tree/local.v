From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From SST Require Import type.local.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.
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
  match lis with 
    | x::xs =>
      match n with
        | S m => onth m xs
        | 0   => x
      end
    | [] => Datatypes.None
  end.

Fixpoint ozip {A B: Type} (l1: list A) (l2: list B): list (option(A*B)) :=
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
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Lemma mon_wfrec: forall ys xs r r',
  wfrec subsort r ys xs ->
  (forall x0 x1 : ltt, r x0 x1 -> r' x0 x1) ->
  wfrec subsort r' ys xs.
Proof. intro ys.
       induction ys; intros.
       - case_eq xs; intros.
         + simpl. easy.
         + subst. easy.
       - case_eq xs; intros.
         + simpl. subst. easy.
         + subst. simpl in H. simpl.
           destruct a. destruct p, o. destruct p.
           split. easy. split. apply H0. easy.
           apply IHys with (r := r); easy.
           easy.
           destruct o. easy.
           apply IHys with (r := r); easy.
Qed.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfsend R1 R2 xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Lemma mon_wfsend: forall xs ys r r',
  wfsend subsort r xs ys ->
  (forall x0 x1 : ltt, r x0 x1 -> r' x0 x1) ->
  wfsend subsort r' xs ys.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + simpl. easy.
         + subst. easy.
       - case_eq ys; intros.
         + simpl. subst. easy.
         + subst. simpl in H. simpl.
           destruct a. destruct p, o. destruct p.
           split. easy. split. apply H0. easy.
           apply IHxs with (r := r); easy.
           easy.
           destruct o. easy.
           apply IHxs with (r := r); easy.
Qed.

Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p xs ys,
                    wfrec subsort R ys xs ->
                    subtype R (ltt_recv p xs) (ltt_recv p ys)
  | sub_out : forall p xs ys,
                     wfsend subsort R xs ys ->
                     subtype R (ltt_send p xs) (ltt_send p ys).

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.

Lemma st_mon: monotone2 subtype.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - constructor.
         apply mon_wfrec with (r := r); easy.
       - constructor.
         apply mon_wfsend with (r := r); easy.
Qed.

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


Lemma stTrans: forall l1 l2 l3, subtypeC l1 l2 -> subtypeC l2 l3 -> subtypeC l1 l3.
Proof. Admitted.

(* #[export]
Declare Instance stTrans: Transitive (subtypeC).
 *)
(* #[export]
Declare Instance stRefl: Reflexive (subtypeC). *)