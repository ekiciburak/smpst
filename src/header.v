From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations.
Import ListNotations. 

Notation fin := nat.

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

Fixpoint extendLis {A} (n : fin) (ST : option A) : list (option A) :=
  match n with 
    | S m  => None :: extendLis m ST
    | 0    => [ST]
  end.

Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Inductive Forall2R {X Y} (P : X -> Y -> Prop) : list X -> list Y -> Prop := 
  | Forall2R_nil : forall ys, Forall2R P nil ys
  | Forall2R_cons : forall x xs y ys, P x y -> Forall2R P xs ys -> Forall2R P (x :: xs) (y :: ys).

Inductive multiS {X : Type} (R : relation X) : relation X :=
  | multi_sing : forall (x y : X), R x y -> multiS R x y
  | multi_step : forall (x y z : X), R x y -> multiS R y z -> multiS R x z.
  
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

Lemma onthNil: forall {A: Type} n, @onth A n nil = None.
Proof. intros A n.
       induction n; intros.
       - simpl. easy.
       - simpl. easy.
Qed.
       
