Require Import Setoid Program.
From Paco Require Import paco.
Require Import List.
Import ListNotations Datatypes.

CoInductive box : Type :=   
  | box_end : box
  | cons : list (option box) -> box.

Fixpoint wrel (R : box -> box -> Prop) (xs ys : list (option box)) : Prop := 
  match (xs, ys) with 
    | (Some x :: l1, Some y :: l2) => R x y /\ wrel R l1 l2
    | (None :: l1, None :: l2)     => wrel R l1 l2
    | (_, _) => False
  end.

Inductive rel (R : box -> box -> Prop) : box -> box -> Prop := 
  | rel_end : rel R box_end box_end
  | rel_con : forall xs ys, 
              wrel R xs ys -> rel R (cons xs) (cons ys).

Definition relC l1 l2 := paco2 rel bot2 l1 l2.

Lemma relC_inv : forall x xs y ys, relC (cons (Some x :: xs)) (cons (Some y :: ys)) -> relC x y.
Proof.
  pcofix CIH.
  intros.
  pinversion H0. subst. simpl in H2. destruct H2.
Admitted.



