From SST Require Export type.global type.local type.isomorphism.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Inductive Forall3 {A B C} : (A -> B -> C -> Prop) -> list A -> list B -> list C -> Prop := 
  | Forall3_nil : forall P, Forall3 P nil nil nil
  | Forall3_cons : forall P a xa b xb c xc, P a b c -> Forall3 P xa xb xc -> Forall3 P (a :: xa) (b :: xb) (c :: xc).
 

Inductive merge2 : ltt -> ltt -> ltt -> Prop := 
  | mrg_id : forall x, merge2 x x x
  | mrg_bra : forall p xs ys IJ, Forall3 (fun u v w => 
    (u = None /\ v = None /\ w = None) \/
    (exists t, u = None /\ v = Some t /\ w = Some t) \/
    (exists t, u = Some t /\ v = None /\ w = Some t) \/
    (exists t, u = Some t /\ v = Some t /\ w = Some t)
  ) xs ys IJ ->  merge2 (ltt_recv p xs) (ltt_recv p ys) (ltt_recv p IJ).

Fixpoint isMerge (t : ltt) (lis : list (option ltt)) : Prop := SList lis /\
  match lis with 
    | Some x :: (x2 :: xs)  => exists t', isMerge t' (x2 :: xs) /\ merge2 x t' t
    | None   :: (x2 :: xs)  => isMerge t (x2 :: xs) 
    | Some x :: nil         => t = x
    | _                     => False
  end.
  

Lemma _a_29_part_helper_recv : forall n ys1 x4 p ys,
    onth n ys1 = Some x4 ->
    isMerge (ltt_recv p ys) ys1 -> 
    exists ys1', x4 = ltt_recv p ys1'.
Proof.
Admitted.

Lemma _a_29_part_helper_send : forall n ys2 x3 q x,
    onth n ys2 = Some x3 ->
    isMerge (ltt_send q x) ys2 ->
    exists ys2', x3 = ltt_send q ys2'.
Proof.
Admitted.


Lemma triv_merge : forall T T', isMerge T (Some T' :: nil) -> T = T'.
Admitted.

Lemma triv_merge2 : forall T xs, isMerge T xs -> isMerge T (None :: xs).
Admitted. 

Lemma triv_merge3 : forall T xs, isMerge T xs -> isMerge T (Some T :: xs).
Admitted.

Lemma merge_onth_recv : forall n p LQ ys1 gqT,
      isMerge (ltt_recv p LQ) ys1 ->
      onth n ys1 = Some gqT -> 
      exists LQ', gqT = ltt_recv p LQ'.
Admitted.

Lemma merge_onth_send : forall n q LP ys0 gpT,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some gpT ->
      exists LP', gpT = (ltt_send q LP').
Admitted.

Lemma merge_label_recv : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          exists T', onth l LQ' = Some T'.
Admitted.

Lemma merge_label_send : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          exists T', onth l LP' = Some T'. 
Admitted.

Lemma merge_label_sendb : forall ys0 LP LP' ST n l q,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some (ltt_send q LP') ->
      onth l LP = Some ST ->
      onth l LP' = Some ST.
Admitted.


Lemma merge_constr : forall p LQ ys1 n,
          isMerge (ltt_recv p LQ) ys1 ->
          onth n ys1 = Some ltt_end ->
          False.
Admitted.

Lemma merge_consts : forall q LP ys0 n,
          isMerge (ltt_send q LP) ys0 -> 
          onth n ys0 = Some ltt_end -> 
          False.
Admitted.

Lemma merge_slist : forall T ys, isMerge T ys -> SList ys.
Proof.
  intros T ys. revert T. induction ys; intros; try easy.
  unfold isMerge in H. destruct H. easy.
  unfold isMerge in H. destruct H. easy.
Qed.

 
