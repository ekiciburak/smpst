From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From SST Require Import type.local.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.
Require Import Morphisms.

(* local session trees *)
CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: part -> list (label*sort*ltt) -> ltt
  | ltt_send: part -> list (label*sort*ltt) -> ltt.

Definition ltt_id (s: ltt): ltt :=
  match s with
    | ltt_end      => ltt_end
    | ltt_recv p l => ltt_recv p l
    | ltt_send p l => ltt_send p l
  end.

Lemma ltt_eq: forall s, s = ltt_id s.
Proof. intro s; destruct s; easy. Defined.

(* Inductive lttbisim (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | lttbisim_end : lttbisim R ltt_end ltt_end
  | lttbisim_recv: forall p l s xs ys,
                   length xs = length ys ->
                   List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                   lttbisim R (ltt_recv p (zip (zip l s) xs)) (ltt_recv p (zip (zip l s) ys)).
 *)
Inductive lt2ltt (R: local -> ltt -> Prop): local -> ltt -> Prop :=
  | lt2ltt_end: lt2ltt R l_end ltt_end
  | lt2ltt_rcv: forall p l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                lt2ltt R (l_recv p (zip (zip l s) xs)) (ltt_recv p (zip (zip l s) ys))
  | lt2ltt_snd: forall p l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                lt2ltt R (l_send p (zip (zip l s) xs)) (ltt_send p (zip (zip l s) ys))
  | lt2ltt_mu : forall l t,
                lt2ltt R (subst_local ((l_rec l) .: l_var) l) t ->
                lt2ltt R (l_rec l) t.

Definition lt2lttC l t := paco2 lt2ltt bot2 l t.

Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p l s' s xs ys,
                    length s' = length s ->
                    length xs = length ys ->
                    List.Forall (fun u => subsort (fst u) (snd u)) (zip s' s) ->
                    List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                    subtype R (ltt_recv p (zip (zip l s) xs)) (ltt_recv p (zip (zip l s') ys))
  | sub_out: forall p l s' s xs ys,
                    length s' = length s ->
                    length xs = length ys ->
                    List.Forall (fun u => subsort (fst u) (snd u)) (zip s s') ->
                    List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                    subtype R (ltt_send p (zip (zip l s) xs)) (ltt_send p (zip (zip l s') ys)).

Lemma destZip: forall {A B C: Type} (l: list (A * B * C)),
               exists L S xs, l = (zip (zip L S) xs).
Proof. induction l; intros.
       - exists nil. exists nil. exists nil. easy.
       - destruct IHl as (L,(S,(xs,Hxs))).
         destruct a as ((a1,a2),a3).
         simpl.
         exists (a1::L). exists (a2::S). exists(a3::xs).
         simpl. rewrite Hxs. easy.
Qed.

Lemma stReflH: forall R T, Reflexive R -> subtype R T T.
Proof. intros.
       case_eq T; intros.
       - constructor.
       - subst.
         specialize (destZip l); intro Hdest.
         destruct Hdest as (L,(S,(xs,Hxs))).
         subst.
         apply sub_in. easy. easy.
         apply Forall_forall.
         intros (x1,x2) Hx. simpl.
         induction S; intros.
         subst. simpl in Hx.
         unfold In in Hx. easy.
         subst. simpl in Hx.
         destruct Hx as [Hx | Hx].
         inversion Hx. apply srefl.
         apply IHS. easy.
         
         apply Forall_forall.
         intros (x1,x2) Hx. simpl.
         induction xs; intros.
         subst. simpl in Hx.
         unfold In in Hx. easy.
         subst. simpl in Hx.
         destruct Hx as [Hx | Hx].
         inversion Hx.
         reflexivity.
         apply IHxs. easy.

         specialize (destZip l); intro Hdest.
         destruct Hdest as (L,(S,(xs,Hxs))).
         subst.
         apply sub_out. easy. easy.
         apply Forall_forall.
         intros (x1,x2) Hx. simpl.
         induction S; intros.
         subst. simpl in Hx.
         unfold In in Hx. easy.
         subst. simpl in Hx.
         destruct Hx as [Hx | Hx].
         inversion Hx. apply srefl.
         apply IHS. easy.

         apply Forall_forall.
         intros (x1,x2) Hx. simpl.
         induction xs; intros.
         subst. simpl in Hx.
         unfold In in Hx. easy.
         subst. simpl in Hx.
         destruct Hx as [Hx | Hx].
         inversion Hx. reflexivity.
         apply IHxs. easy.
Qed.

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.

Lemma st_mon: monotone2 subtype.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - apply sub_in; try easy.
         apply Forall_forall. 
         intros (x0,x1) Ha.
         rewrite Forall_forall in H2.
         simpl. apply LE.
         specialize(H2 (x0,x1)). simpl in H2.
         now apply H2.
       - apply sub_out; try easy.
         apply Forall_forall. 
         intros (x0,x1) Ha.
         rewrite Forall_forall in H2.
         simpl. apply LE.
         specialize(H2 (x0,x1)). simpl in H2.
         now apply H2.
Qed.

#[export]
Declare Instance stTrans: Transitive (subtypeC).

#[export]
Declare Instance stRefl: Reflexive (subtypeC).


