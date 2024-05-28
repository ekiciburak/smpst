From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From SST Require Import type.local.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.

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

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.