From mathcomp Require Import all_ssreflect.
From SST Require Import aux.coseq aux.expressions type.global tree.local.
From Paco Require Import paco.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.

(* global session trees *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (label*sort*gtt) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end      => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.

CoFixpoint gparts (t: gtt): coseq part :=
  match t with
    | gtt_send p q [(l,s,g')] => Delay (cocons p (Delay (cocons q (gparts g'))))
    | _                       => Delay conil
  end.

(* inductive membership check *)
Inductive coseqIn: part -> coseq part -> Prop :=
  | CoInSplit1 x xs y ys: force xs = cocons y ys -> x = y  -> coseqIn x xs
  | CoInSplit2 x xs y ys: force xs = cocons y ys -> x <> y -> coseqIn x ys -> coseqIn x xs.

Inductive gt2gtt (R: global -> gtt -> Prop): global -> gtt -> Prop :=
  | gt2gtt_end: gt2gtt R g_end gtt_end
  | gt2gtt_snd: forall p q l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                gt2gtt R (g_send p q (zip (zip l s) xs)) (gtt_send p q (zip (zip l s) ys))
  | gt2gtt_mu : forall g t,
                gt2gtt R (subst_global ((g_rec g) .: g_var) g) t ->
                gt2gtt R (g_rec g) t.

Definition gt2lttC g t := paco2 gt2gtt bot2 g t.

Fixpoint findpath (l: list (label*sort*gtt)) (lbl: label): option gtt :=
  match l with
    | []           => Datatypes.None
    | (l1,s,g)::xs => if eqb l1 lbl then Datatypes.Some g else findpath xs lbl
  end.

Inductive gttstep (R: gtt -> gtt -> part -> part -> Prop): gtt -> gtt -> part -> part -> Prop :=
  | steq : forall p q l xs gc,
(*                eqb p q = false -> *)
                  Datatypes.Some gc = findpath xs l -> gttstep R (gtt_send p q xs) gc p q
  | stneq: forall p q r s L S xs ys,
(*                eqb p q = false ->
                  eqb r s = false -> *)
                  eqb r p = false ->
                  eqb r q = false ->
                  eqb s p = false ->
                  eqb s q = false ->
                  List.Forall (fun u => coseqIn p (gparts u)) xs ->
                  List.Forall (fun u => coseqIn q (gparts u)) xs ->
                  List.Forall (fun u => R (fst u) (snd u) p q) (zip xs ys) ->
                  gttstep R (gtt_send r s (zip (zip L S) xs)) (gtt_send p q (zip (zip L S) ys)) p q.

Definition gttstepC g1 g2 p q := paco4 gttstep bot4 g1 g2 p q.

Inductive projection (R: part -> gtt -> ltt -> Prop): part -> gtt -> ltt -> Prop :=
  | proj_end: forall g r, (coseqIn r (gparts g) -> False) -> projection R r g (ltt_end)
  | proj_in : forall p r l s xs ys,
              List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
              projection R r (gtt_send p r (zip (zip l s) xs)) (ltt_recv p (zip (zip l s) ys))
  | proj_out: forall p r l s xs ys,
              List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
              projection R r (gtt_send r p (zip (zip l s) xs)) (ltt_send p (zip (zip l s) ys)).

Definition projectionC r g t := paco3 projection bot3 r g t.

(* TODO: add merging *)