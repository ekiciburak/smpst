From SST Require Import aux.unscoped aux.expressions process.processes type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Inductive ctxS : Type := 
  | emptyS : ctxS
  | consS : fin -> sort -> ctxS -> ctxS.

Inductive ctxT : Type := 
  | emptyT : ctxT 
  | consT : fin -> ltt -> ctxT -> ctxT.

(* Fixpoint memS (n: fin) (s: sort) (m: ctxS): Prop :=
  match m with
    | consS u v m1 => (n = u /\ (subsort s v \/ v = s)) \/ memS n s m1
    | _            => False
  end.

Fixpoint memT (n: fin) (t: ltt) (m: ctxT): Prop :=
  match m with
    | consT u v m1 => (n = u /\ (subtypeC t v \/ v = t)) \/ memT n t m1
    | _            => False
  end. *)

Definition extendS (m: ctxS) (s: fin) (t: expressions.sort) :=
  consS s t m.

Definition extendT (m: ctxT) (s: fin) (t: ltt) :=
  consT s t m.

Fixpoint lookupS (m: ctxS) (s: fin): option expressions.sort :=
  match m with
    | consS s' t' xs => if Nat.eqb s s' then Some t' else lookupS xs s
    | emptyS          => None
  end.

Fixpoint lookupT (m: ctxT) (s: fin): option ltt :=
  match m with
    | consT s' t' xs => if Nat.eqb s s' then Some t' else lookupT xs s
    | emptyT          => None
  end.

(* Fixpoint existsbS (n : fin) (l: ctxS) : bool :=
    match l with
      | emptyS => false
      | consS f _ l => (Nat.eqb n f) || existsbS n l
    end.

Fixpoint existsbT (n : fin) (l: ctxT) : bool :=
    match l with
      | emptyT => false
      | consT f _ l => (Nat.eqb n f) || existsbT n l
    end. *)

Fixpoint consistent_ctxS (m : ctxS) : Prop := 
  match m with 
    | emptyS => True
    | consS f _ l => (lookupS l f = None) /\ consistent_ctxS l
  end.

Fixpoint consistent_ctxT (m : ctxT) : Prop := 
  match m with 
    | emptyT => True
    | consT f _ l => (lookupT l f = None) /\ consistent_ctxT l
  end.
  
Definition eq_ctxS (m1 m2 : ctxS) := forall n, consistent_ctxS m1 /\ consistent_ctxS m2 /\ lookupS m1 n = lookupS m2 n.
Definition eq_ctxT (m1 m2 : ctxT) := forall n, consistent_ctxT m1 /\ consistent_ctxT m2 /\ lookupT m1 n = lookupT m2 n.


Inductive typ_expr: ctxS -> expr -> sort -> Prop :=
  | sc_var : forall c s t, consistent_ctxS c -> Some t = lookupS c s -> typ_expr c (e_var s) t
  | sc_vali: forall c i, consistent_ctxS c -> typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, consistent_ctxS c -> typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, consistent_ctxS c -> typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, consistent_ctxS c -> typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 typ_expr c e s'
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint.

Fixpoint matchSel (l: label) (xs: list(label*(expressions.sort)*ltt)%type): option ((sort)*ltt)%type :=
  match xs with
    | nil           => None
    | (lbl,s,t)::ys => if Nat.eqb l lbl then Some(s,t) else matchSel l ys
  end.

(* Require Import Coq.Init.Logic. *)

(* Definition sub_ctx (m1 m2: ctx) :=
  ((forall n s s', subsort s s'  -> (memS n s m1 <-> memS n s' m2)) \/ eq_ctx m1 m2) /\
  ((forall n t t', subtypeC t t' -> (memT n t m1 <-> memT n t' m2)) \/ eq_ctx m1 m2). *)

Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Fixpoint findCtxT (n: fin) (t: ltt) (m: ctxT): Prop :=
  match m with
    | consT u v m1 => (n = u /\ v = t) \/ findCtxT n t m1
    | _            => False
  end.

Inductive typ_proc: fin -> ctxS -> ctxT -> process -> ltt -> Prop :=
  | tc_inact: forall em cs ct, consistent_ctxS cs -> consistent_ctxT ct -> typ_proc em cs ct (p_inact) (ltt_end)
  | tc_var  : forall em cs ct s t, consistent_ctxS cs -> consistent_ctxT ct -> Some t = lookupT ct s ->
                                   typ_proc em cs ct (p_var s) t
  | tc_mu   : forall em cs ct x p t, let ct' := extendT ct x t in
                                     typ_proc em cs ct' p t ->
                                     typ_proc em cs ct (p_rec x p) t
  | tc_ite  : forall em cs ct e p1 p2 T, typ_expr cs e sbool ->
                                         typ_proc em cs ct p1 T ->
                                         typ_proc em cs ct p2 T ->
                                         typ_proc em cs ct (p_ite e p1 p2) T
  | tc_sub  : forall em cs ct p t t', typ_proc em cs ct p t ->
                                              subtypeC t t' ->
                                              typ_proc em cs ct p t'
  | tc_recv : forall em cs ct p lb st pr ty L ST P T,
                     length L = length ST ->
                     length ST = length P ->
                     length P = length T ->
                     typ_proc (S em) (extendS cs em st) ct pr ty ->
                     List.Forall (fun u => typ_proc (S em) (extendS cs em (fst u)) ct (fst (snd u)) (snd (snd u))) (zip ST (zip P T)) ->
                     typ_proc em cs ct (p_recv p (zip (lb::L) (pr::P))) (ltt_recv p (zip (zip (lb::L) (st::ST)) (ty::T)))
  | tc_send: forall em cs ct p l e P S T, typ_expr cs e S ->
                                          typ_proc em cs ct P T ->
                                          typ_proc em cs ct (p_send p l e P) (ltt_send p [(l,S,T)]).

Lemma natb_to_prop : forall a b, (a =? b)%nat = true -> a = b.
Proof. 
    intros a b.
    specialize(Nat.eqb_eq a b); intro H1.
    destruct H1.
    easy.
Qed.

Lemma natb_to_propf : forall a b, (a =? b)%nat = false -> a <> b.
Proof.
    intros a b.
    specialize(Nat.eqb_neq a b); intro H1.
    destruct H1.
    easy.
Qed.
(* 
Lemma ref_stronger_C : forall cs cs', refCtxS cs cs' -> leq_ctxS cs cs'. 
  intros cs cs'.
  induction 
  destruct cs, cs'. easy. easy. easy.
  induction cs. 
  induction cs'. 
  easy. easy.
  intros.
  
  
  induction cs'.
  
    
  induction cs'.
  easy.
  intros.
  simpl in H.
  simpl in IHcs, IHcs'.
  
  
  unfold refCtxS in *.  
  


Admitted.

Lemma ref_stronger_T : forall ct ct', refCtxT ct ct' -> leq_ctxT ct ct'. 
Admitted. *)



(* 
Lemma ref_ctx_1: forall c c' t t' u,
 refCtxT t t' c c' -> refCtxT u u c c'.
Proof. intro c.
       induction c; intros.
       - case_eq c'; intros.
         + easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - case_eq c'; intros.
         + subst. simpl in H. simpl. easy.
         + subst. simpl. simpl in H.
           destruct H as (Ha, (Hb, Hc)).
           subst. split. easy. split. easy.
           apply IHc with (t := t) (t' := t'). easy.
         + subst. simpl in H. easy.
       - case_eq c'; intros.
         + subst. simpl in H. simpl. easy.
         + subst. simpl in H. easy.
         + subst. simpl. simpl in H.
           destruct H as (Ha, Hb).
           destruct Ha as [Ha | Ha].
           destruct Ha as (Ha,(Hc,Hd)).
           subst.
           
           subst. split. easy. split. easy.
           apply IHc with (t := t) (t' := t'). easy. 
(*  *)
Example complex_mu : process := 
  p_rec (p_recv "Alice" [
    (0, sbool, p_var 0);
    (1, sbool, p_rec (p_recv "Bob" [
       (3, sbool, p_var 0);
       (4, sbool, p_var 1);
       (5, sbool, p_inact)
    ]));
    (2, sbool, p_inact)
  ]).

Compute unfold_rec complex_mu. 
 *)








