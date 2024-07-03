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

(* Lookup by shadowing *)
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

Inductive subCtxS : ctxS -> ctxS -> Prop := 
  | sctxs_app : forall m s s' c c', subCtxS c c' -> subsort s s' -> subCtxS (consS m s c) (consS m s' c') 
  | sctxs_appe: forall m s c c', subCtxS c c' -> subCtxS (consS m s c) (consS m s c') 
  | sctxs_ref : forall c, subCtxS c c.

Inductive subCtxT : ctxT -> ctxT -> Prop := 
  | sctxt_app : forall m t t' c c', subCtxT c c' -> subtypeC t t' -> subCtxT (consT m t c) (consT m t' c')
  | sctxt_appe: forall m t c c', subCtxT c c' -> subCtxT (consT m t c) (consT m t c') 
  | sctxt_ref : forall c, subCtxT c c.

Fixpoint refCtxS (c1 c2: ctxS) : Prop := 
  match (c1, c2) with 
    | (consS u1 v1 m1, consS u2 v2 m2) => (u1 = u2 /\ (subsort v1 v2 \/ v1 = v2) /\ refCtxS m1 m2)
    | (emptyS, emptyS) => True
    | _ => False
  end.
  
Fixpoint refCtxT (c1 c2: ctxT) : Prop := 
  match (c1, c2) with 
    | (consT u1 v1 m1, consT u2 v2 m2) => (u1 = u2 /\ (subtypeC v1 v2 \/ v1 = v2) /\ refCtxT m1 m2)
    | (emptyT, emptyT) => True
    | _ => False
  end.

(* Definition eq_ctxS (m1 m2 : ctxS) := forall n s, memS n s m1 <-> memS n s m2.
  
Definition eq_ctxT (m1 m2 : ctxT) := forall n t, memT n t m1 <-> memT n t m2.

Definition leq_ctxS (m1 m2 : ctxS) := forall n s, memS n s m1 -> memS n s m2.
  
Definition leq_ctxT (m1 m2 : ctxT) := forall n t, memT n t m1 -> memT n t m2. *)

Definition leq_sinctx_prop (n : fin) (m1 m2 : ctxS) : Prop :=
  match lookupS m1 n with
    | Some s => match lookupS m2 n with
        | Some s' => subsort s s' 
        | None => False 
       end
    | None => match lookupS m2 n with
        | Some s' => False
        | None => True
      end
  end.

Definition leq_tinctx_prop (n : fin) (m1 m2 : ctxT) : Prop := 
  match lookupT m1 n with 
    | Some t => match lookupT m2 n with
        | Some t' => subtypeC t t'
        | None => False 
       end
    | None => match lookupT m2 n with
        | Some t' => False
        | None => True 
       end
  end.

Definition eq_ctxS (m1 m2 : ctxS) := forall n, (leq_sinctx_prop n m1 m2) /\ (leq_sinctx_prop n m2 m1).
  
Definition eq_ctxT (m1 m2 : ctxT) := forall n, (leq_tinctx_prop n m1 m2) /\ (leq_tinctx_prop n m2 m1).

Definition leq_ctxS (m1 m2 : ctxS) := forall n, (leq_sinctx_prop n m1 m2).
  
Definition leq_ctxT (m1 m2 : ctxT) := forall n, (leq_tinctx_prop n m1 m2).


Inductive typ_expr: ctxS -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = lookupS c s -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c c' e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 leq_ctxS c c' ->
                                 typ_expr c' e s'
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
  | tc_inact: forall em cs ct, typ_proc em cs ct (p_inact) (ltt_end)
  | tc_var  : forall em cs ct s t, Some t = lookupT ct s ->
                                   typ_proc em cs ct (p_var s) t
  | tc_mu   : forall em cs ct x p t, let ct' := extendT ct x t in
                                     typ_proc em cs ct' p t ->
                                     typ_proc em cs ct (p_rec x p) t
  | tc_ite  : forall em cs ct e p1 p2 T, typ_expr cs e sbool ->
                                         typ_proc em cs ct p1 T ->
                                         typ_proc em cs ct p2 T ->
                                         typ_proc em cs ct (p_ite e p1 p2) T
  | tc_sub  : forall em cs cs' ct ct' p t t', typ_proc em cs ct p t ->
                                              subtypeC t t' ->
                                              leq_ctxS cs cs' ->
                                              leq_ctxT ct ct' -> 
                                              typ_proc em cs' ct' p t'
  | tc_recv : forall em cs ct p L ST P T,
                     length L = length ST ->
                     length ST = length P ->
                     length P = length T ->
                     List.Forall (fun u => typ_proc (S em) (extendS cs em (fst u)) ct (fst (snd u)) (snd (snd u))) (zip ST (zip P T)) ->
                     typ_proc em cs ct (p_recv p (zip L P)) (ltt_recv p (zip (zip L ST) T))
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

Lemma leq_ctxS_refl : forall cs, leq_ctxS cs cs.
Proof.
  intros. unfold leq_ctxS.
  intros. unfold leq_sinctx_prop.
  destruct lookupS. 
  apply (srefl s).
  easy. 
Qed.

Lemma leq_ctxT_refl : forall ct, leq_ctxT ct ct.
Proof.
  intros. unfold leq_ctxT.
  intros. unfold leq_tinctx_prop.
  destruct lookupT. easy. easy.
Qed.

Lemma leq_ctxC_trans : forall cs1 cs2 cs3, leq_ctxS cs1 cs2 -> leq_ctxS cs2 cs3 -> leq_ctxS cs1 cs3.
Proof.
  intros.
  unfold leq_ctxS in *.
  unfold leq_sinctx_prop in *.
  intro n.
  specialize(H n); intros.
  specialize(H0 n); intros.
  induction cs1; intros; try easy.
  simpl.
  simpl in H.
  induction cs2; intros; try easy.
  case_eq (Nat.eqb n n0); intros.
  specialize(natb_to_prop n n0 H1); intros. subst. simpl in H.
  replace ((n0 =? n0)%nat) with true in H. 
  contradiction.
  simpl in H.
  replace ((n =? n0)%nat) with false in H.
  specialize(IHcs2 H); intros.
  simpl in H0. 
  replace ((n =? n0)%nat) with false in H0.
  specialize(IHcs2 H0); intros. 
  easy.
  
  simpl.
  case_eq (Nat.eqb n n0); intros.
  simpl in H.
  replace ((n =? n0)%nat) with true in H.
  
  
  destruct (lookupS cs2 n) in *. 
  destruct (lookupS cs3 n) in *.
  specialize(sstrans s s0 s1 H H0); intros. 
  easy. easy.
  contradiction.
  simpl in H.
  replace ((n =? n0)%nat) with false in H.
  specialize(IHcs1 H); intros. easy.
Qed.

Lemma leq_ctxT_trans : forall ct1 ct2 ct3, leq_ctxT ct1 ct2 -> leq_ctxT ct2 ct3 -> leq_ctxT ct1 ct3.
Proof.
  intros.
  unfold leq_ctxT in *.
  unfold leq_tinctx_prop in *.
  intro n.
  specialize(H n); intros.
  specialize(H0 n); intros.
  induction ct1; intros; try easy.
  simpl.
  simpl in H.
  induction ct2; intros; try easy.
  case_eq (Nat.eqb n n0); intros.
  specialize(natb_to_prop n n0 H1); intros. subst. simpl in H.
  replace ((n0 =? n0)%nat) with true in H. 
  contradiction.
  simpl in H.
  replace ((n =? n0)%nat) with false in H.
  specialize(IHct2 H); intros.
  simpl in H0. 
  replace ((n =? n0)%nat) with false in H0.
  specialize(IHct2 H0); intros. 
  easy.
  
  simpl.
  case_eq (Nat.eqb n n0); intros.
  simpl in H.
  replace ((n =? n0)%nat) with true in H.
  
  
  destruct (lookupT ct2 n) in *. 
  destruct (lookupT ct3 n) in *.
  specialize(stTrans l l0 l1 H H0); intros. 
  easy. easy.
  contradiction.
  simpl in H.
  replace ((n =? n0)%nat) with false in H.
  specialize(IHct1 H); intros. easy.
Qed.

Lemma empty_nil: forall {A: Type} (l: list A),
  0 = length l <-> l = [].
Proof. intros A l.
       case l; intros; easy.
Qed.


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


Lemma _a21: forall P Q m em T G,
  typ_proc m em G Q T ->
  typ_proc (S m) em (extendT G m T) P T.
(*   typ_proc m em G (subst_proc Q P) T. *)
Proof. Admitted.







