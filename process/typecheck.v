From SST Require Import src.expressions process.processes type.global type.local type.isomorphism.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.


Definition ctxS := list (option sort).
Definition ctxT := list (option ltt).


Inductive typ_expr: ctxS -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = onth s c -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
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
                             typ_expr c (e_plus e1 e2) sint
  | sc_det  : forall c e1 e2 s, typ_expr c e1 s -> typ_expr c e2 s -> typ_expr c (e_det e1 e2) s.


(*  depth *)
Inductive typ_proc: ctxS -> ctxT -> process -> ltt -> Prop :=
  | tc_inact: forall cs ct,     typ_proc cs ct (p_inact) (ltt_end)
  | tc_var  : forall cs ct s t, Some t = onth s ct -> wfC t ->
                                typ_proc cs ct (p_var s) t
  | tc_mu   : forall cs ct p t,       typ_proc cs (Some t :: ct) p t ->
                                      typ_proc cs ct (p_rec p) t
  | tc_ite  : forall cs ct e p1 p2 T, typ_expr cs e sbool ->
                                      typ_proc cs ct p1 T ->
                                      typ_proc cs ct p2 T ->
                                      typ_proc cs ct (p_ite e p1 p2) T
  | tc_sub  : forall cs ct p t t',    typ_proc cs ct p t ->
                                      subtypeC t t' -> wfC t' ->
                                      typ_proc cs ct p t'
  | tc_recv : forall cs ct p STT P,
                     length P = length STT -> SList P ->
                     Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: cs) ct p t)) P STT ->
                     typ_proc cs ct (p_recv p P) (ltt_recv p STT)
  | tc_send : forall cs ct p l e P S T, typ_expr cs e S ->
                                        typ_proc cs ct P T ->
                                        typ_proc cs ct (p_send p l e P) (ltt_send p (extendLis l (Some (S,T)))).

Section typ_proc_ind_ref.
  Variable P : ctxS -> ctxT -> process -> ltt -> Prop.
  Hypothesis P_inact : forall cs ct, P cs ct p_inact ltt_end.
  Hypothesis P_var   : forall cs ct s t, Some t = onth s ct -> wfC t -> P cs ct (p_var s) t.
  Hypothesis P_mu    : forall cs ct p t, P cs (Some t :: ct) p t -> P cs ct (p_rec p) t.
  Hypothesis P_ite   : forall cs ct e p1 p2 T, typ_expr cs e sbool -> P cs ct p1 T -> P cs ct p2 T -> P cs ct (p_ite e p1 p2) T.
  Hypothesis P_sub   : forall cs ct p t t', P cs ct p t -> subtypeC t t' -> wfC t' -> P cs ct p t'.
  Hypothesis P_recv  : forall cs ct p STT Pr, length Pr = length STT -> SList Pr ->
                     Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ P (Some s :: cs) ct p t)) Pr STT ->
                     P cs ct (p_recv p Pr) (ltt_recv p STT).
  Hypothesis P_send  : forall cs ct p l e Pr S T, typ_expr cs e S -> P cs ct Pr T -> P cs ct (p_send p l e Pr) (ltt_send p (extendLis l (Some (S,T)))).
  
  Fixpoint typ_proc_ind_ref (cs : ctxS) (ct : ctxT) (p : process) (T : ltt) (a : typ_proc cs ct p T) {struct a} : P cs ct p T.
  Proof.
    refine (match a with
      | tc_inact s t => P_inact s t 
      | tc_var s t s1 t1 Hsl Hwf => P_var s t s1 t1 Hsl Hwf
      | tc_mu sc tc pr t Ht => P_mu sc tc pr t (typ_proc_ind_ref sc (Some t :: tc) pr t Ht)
      | tc_ite sc tc ex p1 p2 t He Hp1 Hp2 => P_ite sc tc ex p1 p2 t He (typ_proc_ind_ref sc tc p1 t Hp1) (typ_proc_ind_ref sc tc p2 t Hp2)
      | tc_sub sc tc pr t t' Ht Hst Hwf => P_sub sc tc pr t t' (typ_proc_ind_ref sc tc pr t Ht) Hst Hwf
      | tc_recv sc st p STT Pr HST HSl Hm => P_recv sc st p STT Pr HST HSl _
      | tc_send sc tc p l ex Pr Sr Tr He HT => P_send sc tc p l ex Pr Sr Tr He (typ_proc_ind_ref sc tc Pr Tr HT)
    end); try easy.
    revert Hm.
    apply Forall2_mono. intros.
    destruct H. left. easy. destruct H. destruct H. destruct H. right. exists x0, x1, x2.
    destruct H. destruct H0. split. easy. split. easy.
    apply typ_proc_ind_ref. easy.
  Qed.

End typ_proc_ind_ref.

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




