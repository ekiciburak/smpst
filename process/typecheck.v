From SST Require Import aux.unscoped aux.expressions process.processes type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.


Definition ctxS := list (option sort).
Definition ctxT := list (option ltt).

Fixpoint onth {A : Type} (n : fin) (lis : list (option A)) : option A :=
  match lis with 
    | x::xs =>
      match n with
        | S m => onth m xs
        | 0   => x
      end
    | [] => None
  end.


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
                             typ_expr c (e_plus e1 e2) sint.


(*  depth *)
Inductive typ_proc: ctxS -> ctxT -> process -> ltt -> Prop :=
  | tc_inact: forall cs ct,     typ_proc cs ct (p_inact) (ltt_end)
  | tc_var  : forall cs ct s t, Some t = onth s ct ->
                                typ_proc cs ct (p_var s) t
  | tc_mu   : forall cs ct p t t',    typ_proc cs (Some t :: ct) p t' ->
                                      subtypeC t t' ->
                                      typ_proc cs ct (p_rec p) t'
  | tc_ite  : forall cs ct e p1 p2 T, typ_expr cs e sbool ->
                                      typ_proc cs ct p1 T ->
                                      typ_proc cs ct p2 T ->
                                      typ_proc cs ct (p_ite e p1 p2) T
  | tc_sub  : forall cs ct p t t',    typ_proc cs ct p t ->
                                      subtypeC t t' ->
                                      typ_proc cs ct p t'
  | tc_recv : forall cs ct p L ST P T,
                     length L = length ST ->
                     length ST = length P ->
                     length P = length T ->
                     SSortedNList L ->
                     Forall2 (fun u v => typ_proc (Some (fst v) :: cs) ct u (snd v)) P (zip ST T) ->
                     typ_proc cs ct (p_recv p L P) (ltt_recv p (zip L (zip ST T)))
  | tc_send: forall cs ct p l e P S T, typ_expr cs e S ->
                                       typ_proc cs ct P T ->
                                       typ_proc cs ct (p_send p l e P) (ltt_send p [(l,(S,T))]).

Print typ_proc_ind.

Section typ_proc_ind_ref.
  Variable P : ctxS -> ctxT -> process -> ltt -> Prop.
  Hypothesis P_inact : forall cs ct, P cs ct p_inact ltt_end.
  Hypothesis P_var   : forall cs ct s t, Some t = onth s ct -> P cs ct (p_var s) t.
  Hypothesis P_mu    : forall cs ct p t t', P cs (Some t :: ct) p t' -> subtypeC t t' -> P cs ct (p_rec p) t'.
  Hypothesis P_ite   : forall cs ct e p1 p2 T, typ_expr cs e sbool -> P cs ct p1 T -> P cs ct p2 T -> P cs ct (p_ite e p1 p2) T.
  Hypothesis P_sub   : forall cs ct p t t', P cs ct p t -> subtypeC t t' -> P cs ct p t'.
  Hypothesis P_recv  : forall cs ct p L ST Pr T, length L = length ST -> length ST = length Pr -> length Pr = length T ->
                     SSortedNList L ->
                     List.Forall2 (fun u v => P (Some (fst v) :: cs) ct u (snd v)) Pr (zip ST T) ->
                     P cs ct (p_recv p L Pr) (ltt_recv p (zip L (zip ST T))).
  Hypothesis P_send  : forall cs ct p l e Pr S T, typ_expr cs e S -> P cs ct Pr T -> P cs ct (p_send p l e Pr) (ltt_send p [(l,(S,T))]).
  
  Fixpoint typ_proc_ind_ref (cs : ctxS) (ct : ctxT) (p : process) (T : ltt) (a : typ_proc cs ct p T) {struct a} : P cs ct p T.
  Proof.
    refine (match a with
      | tc_inact s t => P_inact s t 
      | tc_var s t s1 t1 Hsl => P_var s t s1 t1 Hsl
      | tc_mu sc tc pr t t' Ht Hst => P_mu sc tc pr t t' (typ_proc_ind_ref sc (Some t :: tc) pr t' Ht) Hst
      | tc_ite sc tc ex p1 p2 t He Hp1 Hp2 => P_ite sc tc ex p1 p2 t He (typ_proc_ind_ref sc tc p1 t Hp1) (typ_proc_ind_ref sc tc p2 t Hp2)
      | tc_sub sc tc pr t t' Ht Hst => P_sub sc tc pr t t' (typ_proc_ind_ref sc tc pr t Ht) Hst
      | tc_recv sc st p L ST Pr Tr HL HST HP HsL Hm => P_recv sc st p L ST Pr Tr HL HST HP HsL _
      | tc_send sc tc p l ex Pr Sr Tr He HT => P_send sc tc p l ex Pr Sr Tr He (typ_proc_ind_ref sc tc Pr Tr HT)
    end); try easy.
    revert Hm.
    apply Forall2_mono. intros. apply (typ_proc_ind_ref (Some (fst y) :: sc) st x (snd y) H).
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








