From SST Require Import aux.unscoped aux.expressions process.processes type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.

Inductive ctx: Type :=
  | empty: ctx
  | consS: fin -> sort -> ctx -> ctx
  | consT: fin -> ltt -> ctx -> ctx.

Definition extendS (m: ctx) (s: fin) (t: expressions.sort) :=
  consS s t m.

Definition extendT (m: ctx) (s: fin) (t: ltt) :=
  consT s t m.

Fixpoint lookupS (m: ctx) (s: fin): option expressions.sort :=
  match m with
    | empty          => None
    | consS s' t' xs => if Nat.eqb s s' then Some t' else lookupS xs s
    | consT s' t' xs => lookupS xs s
  end.

Fixpoint lookupT (m: ctx) (s: fin): option ltt :=
  match m with
    | empty          => None
    | consT s' t' xs => if Nat.eqb s s' then Some t' else lookupT xs s
    | consS s' t' xs => lookupT xs s
  end.

Fixpoint infr_expr (m: ctx) (e: expr): option sort :=
  match e with
    | e_var x   => lookupS m x
    | e_val v   => 
      match v with
        | vint i  => Some sint
        | vbool b => Some sbool
        | vunit u => Some sunit
        | vnat n =>  Some snat
      end
    | e_succ e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some gint => Some sint
        | _         => None
      end
    | e_neg e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some gint => Some sint
        | _         => None
      end
    | e_not e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some goobl => Some sbool
        | _          => None
      end
    | e_gt e1 e2 => 
      let se1 := infr_expr m e1 in
      let se2 := infr_expr m e2 in
      match pair se1 se2 with
        | pair (Some sint) (Some sint) => Some sbool
        | _                            => None
      end
    | e_plus e1 e2 => 
      let se1 := infr_expr m e1 in
      let se2 := infr_expr m e2 in
      match pair se1 se2 with
        | pair (Some sint) (Some sint) => Some sint
        | _                            => None
      end
  end.

Inductive typ_expr: ctx -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = lookupS c s -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
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

Fixpoint matchSel (l: label) (xs: list(label*(expressions.sort)*ltt)%type): option ((sort)*ltt)%type :=
  match xs with
    | nil           => None
    | (lbl,s,t)::ys => if eqb l lbl then Some(s,t) else matchSel l ys
  end.

Inductive typ_proc: fin -> fin -> ctx -> process -> ltt -> Prop :=
  | tc_inact: forall m em c, typ_proc m em c (p_inact) (ltt_end)
  | tc_var  : forall m em c s t, Some t = lookupT c s ->
                                 typ_proc m em c (p_var s) t
  | tc_mu   : forall m em c p t, let c' := extendT c m t in
                                 typ_proc (S m) em c' p t ->
                                 typ_proc m em c (p_rec t p) t
  | tc_ite  : forall m em c e p1 p2 T, typ_expr c e sbool ->
                                       typ_proc m em c p1 T ->
                                       typ_proc m em c p2 T ->
                                       typ_proc m em c (p_ite e p1 p2) T
  | tc_sub  : forall m em c p t t', typ_proc m em c p t ->
                                    subtypeC t t' ->
                                    typ_proc m em c p t'
  | tc_recv : forall m em c p L ST P T,
                     List.Forall (fun u => typ_proc m (S em) (extendS c em (fst u)) (fst (snd u)) (snd (snd u))) (zip ST (zip P T)) ->
                     typ_proc m em c (p_recv p (zip (zip L ST) P)) (ltt_recv p (zip (zip L ST) T))
  | tc_send: forall m em c p l e P S T, typ_expr c e S ->
                                        typ_proc m em c P T ->
                                        typ_proc m em c (p_send p l e P) (ltt_send p [(l,S,T)]).
(*   | tc_send: forall m em c p l e P xs S T, Some(S,T) = matchSel l xs ->
                                           typ_expr c e S ->
                                           typ_proc m em c P T ->
                                           typ_proc m em c (p_send p l e P) (ltt_send p xs). *)

(* From Paco Require Import paco.

Lemma _a23_b: forall p l e S S' Q T T' G,
  typ_proc 0 0 G (p_send p l e Q) T ->
  typ_expr G e S ->
  typ_proc 0 0 G Q T' ->
  subsort S' S ->
  subtypeC (ltt_send p [(l,S',T')]) T.
Proof. intros.
       inversion H. subst.
       pfold.
       punfold H4. inversion H4. subst. admit.
       subst. admit.
       subst. 
       simpl.
       destruct T. inversion H. subst.
       inversion . easy.
       specialize(sub_out (upac subst.o2 subtype bot2)
          p [l] [S] [S] [T'] [t]
        ); intros HHa.
       simpl in HHa.
        admit.
       subst. split.
       
       split.
       inversion H. subst.
       exists S. exists S. exists T0.
       split. exact H8.
       split. exact H9.
       split. apply srefl.
       pfold.
       specialize(sub_out (upaco2 subtype bot2)
          p [l] [S] [S] [T0] [T0]
        ); intros HHa.
       simpl in HHa.
       apply HHa. easy. easy.
       apply Forall_forall. simpl.
       intros (s1, s2) Hs. destruct Hs.
       inversion H0. subst. simpl. apply srefl.
       easy.
       apply Forall_forall. simpl.
       intros (T1, T2) Hs. destruct Hs.
       inversion H0. subst.
       simpl. left. pfold.
       admit.
       simpl. easy.
Admitted.

Lemma _a23_b: forall p l e Q T G,
  typ_proc 0 0 G (p_send p l e Q) T ->
  exists S S' T',
  typ_expr G e S /\
  typ_proc 0 0 G Q T' /\
  subsort S' S /\
  subtypeC (ltt_send p [(l,S',T')]) T.
Proof. intros.
       inversion H. subst.
       exists S. exists S. exists T0.
       split. exact H8.
       split. exact H9.
       split. apply srefl.
       pfold.
       specialize(sub_out (upaco2 subtype bot2)
          p [l] [S] [S] [T0] [T0]
        ); intros HHa.
       simpl in HHa.
       apply HHa. easy. easy.
       apply Forall_forall. simpl.
       intros (s1, s2) Hs. destruct Hs.
       inversion H0. subst. simpl. apply srefl.
       easy.
       apply Forall_forall. simpl.
       intros (T1, T2) Hs. destruct Hs.
       inversion H0. subst.
       simpl. left. pfold.
       admit.
       simpl. easy.
Admitted.

Lemma _a23_c: forall e P1 P2 T1 T2 T G,
  typ_proc 0 0 G (p_ite e P1 P2) T ->
  typ_proc 0 0 G P1 T1 /\
  typ_proc 0 0 G P2 T2 /\
  subtypeC T1 T.
Proof. intros.
       inversion H.
       subst.
       split.
       
Qed.

Lemma _a23_d: forall Q T G,
  typ_proc 0 0 G (p_rec T Q) T ->
  typ_proc 1 0 (extendT G 0 T) Q T.
Proof. intros.
       inversion H. subst. easy.
Qed.
 *)






