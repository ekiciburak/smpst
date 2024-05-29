From SST Require Import aux.unscoped aux.expressions process.processes type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Inductive ctx: Type :=
  | empty: ctx
  | consS: fin -> sort -> ctx -> ctx
  | consT: fin -> ltt -> ctx -> ctx.

Fixpoint memS (n: fin) (s: sort) (m: ctx): Prop :=
  match m with
    | consS u v m1 => (n = u /\ v = s) \/ memS n s m1
    | consT u v m1 => memS n s m1
    | _            => False
  end.

Fixpoint memT (n: fin) (t: ltt) (m: ctx): Prop :=
  match m with
    | consT u v m1 => (n = u /\ v = t) \/ memT n t m1
    | consS u v m1 => memT n t m1
    | _            => False
  end.

Definition eq_ctx (m1 m2: ctx) := 
  (forall n s, memS n s m1 <-> memS n s m2) /\
  (forall n t, memT n t m1 <-> memT n t m2).

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


Lemma _a23_b: forall m em p l e Q P G T, 
  typ_proc m em G P T ->
  (P = (p_send p l e Q) -> exists S S' T', typ_expr G e S /\ typ_proc m em G Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,S',T')]) T).
Proof. intros m em p l e Q P G T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H1).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split. easy. split. easy. split. easy.
       destruct Ha as (Ha,(Hb,(Hc,Hd))).
       specialize(stTrans (ltt_send p [(l, S', T')]) t t' Hd H0); intro HT.
       apply HT.
       exists S. exists S. exists T.
       inversion H1. subst.
       split. easy. split. easy.
       split. apply srefl. 
       specialize(sub_out (upaco2 subtype bot2)
          p [l] [S] [S] [T] [T]
        ); intros HHa.
       simpl in HHa.
       pfold.
       apply HHa. easy. easy.
       apply Forall_forall. simpl.
       intros (s1, s2) Hs. destruct Hs.
       inversion H2. subst. simpl. apply srefl.
       easy.
       apply Forall_forall. simpl.
       intros (T1, T2) Hs. destruct Hs.
       inversion H2. subst.
       simpl. left. pfold.
       specialize(stRefl T2); intro HT.
       punfold HT. apply st_mon.
       easy.
Qed.

Lemma _a23_c: forall P m em e Q1 Q2 T G,
  typ_proc m em G P T ->
  (P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc m em G Q1 T1 /\ typ_proc m em G Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
       exists T. exists T.
       split. easy. split. easy. split.
       specialize(stRefl T); intro HT. easy.
       specialize(stRefl T); intro HT. easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T1,(T2,(Ha,(Hb,(Hc,Hd))))).
       exists T1. exists T2.
       split. easy. split. easy.
       split.
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       specialize(stTrans T2 t t' Hd H1); intro HT. easy.
Qed.

Lemma _a23_d: forall P m em Q T T' G,
  typ_proc m em G P T ->
  (P = (p_rec T' Q) /\ subtypeC T T' -> typ_proc (S m) em (extendT G m T') Q T').
Proof. intros.
       induction H; intros; try easy.
       destruct H0 as (Ha, Hb).
       inversion Ha. subst. 
       unfold c' in *.
       easy.

       destruct H0 as (Ha, Hb).
       specialize(stTrans t t' T' H1 Hb); intro HT.
       apply IHtyp_proc.
       split; easy.
Qed.

Lemma _a23_d_v2: forall P m em Q T G,
  typ_proc m em G P T ->
  (exists T', (P = (p_rec T' Q) /\ subtypeC T T') -> typ_proc (S m) em (extendT G m T') Q T').
Proof. intros.
       induction H; try (exists ltt_end; easy).
       exists t.
       intros (Ha, Hb). 
       inversion Ha. subst. 
       unfold c' in *.
       easy.

       destruct IHtyp_proc as (T', Hp).
       exists T'.
       intros (Ha, Hb).
       apply Hp.
       split. easy.
       specialize(stTrans t t' T' H0 Hb); intro HT.
       exact HT.
Qed.

Lemma _a23_e: forall P (n: fin) m em n T G,
  typ_proc m em G P T ->
  (P = (p_var n) -> exists T' G', eq_ctx G (extendT G' n T') /\ subtypeC T' T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       induction c; intros.
       simpl in H. easy.
       simpl in H.
       specialize(IHc H).
       destruct IHc as (T',(G',(Ha,Hb))).
       exists  T'. exists (consS n1 s G').

       split.
       unfold eq_ctx in *.
       split.
       intros. simpl.
       destruct Ha as (Ha1,Ha2).
       split. intro HH.
       inversion HH.
       destruct H1 as( H1a, H1b).
       subst. unfold extendT. simpl.
       left. split. easy. easy.
       simpl. right.
       apply Ha1. easy.
       intro HH.
       simpl in HH.
       destruct HH as [HH | HH].
       simpl. left. easy.
       simpl. right.
       apply Ha1. easy.
       
       intros.
       destruct Ha as (Ha1,Ha2).
       split. intro HH.
       simpl in HH. simpl.
       apply Ha2 in HH.
       unfold extendT in HH. simpl in HH. easy.
       intro HH.
       simpl. simpl in HH.
       apply Ha2. simpl. easy.
       easy.

       simpl in H.
       case_eq((Nat.eqb n0 n1)); intro Heq.
       rewrite Heq in H. inversion H. subst.
       exists l. exists c. split. unfold extendT.
       apply Nat.eqb_eq in Heq. subst. easy.
       specialize(stRefl l); intro HT. easy.
       rewrite Heq in H.
       specialize(IHc H).
       destruct IHc as (T',(G',(Ha,Hb))).
       exists T'. exists (consT n1 l G').
       split.

       unfold eq_ctx, extendT in *.
       split.
       intros. simpl.
       destruct Ha as (Ha1,Ha2).
       split. intro HH.
       apply Ha1. easy.
       intro HH. apply Ha1. simpl. easy.
       
       destruct Ha as (Ha1,Ha2).
       split. intro HH.
       simpl. simpl in HH.
       destruct HH as [HH |HH]. 
       right. left. easy.
       apply Ha2 in HH.
       simpl in HH.
       destruct HH as [HH |HH].
       left. easy.
       right. right. easy.
       
       intro HH.
       simpl. simpl in HH.
       destruct HH as [HH |HH].
       right. apply Ha2. simpl. left. easy.
       destruct HH as [HH |HH].
       left. easy.
       right.
       apply Ha2. simpl. right. easy.
       easy.

       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T',(G',(Ha,Hb))).
       exists T'. exists G'.
       split.
       easy. 
       specialize(stTrans T' t t' Hb H1); intro HT. easy.
Qed.

Lemma _a23_f: forall P m em T G,
  typ_proc m em G P T ->
  (P = (p_inact) -> T = ltt_end).
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc eq_refl).
       subst.
       punfold H1. inversion H1. easy.
       apply st_mon.
Qed.













