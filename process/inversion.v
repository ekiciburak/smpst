From SST Require Import src.unscoped src.expressions process.processes process.typecheck type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Lemma typable_implies_wfC_helper : forall Pr STT,
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ wfC t)) Pr STT ->
  Forall
  (fun u : option (sort * ltt) =>
   u = None \/
   (exists (s : sort) (t : ltt), u = Some (s, t) /\ upaco1 wf bot1 t))
  STT.
Proof.
  intro Pr. induction Pr; intros; try easy.
  destruct STT; try easy.
  destruct STT; try easy.
  specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ wfC t)) a o Pr STT); intros.
  destruct H0. clear H1. specialize(H0 H); intros. clear H. destruct H0.
  specialize(IHPr STT H0); intros.
  apply Forall_cons; try easy.
  destruct H; try easy. left; easy. right.
  destruct H. destruct H. destruct H. exists x0, x1. destruct H. destruct H1. 
  split. easy. unfold upaco1. left. easy.
Qed.

Lemma extended_SList : forall l S T, SList (extendLTT l [] (Some (S, T))).
Proof.
  intro l. induction l; try easy.
Qed.

Lemma typable_implies_wfC_helper2 : forall p l S T,
  wfC T ->
  wf (upaco1 wf bot1) (ltt_send p (extendLTT l [] (Some (S, T)))).
Proof.
  intros p l. induction l; intros; try easy.
  simpl in *.
  apply wf_send; try easy. apply Forall_cons; try easy. right.
  exists S, T. split. easy. unfold upaco1. unfold wfC in H. left. easy.
  simpl. 
  constructor. simpl. apply extended_SList.
  apply Forall_cons; try easy. left. easy.
  specialize(IHl S T H); intros. inversion IHl; try easy.
Qed.

Lemma SList_induc {A} : forall x (xs : list (option A)), SList (x :: xs) -> (xs = [] \/ SList xs).
Proof.
  intros. destruct xs.
  left. easy. right. simpl in *. 
  destruct o. destruct x. easy. easy. 
  destruct x. easy. easy.
Qed.

Lemma SList_inducb {A} : forall x (xs : list (option A)), SList xs -> SList (x::xs).
Proof.
  intros. simpl.
  destruct x; try easy.
  destruct xs; try easy.
Qed.

Lemma typable_implies_wfC_helper3 : forall Pr STT,
    SList Pr ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ wfC t)) Pr STT ->
    SList STT.
Proof.
  intro Pr. induction Pr; intros; try easy.
  destruct STT; try easy.
  specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ wfC t)) a o Pr STT); intros.
  destruct H1. specialize(H1 H0). clear H0 H2.
  destruct H1. destruct H0.
  destruct H0. subst. simpl. apply IHPr; try easy.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. subst.
  
  destruct Pr; try easy.
  specialize(Forall2_length H1); intros. simpl in H0.
  specialize(length_zero_iff_nil STT); intros. destruct H2. clear H4.
  specialize(H2 (ssrfun.esym H0)). subst. easy.
  apply SList_inducb. apply IHPr; try easy.
Qed.
  

Lemma typable_implies_wfC [P : process] [Gs : ctxS] [Gt : ctxT] [T : ltt] :
  typ_proc Gs Gt P T -> wfC T.
Proof.
  intros. induction H using typ_proc_ind_ref; try easy.
  - unfold wfC. pfold. constructor.
  - unfold wfC. pfold. constructor; try easy.
    apply typable_implies_wfC_helper3 with (Pr := Pr); try easy.
    apply typable_implies_wfC_helper with (Pr := Pr); try easy.
  - unfold wfC. pfold. 
    apply typable_implies_wfC_helper2; try easy.
Qed.

Lemma _a23_a: forall p Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_recv p Q) -> 
  (exists STT, length Q = length STT /\ subtypeC (ltt_recv p STT) T /\ 
  List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) Gt p t)) Q STT /\ SList Q).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H3. destruct H4. 
       exists x.
       split; try easy. split; try easy.
       specialize(stTrans (ltt_recv p x) t t' H4 H1); intros.
       easy.
       inversion H0. subst. exists STT.
       split. easy. split. apply stRefl. easy.
Qed.
(* 
Lemma _a23_b: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S S' T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,(S',T'))]) T.
Proof. intros p l e Q P Gs Gt T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H1).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split.
       specialize(sc_sub cs e S S); intro HSS.
       apply HSS. easy. apply srefl. 
       split.
       specialize(tc_sub cs ct Q T' T'); intro HTS.
       apply HTS. easy.
       apply stRefl. split. easy.
       destruct Ha as (Ha,(Hb,(Hc,Hd))).
       specialize(stTrans (ltt_send p [(l, (S', T'))]) t t' Hd H0); intro HT.
       apply HT.
       exists S. exists S. exists T.
       inversion H1. subst.
       split. easy. split. easy.
       split. apply srefl.
       apply stRefl. 
Qed.
 *)
Lemma _a23_bf: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\  subtypeC (ltt_send p (extendLTT l [] (Some (S,T')))) T.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H2); intros. destruct IHtyp_proc. destruct H3. destruct H3. destruct H4.
  exists x. exists x0. split; try easy. split; try easy.
  specialize(stTrans (ltt_send p (extendLTT l [] (Some (x, x0)))) t t' H5 H0); intros; try easy.
  inversion H1. subst.
  exists S. exists T. split; try easy. split; try easy. apply stRefl. 
Qed.
(* 
Lemma _a23_bs: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> forall S T', subtypeC (ltt_send p [(l,(S,T'))]) T -> 
  typ_expr Gs e S /\ typ_proc Gs Gt Q T'.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H1); intros. 
  specialize(stTrans (ltt_send p [(l, (S, T'))]) t t' IHtyp_proc H0); intros; try easy.
  inversion H3. subst.
  exists S. exists T. split; try easy. 
Qed.
 *)
Lemma _a23_c: forall P e Q1 Q2 T Gs Gt,
  typ_proc Gs Gt P T ->
  P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc Gs Gt Q1 T1 /\ typ_proc Gs Gt Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T /\ typ_expr Gs e sbool.
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
       exists T. exists T.
       split. easy. split. easy. split. apply stRefl. split. apply stRefl. easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T1,(T2,(Ha,(Hb,(Hc,Hd))))).
       exists T1. exists T2.
       split.
       specialize(tc_sub cs ct Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. specialize(typable_implies_wfC Ha); easy.
       split. easy. split. 
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       split. destruct Hd.
       specialize(stTrans T2 t t' H3 H1); intro HT. easy.
       destruct Hd. easy.
Qed.

Lemma _a23_d: forall P Q T'' Gs Gt,
  typ_proc Gs Gt P T'' ->
  P = (p_rec Q)   -> exists T T', (typ_proc Gs (Some T :: Gt) Q T' /\ subtypeC T T' /\ subtypeC T' T'').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. exists t'. 
       split. easy. split. easy. apply stRefl.
              
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H3. destruct H3. destruct H4. 
       exists x. exists x0.
       split. easy. split. easy. 
       specialize(stTrans x0 t t' H5 H1); intros. easy.
Qed. 


Lemma _a23_e: forall P X T Gs Gt,
  typ_proc Gs Gt P T ->
  (P = (p_var X) -> exists T', onth X Gt = Some T' /\ subtypeC T' T /\ wfC T').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. split. easy. split. apply stRefl. easy.
       
       specialize(IHtyp_proc H0); intros. destruct IHtyp_proc.
       destruct H3.
       exists x. split. easy. split. destruct H4.
       specialize(stTrans x t t' H4 H1); intros; try easy. easy.
Qed.
       

Lemma _a23_f: forall P T Gs Gt,
  typ_proc Gs Gt P T ->
  P = p_inact -> T = ltt_end.
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc eq_refl).
       subst.
       punfold H1. inversion H1. easy.
       (* need monotone2 subtype *)
Admitted.
