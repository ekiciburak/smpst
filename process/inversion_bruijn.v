From SST Require Import aux.unscoped aux.expressions process.processes_bruijn process.typecheck_bruijn type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Lemma empty_nil: forall {A: Type} (l: list A),
  0 = length l <-> l = [].
Proof. intros A l.
       case l; intros; easy.
Qed.
   

Lemma zip_eq: forall {A B: Type} (l1 l3: list A) (l2 l4: list B),
  length l1 = length l2 -> length l2 = length l3 -> length l3 = length l4 ->
  (zip l1 l2) = (zip l3 l4) ->
  l1 = l3 /\ l2 = l4.
Proof. intros A B l1.
       induction l1; intros.
       - simpl in *.
         rewrite <- H in H0.
         rewrite <- H0 in H1.
         rewrite empty_nil in H.
         rewrite empty_nil in H0.
         rewrite empty_nil in H1.
         subst. easy.
       - simpl in H.
         case_eq l2; intros.
         + subst. simpl in *. easy.
         + subst. simpl in *.
           case_eq l3; intros.
           ++ subst. easy.
           ++ case_eq l4; intros.
              -- subst. easy.
              -- subst. simpl in *.
                 inversion H2. subst.
                 inversion H.
                 inversion H1.
                 inversion H0.
                 specialize(IHl1 l0 l l2 H4 H7 H5 H6).
                 split. f_equal. easy.
                 f_equal. easy.
Qed.

Lemma zip_len: forall {A B: Type} (l1: list A) (l2: list B),
  length l1 = length l2 -> length l1 = length (zip l1 l2).
Proof. intros A B l1.
       induction l1; intros.
       - simpl in H. rewrite empty_nil in H.
         subst. simpl. easy.
       - simpl in H. simpl.
         case_eq l2; intros.
         subst. easy.
         subst. simpl in H.
         inversion H.
         simpl. f_equal.
         apply IHl1. easy.
Qed.

(* Lemma remove_S : forall {a b : fin}, S a = S b -> a = b.
Proof.
  intros.
  inversion H. easy.
Qed.
 *)
Lemma _a23_a: forall p L Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_recv p L Q) -> 
  (exists T' ST, length T' = length L /\ length T' = length ST /\ length T' = length Q /\ subtypeC (ltt_recv p (zip L (zip ST T'))) T /\ SSortedNList L /\ 
  List.Forall2 (fun u v => typ_proc (Some (fst v) :: Gs) Gt u (snd v)) Q (zip ST T')).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5. destruct H6.
       exists x. exists x0.
       split; try easy. split; try easy. split; try easy. split.
       specialize(stTrans (ltt_recv p (zip L (zip x0 x))) t t' H5 H1); intros.
       easy.
       split. easy. easy.
       inversion H0. subst. exists T. exists ST.   
       specialize(eq_trans H1 H2); intros.
       specialize(eq_trans H H5); intros.
       split; try easy.     
Qed.


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

Lemma _a23_bf: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\  subtypeC (ltt_send p [(l,(S,T'))]) T.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H1); intros. destruct IHtyp_proc. destruct H2. destruct H2. destruct H3.
  exists x. exists x0. split; try easy. split; try easy.
  specialize(stTrans (ltt_send p [(l, (x, x0))]) t t' H4 H0); intros; try easy.
  inversion H1. subst.
  exists S. exists T. split; try easy. 
Qed.

Lemma _a23_c: forall P e Q1 Q2 T Gs Gt,
  typ_proc Gs Gt P T ->
  P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc Gs Gt Q1 T1 /\ typ_proc Gs Gt Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T /\ typ_expr Gs e sbool.
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
       exists T. exists T.
       split. easy. split. easy. split. easy. easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T1,(T2,(Ha,(Hb,(Hc,Hd))))).
       exists T1. exists T2.
       split.
       specialize(tc_sub cs ct Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. split. easy. split. 
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       split. destruct Hd.
       specialize(stTrans T2 t t' H2 H1); intro HT. easy.
       destruct Hd. easy.
Qed.

Lemma _a23_d: forall P Q T'' Gs Gt,
  typ_proc Gs Gt P T'' ->
  P = (p_rec Q)   -> exists T T', (typ_proc Gs (Some T :: Gt) Q T' /\ subtypeC T T' /\ subtypeC T' T'').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. exists t'. 
       split. easy. split. easy. easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H2. 
       exists x. exists x0.
       destruct H2. destruct H3. 
       split. easy. split. easy. 
       specialize(stTrans x0 t t' H4 H1); intros. easy.
Qed. 


Lemma _a23_e: forall P X T Gs Gt,
  typ_proc Gs Gt P T ->
  (P = (p_var X) -> exists T', onth X Gt = Some T' /\ subtypeC T' T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. split. easy. easy.
       
       specialize(IHtyp_proc H0); intros. destruct IHtyp_proc.
       destruct H2.
       exists x. split. easy.
       specialize(stTrans x t t' H3 H1); intros; try easy.
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
       apply st_mon.
Qed.
