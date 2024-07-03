From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

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

Lemma _a23_a: forall em p L Q P Gs Gt T, 
  typ_proc em Gs Gt P T ->
  P = (p_recv p (zip L Q)) -> 
  (exists T' S, length T' = length L -> length T' = length S -> length T' = length Q -> subtypeC (ltt_recv p (zip (zip L S) T')) T /\  
  List.Forall (fun u => typ_proc (Datatypes.S em) (extendS Gs em (fst u)) Gt (fst (snd u)) (snd (snd u))) (zip S (zip Q T'))).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T',IHtyp_proc).
       exists T'.
       simpl.
       destruct IHtyp_proc as [S'].
       exists S'.
       intros Hla1 Hla2 Hla3.
       split.
       specialize(H4 Hla1 Hla2 Hla3).
       destruct H4 as (IHtyp_proc, Ha).
       specialize(stTrans (ltt_recv p (zip (zip L S') T')) t t' IHtyp_proc); intro HT.
       apply HT.
       easy.
       
       (**)
       destruct H4 as (IHtyp_proc, Ha). easy. easy. easy.
       apply Forall_forall.
       intros (x1,(x2,x3)) Hx.
       simpl in *.
       rewrite Forall_forall in Ha.
       specialize(Ha (x1,(x2,x3))). simpl in Ha.
       specialize(tc_sub (Datatypes.S em) (extendS cs em x1) (extendS cs' em x1) ct ct' x2 x3 x3); intro HTC.
       apply HTC.
(*        specialize(tc_sub m (Datatypes.S em) c); intro HTC. *)
       apply Ha. easy.
       apply stRefl.
       simpl.
       split. split. split. right. easy. easy. easy.

       rewrite Forall_forall in H3.
       exists T. exists ST.
       intros Hla1 Hla2 Hla3.
       split.
       inversion H0. subst.
       assert(length (zip L0 ST) = length L0) as Hasrt1.
       { symmetry.
         apply zip_len. easy.
       }
       assert(L0 = L /\ P = Q).
       { 
          specialize(eq_trans H H1); intros.
          specialize(eq_trans H2 Hla1); intros.
          specialize(eq_trans (eq_sym Hla1) Hla3); intros.
          specialize(zip_eq L0 L P Q H4 H5 H7 H6); intros.
          easy.
       }
       subst.
       pfold.
       destruct H4.
       replace L0 with L.
       apply sub_in. easy. easy.
       clear H H1 H2 H3 H6 Hla1 Hla2 Hla3 Hasrt1.
       apply Forall_forall.
       intros (x1,x2) Hx.
       induction ST; intros.
       simpl in Hx. easy.
       simpl in Hx.
       destruct Hx as [Hx | Hx].
       inversion Hx. subst.
       simpl. apply srefl.
       simpl. apply IHST. easy. 

       apply Forall_forall.
       intros (x1,x2) Hx.
       clear H H1 H2 H3 Hla1 Hla2 Hla3 Hasrt1.
       induction T; intros.
       simpl in Hx. easy.
       simpl in Hx.
       simpl in IHT.
       destruct Hx as [Hx | Hx].
       inversion Hx. subst. simpl.
       specialize(stRefl x2); intro HT.
       punfold HT. apply st_mon.
       simpl. apply IHT. easy.
       
       (**)
       apply Forall_forall.
       intros (x1,(x2,x3)) Hx.
       simpl in *.
       specialize(H3 (x1,(x2,x3))). simpl in H3.
       inversion H0. subst.
       apply H3.
       assert(L0 = L /\ P = Q).
       { 
          specialize(eq_trans H H1); intros.
          specialize(eq_trans H2 Hla1); intros.
          specialize(eq_trans (eq_sym Hla1) Hla3); intros.
          specialize(zip_eq L0 L P Q H4 H5 H7 H6); intros.
          easy.
       }
       destruct H4.
       subst.
       easy.
Qed.


Lemma _a23_b: forall em p l e Q P Gs Gt T, 
  typ_proc em Gs Gt P T ->
  P = (p_send p l e Q) -> exists S S' T', typ_expr Gs e S /\ typ_proc em Gs Gt Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,S',T')]) T.
Proof. intros em p l e Q P Gs Gt T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H3).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split.
       specialize(sc_sub cs cs' e S S); intro HSS.
       apply HSS. easy. apply srefl. easy.
       split.
       specialize(tc_sub em cs cs' ct ct' Q T' T'); intro HTS.
       apply HTS. easy.
       apply stRefl. easy. easy. split. easy.
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

Lemma _a23_c: forall P em e Q1 Q2 T Gs Gt,
  typ_proc em Gs Gt P T ->
  P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc em Gs Gt Q1 T1 /\ typ_proc em Gs Gt Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T.
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
       specialize(tc_sub em cs cs' ct ct' Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. easy. easy.
       split.
       specialize(tc_sub em cs cs' ct ct' Q2 T2 T2); intro HTS.
       apply HTS. easy. apply stRefl. easy. easy. 
       split.
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       specialize(stTrans T2 t t' Hd H1); intro HT. easy.
Qed.

Lemma _a23_d: forall P em x Q T Gs Gt,
  typ_proc em Gs Gt P T ->
  P = (p_rec x Q)   -> typ_proc em Gs (extendT Gt x T) Q T.
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       unfold ct' in *. easy.

       subst.
       apply tc_sub with
       (ct := extendT ct x t) (cs := cs) (t := t).
       apply IHtyp_proc. easy.
       easy. easy.
       split. split. split. left. easy. easy.
Qed.

Lemma helper_a23_e_1 : forall x X n l x0 ct t, (Some t = lookupT ct X) -> (leq_ctxT (extendT x0 X x) ct) -> ((X =? n)%nat = false)
    -> subtypeC x t -> leq_ctxT (consT X x (consT n l x0)) (consT n l ct).
Proof. 
  unfold leq_ctxT at 2. unfold leq_tinctx_prop.
  induction lookupT; intros; try easy.
  
  case_eq (Nat.eqb n0 X); intros; try easy.
  specialize(natb_to_prop n0 X H3); intros. subst. simpl.
  replace (X =? X)%nat with true.
  replace (X =? n)%nat with false.
  replace (lookupT ct X) with (Some t).
  easy.
  
  simpl. 
  replace (n0 =? X)%nat with false.
  case_eq (Nat.eqb n0 n); intros; try easy.
  unfold leq_ctxT in H0. unfold leq_tinctx_prop in H0.
  specialize(H0 n0). simpl in H0.
  replace (n0 =? X)%nat with false in H0. easy.
  
  case_eq (Nat.eqb n0 X); intros; try easy.
  specialize(natb_to_prop n0 X H3); intros. subst. simpl.
  replace (X =? X)%nat with true.
  replace (X =? n)%nat with false.
  replace (lookupT ct X) with (Some t).
  easy.
  
  simpl. 
  replace (n0 =? X)%nat with false.
  case_eq (Nat.eqb n0 n); intros; try easy.
  unfold leq_ctxT in H0. unfold leq_tinctx_prop in H0.
  specialize(H0 n0). simpl in H0.
  replace (n0 =? X)%nat with false in H0. easy.
  
  apply emptyT.
  apply 0.
  
Qed.

Lemma _a23_e: forall P em X T Gs Gt,
  typ_proc em Gs Gt P T ->
  (P = (p_var X) -> exists T' G', leq_ctxT (extendT G' X T') Gt /\ subtypeC T' T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       induction ct; intros. easy.
       simpl in H.
       
       case_eq (Nat.eqb X n); intros Hb.
       
       replace (X =? n)%nat with true in H.
       inversion H. 
       exists l. exists ct. unfold extendT. 
       split. 
       specialize(natb_to_prop X n Hb); intros.
       subst.
       apply leq_ctxT_refl.
       easy.

       replace (X =? n)%nat with false in H.
       specialize(IHct H).
       destruct IHct. destruct H1.
       exists x. exists (consT n l x0).
       split. unfold extendT.
       destruct H1.
       specialize(helper_a23_e_1 x X n l x0 ct t H H1 Hb H2); intros.
       easy.
       
       destruct H1.
       easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H4.
       specialize(ref_stronger_T ct ct' H3); intros.
       destruct H4.
       specialize(leq_ctxT_trans (extendT x0 X x) ct ct' H4 H5); intros.
       specialize(stTrans x t t' H6 H1); intros.
       exists x. exists x0.
       split.
       apply H7.
       apply H8.
      
Qed.

Lemma _a23_f: forall P em T Gs Gt,
  typ_proc em Gs Gt P T ->
  P = p_inact -> T = ltt_end.
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc eq_refl).
       subst.
       punfold H1. inversion H1. easy.
       apply st_mon.
Qed.
