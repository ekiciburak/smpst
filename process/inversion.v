From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck type.global tree.global tree.local.
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

Lemma remove_S : forall {a b : fin}, S a = S b -> a = b.
Proof.
  intros.
  inversion H. easy.
Qed.

Lemma _a23_a: forall em p lb pr L Q P Gs Gt T, 
  typ_proc em Gs Gt P T ->
  P = (p_recv p lb pr L Q) -> 
  (exists ty st T' S, length (ty::T') = length (lb::L) -> length (ty::T') = length (st::S) -> length (ty::T') = length (pr::Q) -> subtypeC (ltt_recv p (zip (zip (lb::L) (st::S)) (ty::T'))) T /\  
  typ_proc (Datatypes.S em) (extendS Gs em st) Gt pr ty /\
  List.Forall (fun u => typ_proc (Datatypes.S em) (extendS Gs em (fst u)) Gt (fst (snd u)) (snd (snd u))) (zip S (zip Q T'))).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (q',IHtyp_proc).
       destruct IHtyp_proc. destruct H2. destruct H2. simpl in H2.
       exists q'. exists x. exists x0. exists x1. simpl.
       intros.
       specialize(H2 H3 H4 H5); intros.
       destruct H2. destruct H6. split.
       specialize(stTrans (ltt_recv p ((lb, x, q') :: zip (zip L x1) x0)) t t' H2 H1); intros.
       easy.
       split. easy.
       apply Forall_forall.
       intros (y1, (y2, y3)) Hx.
       simpl in *.
       rewrite Forall_forall in H7.
       specialize(H7 (y1,(y2,y3)) Hx); intros. 
       simpl in H7. easy.
       
       clear IHtyp_proc.
       inversion H0. subst. 
       exists ty. exists st. exists T. exists ST.
       intros. simpl in *.
       specialize(remove_S H5); intros. 
       specialize(remove_S H6); intros. 
       specialize(remove_S H7); intros.
       clear H5 H6 H7. 
       split. easy. split. easy. easy.
Qed.


Lemma _a23_b: forall em p l e Q P Gs Gt T, 
  typ_proc em Gs Gt P T ->
  P = (p_send p l e Q) -> exists S S' T', typ_expr Gs e S /\ typ_proc em Gs Gt Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,S',T')]) T.
Proof. intros em p l e Q P Gs Gt T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H1).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split.
       specialize(sc_sub cs e S S); intro HSS.
       apply HSS. easy. apply srefl. 
       split.
       specialize(tc_sub em cs ct Q T' T'); intro HTS.
       apply HTS. easy.
       apply stRefl. split. easy.
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
  P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc em Gs Gt Q1 T1 /\ typ_proc em Gs Gt Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T /\ typ_expr Gs e sbool.
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
       specialize(tc_sub em cs ct Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. split. easy. split. 
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       split. destruct Hd.
       specialize(stTrans T2 t t' H2 H1); intro HT. easy.
       destruct Hd. easy.
Qed.

Lemma _a23_d: forall P em x Q T'' Gs Gt,
  typ_proc em Gs Gt P T'' ->
  P = (p_rec x Q)   -> exists T T', (typ_proc em Gs (extendT Gt x T) Q T' /\ subtypeC T T' /\ subtypeC T' T'').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. exists t. 
       split. easy. split. easy. easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H2. 
       exists x0. exists x1. 
       destruct H2. destruct H3. 
       split. easy. split. easy. 
       specialize(stTrans x1 t t' H4 H1); intros. easy.
Qed. 
(* 

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
  
Qed. *)

Lemma refl_eq_ctxT : forall m, consistent_ctxT m -> eq_ctxT m m.
Proof.
  intros. 
  unfold eq_ctxT. intros.
  split. easy. split. easy.
  induction lookupT. easy. easy.
Qed.

Lemma band_destruct : forall (a b : bool), true = a -> true = b -> true = (a && b)%bool.
Proof.
  intros. destruct H0. replace a with true. easy.
Qed.

Lemma bnat_comm : forall a b, ((a =? b)%nat = (b =? a)%nat).
Proof. 
      intros.
      specialize(Nat.eqb_eq a b); intros.
      specialize(Nat.eqb_eq b a); intros.
      specialize(Nat.eqb_neq a b); intros.
      specialize(Nat.eqb_neq b a); intros.
      case_eq (a =? b)%nat.
      - intros.
        destruct H. specialize(H H3). 
        specialize(eq_sym H); intros.
        destruct H0. specialize(H6 H5). 
        replace (b =? a)%nat with true.
        easy.
      - intros. destruct H1. specialize(H1 H3); intros.
        specialize(not_eq_sym H1); intros.
        destruct H2. specialize(H6 H5); intros. easy.
Qed.

Lemma swap_eq_ctxT : forall m X Y T T', consistent_ctxT (consT X T (consT Y T' m)) -> eq_ctxT (consT X T (consT Y T' m)) (consT Y T' (consT X T m)).
Proof.
  intros.
  unfold eq_ctxT. intros.
  split. easy. split. 
  assert(consistent_ctxT (consT Y T' (consT X T m))).
  {
    simpl in H.
    simpl.
    case_eq (Nat.eqb X Y); intros.
    replace (X =? Y)%nat with true in H. destruct H. easy.
    replace (X =? Y)%nat with false in H.
    specialize(bnat_comm Y X); intros.
    specialize(eq_trans H1 H0); intros. 
    replace (Y =? X)%nat with false.
    split. destruct H. destruct H3.
    easy. destruct H. destruct H3. split. easy. easy.
  }
  easy.
  simpl. simpl in H.
  case_eq (Nat.eqb n X); intros. 
  - case_eq (Nat.eqb n Y); intros; try easy.
    specialize(Nat.eqb_eq n X); intros. destruct H2. specialize(H2 H0); intros.
    specialize(Nat.eqb_eq n Y); intros. destruct H4. specialize(H4 H1); intros.
    specialize(eq_sym H2); intros. specialize(eq_trans H6 H4); intros.
    specialize(Nat.eqb_eq X Y); intros. destruct H8. specialize(H9 H7); intros.
    replace (X =? Y)%nat with true in H. simpl in H. easy.
  - case_eq (Nat.eqb n Y); intros. try easy.
    easy.
Qed.

Lemma sym_eq_ctxT : forall m1 m2, eq_ctxT m1 m2 -> eq_ctxT m2 m1.
Proof.
  intros.
  unfold eq_ctxT in *.
  intros.
  specialize(H n); intros.
  destruct H. destruct H0.
  split. easy. split. easy. easy.
Qed.

Lemma trans_eq_ctxT : forall m1 m2 m3, 
      eq_ctxT m1 m2 -> eq_ctxT m2 m3 -> eq_ctxT m1 m3.
Proof.
  intros.
  unfold eq_ctxT in *.
  intros.
  split. specialize(H n); intros. easy. split. specialize(H0 n); intros. easy.
  specialize(H n); intros.
  specialize(H0 n); intros. 
  destruct H0. destruct H1. destruct H. destruct H3. 
  specialize(eq_trans H4 H2); intros. easy.
Qed.
  
Lemma cons_eq_ctxT_helper : forall m1 m2 n, eq_ctxT m1 m2 -> lookupT m1 n = None -> lookupT m2 n = None.
Proof. 
  intros.
  unfold eq_ctxT in H. specialize(H n); intros.
  destruct H. destruct H1.
  specialize(eq_trans (eq_sym H2) H0); intros.
  easy.
Qed.

Lemma cons_eq_ctxT : forall m1 m2 n T, eq_ctxT m1 m2 -> lookupT m1 n = None -> eq_ctxT (consT n T m1) (consT n T m2).
Proof.
  intros.
  pose proof H as H1.
  unfold eq_ctxT. intros.
  specialize(H n0); intros. destruct H. destruct H2. 
  split.
  simpl. split. easy. easy.
  split. simpl. split. 
  specialize(cons_eq_ctxT_helper m1 m2 n H1 H0); intros.
  easy. easy.
  simpl. 
  case_eq (n0 =? n)%nat; intros; try easy.
Qed.

Lemma _a23_e: forall P em X T Gs Gt,
  typ_proc em Gs Gt P T ->
  (P = (p_var X) -> exists T' G', eq_ctxT (extendT G' X T') Gt /\ subtypeC T' T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       
       induction ct. simpl in H2. easy.
       simpl in H2.
       case_eq (Nat.eqb X n); intros.
       replace (X =? n)%nat with true in H2. inversion H2.
       simpl in H1. destruct H1.
       specialize(IHct H4); intros.
       unfold extendT in *.
       exists l. exists ct. split; try easy.
       specialize(natb_to_prop X n H3); intros. replace X with n. easy.
       
       replace (X =? n)%nat with false in H2.
       simpl in H1. destruct H1. 
       specialize(IHct H4 H2); intros.
       destruct IHct. destruct H5.
       exists x. exists (extendT x0 n l).
       unfold extendT in *.
       destruct H5.
       specialize(sym_eq_ctxT (consT X x x0) ct H5); intros.
       specialize(cons_eq_ctxT ct (consT X x x0) n l H7 H1); intros.
       Compute (swap_eq_ctxT).
       specialize(swap_eq_ctxT x0 X n x l); intros.
       specialize(sym_eq_ctxT (consT n l ct) (consT n l (consT X x x0))); intros.
       
       simpl in H9. replace (X =? n)%nat with false in H9. 
       assert(lookupT x0 X = None /\ lookupT x0 n = None /\ consistent_ctxT x0).
       {
         split; try easy. 
         unfold eq_ctxT in H5. simpl in H5.
         specialize(H5 n); intros. destruct H5. destruct H5.
         easy. split.
         
         unfold eq_ctxT in H8. simpl in H8.
         specialize(bnat_comm n X ); intros. specialize(eq_trans H11 H3); intros.
         replace (n =? X)%nat with false in H8.
         specialize(H8 n); intros. destruct H8. destruct H13. destruct H13. easy.
         
         unfold eq_ctxT in H5. specialize(H5 n); intros. simpl in H5.
         destruct H5. destruct H5. easy.
       }
       specialize(H9 H11); intros.
       specialize(sym_eq_ctxT (consT X x (consT n l x0)) (consT n l (consT X x x0)) H9); intros.
       specialize(trans_eq_ctxT (consT n l ct) (consT n l (consT X x x0)) (consT X x (consT n l x0)) H8 H12); intros.
       split. 
       specialize(sym_eq_ctxT (consT n l ct) (consT X x (consT n l x0)) H13); intros.
       easy. easy.
       
       specialize(IHtyp_proc H0); intros.
       destruct IHtyp_proc. destruct H2.
       exists x. exists x0. 
       destruct H2. split.
       easy.
       specialize(stTrans x t t' H3 H1); intros.
       easy.
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
