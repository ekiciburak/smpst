From mathcomp Require Import all_ssreflect.
From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck process.inversion process.inversion_expr type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.


Fixpoint RemoveT (n : fin) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: RemoveT m xs
        | 0   => None :: xs 
      end
    | [] => []
  end.

Fixpoint extendT (n : fin) (T : ltt) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: extendT m T xs
        | 0   => Some T :: xs 
      end 
    | [] =>
      match n with 
        | S m => None :: extendT m T [] 
        | 0   => [Some T]
      end 
  end.
  
Lemma onth_nil : forall n, @onth ltt n [] = None.
Proof.
  intros. induction n. easy. easy.
Qed.

Lemma remove_var : forall X n T Gt x, X <> n -> onth n (extendT X T Gt) = Some x -> onth n Gt = Some x.
Proof.
  intros X n T Gt. revert X T Gt. induction n; intros; try easy.
  destruct X; try easy. destruct Gt. easy. simpl in H0. simpl. easy.
  destruct X. destruct Gt; try easy. simpl in H0. simpl. 
  specialize(onth_nil n); intros.
  specialize(eq_trans (ssrfun.esym H1) H0); intros. easy.
  specialize(Nat.succ_inj_wd_neg X n); intros. destruct H1. 
  specialize(H1 H); intros. clear H2.
  destruct Gt. 
  - simpl in H0.
    specialize(IHn X T [] x H1 H0); intros.
    specialize(onth_nil n); intros.
    specialize(eq_trans (ssrfun.esym H2) IHn); intros. easy.
  - simpl in *. 
    apply IHn with (X := X) (T := T); try easy.
Qed.

Lemma extend_extract : forall n (T : ltt) Gt, onth n (extendT n T Gt) = Some T.
Proof.
  intro n. induction n using strong_ind.
  intros t gt. revert t. induction gt.
  - intros. destruct n. easy.
    simpl. apply H; try easy. apply Nat.lt_succ_diag_r.
  - intros. destruct n. easy.
    simpl. apply H; try easy. apply Nat.lt_succ_diag_r.
Qed.

Lemma positive_list_length_dst {A} : forall (xs : list A) n, length xs = S(n) -> exists y ys, y::ys = xs.
Proof.
  intros.
  induction xs. easy.
  exists a. exists xs. easy.
Qed.

Lemma positive_list_length_dst_zip {A B} : forall (xs : list A) (ys : list B) n, length (zip xs ys) = S n -> exists t ts u us, (t,u) :: zip ts us = zip xs ys.
Proof.
  intros. 
  specialize(positive_list_length_dst (zip xs ys) n H); intros.
  destruct H0. destruct H0.
  exists x.1. exists (list_map fst x0). exists x.2. exists (list_map snd x0).
  specialize(unzip_zip x0); intros. 
  replace (zip (list_map fst x0) (list_map snd x0)) with x0.
  specialize(surjective_pairing x); intros. 
  replace (x.1, x.2) with x. easy.
Qed.

Lemma typable_implies_wfC_helper : forall (T : seq ltt) (Pr : seq process) (ST : seq sort),
  length ST = length Pr ->
  length Pr = length T ->
  Forall2 (fun=> (fun v : sort * ltt => wfC v.2)) Pr (zip ST T) ->
  Forall (upaco1 wf bot1) T.
Proof.
  intro T. induction T; intros; try easy.
  destruct Pr; try easy. destruct ST; try easy.
  simpl in *.
  specialize(Forall2_cons_iff (fun=> (fun v : sort * ltt => wfC v.2)) p (s,a) Pr (zip ST T)); intros.
  destruct H2. clear H3. specialize(H2 H1). clear H1. destruct H2.
  specialize(IHT Pr ST); intros.
  apply Forall_cons; try easy.
  simpl in H1. unfold wfC in H1. unfold upaco1. left. easy.
  apply IHT; try easy.
  apply eq_add_S. easy. apply eq_add_S. easy.
Qed.

Lemma typable_implies_wfC [P : process] [Gs : ctxS] [Gt : ctxT] [T : ltt] :
  typ_proc Gs Gt P T -> wfC T.
Proof.
  intros. induction H using typ_proc_ind_ref; try easy.
  - unfold wfC. pfold. constructor.
  - unfold wfC. pfold. constructor; try easy.
    apply eq_trans with (y := length Pr); try easy.
    apply typable_implies_wfC_helper with (Pr := Pr) (ST := ST); try easy.
  - unfold wfC. pfold. 
    specialize(wf_send (upaco1 wf bot1) p [l] [S] [T]); intros.
    simpl in *. apply H0; try easy. apply sort1.
    apply Forall_cons; try easy.
    unfold upaco1. left. easy.
Qed.

Lemma slideT_helper : forall llp x0 x X m k l Gs Gtl Gtr tm,
    Forall
      (fun Q : process =>
       forall (X m l k : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : seq (option ltt))
         (T : ltt),
       typ_proc Gs (Gtl ++ Gtr) (incr_free l k X m Q) T ->
       length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k X.+1 m Q) T) llp ->
    Forall2 (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gs) (Gtl ++ Gtr) u v.2)
       (list_map (incr_free l k.+1 X m) llp) (zip x0 x) ->
    length Gtl = l ->
    Forall2
      (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gs) (Gtl ++ tm :: Gtr) u v.2)
      (list_map (incr_free l k.+1 X.+1 m) llp) (zip x0 x).
Proof.
  intro llp. induction llp; intros; try easy.
  - specialize(Forall2_length H0); intros.
    specialize(map_length (incr_free 0 1 X m) []); intros.
    specialize(eq_trans (esym H2) H3); intros. simpl in H4.
    specialize(length_zero_iff_nil (zip x0 x)); intros. destruct H5. specialize(H5 H4); intros.
    replace (zip x0 x) with (@nil (sort * ltt)). easy.
  - specialize(Forall2_length H0); intros.
    specialize(map_length (incr_free l k.+1 X m) (a::llp)); intros.
    specialize(eq_trans (esym H2) H3); intros. simpl in H4.
    specialize(positive_list_length_dst_zip x0 x (length llp) H4); intros.
    destruct H5. destruct H5. destruct H5. destruct H5. 
    replace (zip x0 x) with ((x1,x3) :: zip x2 x4) in *. clear H2 H3 H4 H5.
    simpl in H0.
    specialize(Forall2_cons_iff (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gs) (Gtl ++ Gtr) u v.2) (incr_free l k.+1 X m a) (x1,x3) (list_map (incr_free l k.+1 X m) llp) (zip x2 x4)); intros.
    destruct H2. clear H3. specialize(H2 H0); intros. clear H0. destruct H2.
    specialize(Forall_cons_iff (fun Q : process =>
       forall (X m l k : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : seq (option ltt))
         (T : ltt),
       typ_proc Gs (Gtl ++ Gtr) (incr_free l k X m Q) T ->
       length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k X.+1 m Q) T)  a llp); intros. destruct H3. clear H4.
    specialize(H3 H); intros. clear H. destruct H3.
    specialize(IHllp x2 x4 X m k l Gs Gtl Gtr tm H3 H2 H1); intros. clear H2 H3.
    apply Forall2_cons; try easy.
    apply H. easy. easy.
Qed. 

Lemma onth_more {A} : forall l Gtl Gtr n X x (tm : option A),
      (l <= n) = true ->
      length Gtl = l ->
      onth (n + X)%coq_nat (Gtl ++ Gtr) = Some x ->
      Some x = onth (n + X.+1)%coq_nat (Gtl ++ tm :: Gtr).
Proof.
  intro l. induction l; intros; try easy.
  - specialize(length_zero_iff_nil Gtl); intros. destruct H2. specialize(H2 H0); intros. clear H3. subst.
    simpl.
    specialize(Nat.add_succ_r n X); intros. replace ((n + X.+1)%coq_nat) with ((n + X)%coq_nat.+1). simpl.
    simpl in H1. easy.
  - destruct n. easy.
    specialize(positive_list_length_dst Gtl l H0); intros.
    destruct H2. destruct H2. replace Gtl with (x0 :: x1) in *. clear H2.
    simpl in *.
    apply IHl; try easy.
    apply Nat.succ_inj. easy.
Qed.

Lemma onth_less {A} : forall l Gtl Gtr n x (tm : option A),
      (l <= n) = false ->
      length Gtl = l ->
      onth n (Gtl ++ Gtr) = Some x ->
      Some x = onth n (Gtl ++ tm :: Gtr).
Proof.
  intro l. induction l; intros; try easy.
  specialize(positive_list_length_dst Gtl l H0); intros.
  destruct H2. destruct H2. replace Gtl with (x0 :: x1) in *. 
  destruct n; try easy.
  simpl in *.
  apply IHl; try easy.
  apply Nat.succ_inj. easy.
Qed.

Lemma slideTp : forall Q X m l k tm Gs Gtl Gtr T,
typ_proc Gs (Gtl ++ Gtr) (incr_free l k X m Q) T -> length Gtl = l -> typ_proc Gs (Gtl ++ [tm] ++ Gtr) (incr_free l k X.+1 m Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(_a23_e (p_var (if l <= n then (n + X)%coq_nat else n)) (if l <= n then (n + X)%coq_nat else n) T Gs (Gtl ++ Gtr) H (erefl (p_var (if l <= n then (n + X)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    case_eq (l <= n); intros.
    - replace (l <= n) with true in H, H1.
      apply tc_sub with (t := x); try easy. 
      apply tc_var; try easy.
      apply onth_more with (l := l); try easy.
      specialize(typable_implies_wfC H); intros; try easy.
    - replace (l <= n) with false in H, H1.
      apply tc_sub with (t := x); try easy.
      apply tc_var; try easy.
      apply onth_less with (l := l); try easy.
      specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *. 
    specialize(_a23_f p_inact T Gs (Gtl++Gtr) H (erefl p_inact)); intros. subst. 
    apply tc_inact.
  - simpl in *.
    specialize(_a23_bf pt lb (incr_freeE k m ex) (incr_free l k X m Q) (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)) Gs (Gtl ++ Gtr) T H (erefl (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt [(lb, (x, x0))])); try easy.
    apply tc_send; try easy.
    apply IHQ. easy. easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_a pt llb (list_map (incr_free l k.+1 X m) llp) (p_recv pt llb (list_map (incr_free l k.+1 X m) llp)) Gs (Gtl ++ Gtr) T H0 (erefl (p_recv pt llb (list_map (incr_free l k.+1 X m) llp)))); intros.
    destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5. destruct H6.
    apply tc_sub with (t := (ltt_recv pt (zip llb (zip x0 x)))); try easy.
    
    specialize(eq_trans (esym H2) H3); intros; try easy.
    specialize(map_length (incr_free l k.+1 X m) llp); intros.
    specialize(map_length (incr_free l k.+1 X.+1 m) llp); intros.
    specialize(eq_trans H4 H9); intros.
    specialize(eq_trans H11 (esym H10)); intros.
    specialize(eq_trans (esym H3) H11); intros.
    specialize(eq_trans H13 (esym H10)); intros.
    apply tc_recv; try easy. clear H2 H3 H4 H6 H8 H9 H10 H11 H12 H13 H14.
    apply slideT_helper; try easy.
    specialize(typable_implies_wfC H0); intros; try easy.
  - simpl in *.
    specialize(_a23_c (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)) (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2) T Gs (Gtl ++ Gtr) H (erefl (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite; try easy.
    apply tc_sub with (t := x); try easy.
    apply IHQ1; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
    apply tc_sub with (t := x0); try easy.
    apply IHQ2; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *. 
    specialize(_a23_d (p_rec (incr_free l.+1 k X m Q)) (incr_free l.+1 k X m Q) T Gs (Gtl++Gtr) H (erefl (p_rec (incr_free l.+1 k X m Q)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    specialize(IHQ X m l.+1 k tm Gs (Some x :: Gtl) Gtr x0); intros.
    specialize(cat_cons (Some x) Gtl Gtr); intros.
    replace ((Some x :: Gtl) ++ Gtr) with (Some x :: Gtl ++ Gtr) in IHQ. clear H4.
    specialize(IHQ H1); intros. simpl in IHQ.
    specialize(eq_S (length Gtl) l H0); intros.
    specialize(IHQ H4). clear H0 H4.
    apply tc_sub with (t := x0); try easy.
    apply tc_mu with (t := x); try easy.
    specialize(typable_implies_wfC H1); intros; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
Qed.

Lemma slideT : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc Gs (tm :: Gt) (incr_free 0 0 X.+1 m Q) T.
Proof.
  intros.
  specialize(slideTp Q X m 0 0 tm Gs [] Gt T H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma slideSp_e : forall k m ex x Gsl Gsr tm,
  typ_expr (Gsl ++ Gsr) (incr_freeE k m ex) x ->
  length Gsl = k ->
  typ_expr (Gsl ++ tm :: Gsr) (incr_freeE k m.+1 ex) x.
Proof. 
  intros k m ex. revert k m. induction ex; intros; try easy.
  - simpl in *. 
    specialize(inv_expr_var (e_var (if k <= n then (n + m)%coq_nat else n)) (if k <= n then (n + m)%coq_nat else n) (Gsl ++ Gsr) x H (erefl (e_var (if k <= n then (n + m)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    apply sc_sub with (s := x0); try easy.
    apply sc_var.
    case_eq (k <= n); intros.
    - replace (k <= n) with true in H1. subst.
      apply onth_more with (l := length Gsl); try easy.
    - replace (k <= n) with false in H1. subst.
      apply onth_less with (l := length Gsl); try easy.
  - simpl in *. 
    specialize(inv_expr_vali (Gsl ++ Gsr) (e_val v) x v H (erefl (e_val v))); intros.
    destruct H1.
    - subst. destruct H1. destruct H0. subst. apply sc_vali.
    - subst. destruct H1. destruct H0. destruct H0. subst.
      inversion H0. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
      subst. apply sc_valn.
    - subst. destruct H0. destruct H0. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ (Gsl ++ Gsr) (e_succ (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_succ (incr_freeE k m ex)))); intros.
    destruct H1. destruct H2.
    - subst. apply sc_succ; try easy. apply IHex; try easy.
    - subst. apply sc_sub with (s := snat); try easy. apply sc_succ; try easy. apply IHex; try easy.
      apply sni.
  - simpl in *.
    specialize(inv_expr_neg (Gsl ++ Gsr) (e_neg (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_neg (incr_freeE k m ex)))); intros.
    destruct H1. subst. apply sc_neg. apply IHex; try easy.
  - simpl in *.
    specialize(inv_expr_not (Gsl ++ Gsr) (e_not (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_not (incr_freeE k m ex)))); intros. 
    destruct H1. subst. apply sc_not. apply IHex; try easy.
  - simpl in *.
    specialize(inv_expr_gt (Gsl ++ Gsr) (e_gt (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_gt (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H2.
    subst. apply sc_gt. apply IHex1; try easy. apply IHex2; try easy.
  - simpl in *.
    specialize(inv_expr_plus (Gsl ++ Gsr) (e_plus (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_plus (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H2.
    subst. apply sc_plus. apply IHex1; try easy. apply IHex2; try easy.
Qed.

Lemma slideS_helper : forall llp l k X m x0 x Gsl Gsr Gt tm,
    length Gsl = k ->
    Forall
          (fun Q : process =>
           forall (X m l k : fin) (tm : option sort) (Gsl Gsr : seq (option sort)) (Gt : ctxT) (T : ltt),
           typ_proc (Gsl ++ Gsr) Gt (incr_free l k X m Q) T ->
           length Gsl = k -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k X m.+1 Q) T) llp ->
    Forall2 (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gsl ++ Gsr) Gt u v.2)
           (list_map (incr_free l k.+1 X m) llp) (zip x0 x) ->
    Forall2 (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gsl ++ tm :: Gsr) Gt u v.2)
      (list_map (incr_free l k.+1 X m.+1) llp) (zip x0 x).
Proof.
  intro llp. induction llp; intros; try easy.
  - specialize(Forall2_length H1); intros. simpl in *.
    specialize(length_zero_iff_nil (zip x0 x)); intros. destruct H3.
    specialize(H3 (esym H2)). clear H2 H4. replace (zip x0 x) with (@nil (sort * ltt)). easy.
  - specialize(Forall2_length H1); intros. simpl in *.
    specialize(positive_list_length_dst_zip x0 x (length (list_map (incr_free l k.+1 X m) llp)) (esym H2)); intros.
    destruct H3. destruct H3. destruct H3. destruct H3. 
    replace (zip x0 x) with ((x1,x3) :: zip x2 x4) in *. clear H2 H3.
    specialize(Forall2_cons_iff (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gsl ++ Gsr) Gt u v.2) (incr_free l k.+1 X m a) (x1,x3) (list_map (incr_free l k.+1 X m) llp) (zip x2 x4)); intros.
    destruct H2. clear H3. specialize(H2 H1); intros. clear H1. destruct H2.
    specialize(Forall_cons_iff (fun Q : process =>
        forall (X m l k : fin) (tm : option sort) (Gsl Gsr : seq (option sort)) (Gt : ctxT) (T : ltt),
        typ_proc (Gsl ++ Gsr) Gt (incr_free l k X m Q) T ->
        length Gsl = k -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k X m.+1 Q) T) a llp); intros.
    destruct H3. specialize(H3 H0); intros. clear H4 H0. destruct H3.
    specialize(IHllp l k X m x2 x4 Gsl Gsr Gt tm H H3 H2); intros. 
    specialize(H0 X m l k.+1 tm (Some (x1, x3).1 :: Gsl) Gsr Gt (x1, x3).2); intros.
    apply Forall2_cons; try easy.
    apply H0; try easy. simpl.
    apply eq_S. easy.
Qed.

Lemma slideSp : forall Q X m l k tm Gsl Gsr Gt T,
typ_proc (Gsl ++ Gsr) Gt (incr_free l k X m Q) T -> length Gsl = k -> typ_proc (Gsl ++ [tm] ++ Gsr) Gt (incr_free l k X m.+1 Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(_a23_e (p_var (if l <= n then (n + X)%coq_nat else n)) (if l <= n then (n + X)%coq_nat else n) T (Gsl ++ Gsr) Gt H (erefl (p_var (if l <= n then (n + X)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    apply tc_sub with (t := x); try easy. 
    apply tc_var; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_f p_inact T (Gsl ++ Gsr) Gt H (erefl p_inact)); intros. subst.
    apply tc_inact.
  - simpl in *.
    specialize(_a23_bf pt lb (incr_freeE k m ex) (incr_free l k X m Q) (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)) (Gsl ++ Gsr) Gt T H (erefl (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q) ))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt [(lb, (x, x0))])); try easy.
    apply tc_send; try easy.
    apply slideSp_e; try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *.
    specialize(_a23_a pt llb (list_map (incr_free l k.+1 X m) llp) (p_recv pt llb (list_map (incr_free l k.+1 X m) llp)) (Gsl ++ Gsr) Gt T H0 (erefl (p_recv pt llb (list_map (incr_free l k.+1 X m) llp)))); intros.
    destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5. destruct H6.
    apply tc_sub with (t := (ltt_recv pt (zip llb (zip x0 x)))); try easy.
    specialize(eq_trans (esym H2) H3); intros.
    specialize(map_length (incr_free l k.+1 X m) llp); intros.
    specialize(map_length (incr_free l k.+1 X m.+1) llp); intros.
    specialize(eq_trans H4 H9); intros.
    specialize(eq_trans H11 (esym H10)); intros.
    specialize(eq_trans (esym H3) H12); intros.
    apply tc_recv; try easy. clear H2 H3 H4 H6 H8 H9 H10 H11 H12 H13.
    apply slideS_helper; try easy.
    specialize(typable_implies_wfC H0); intros; try easy.
  - simpl in *.
    specialize(_a23_c (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)) (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2) T (Gsl ++ Gsr) Gt H (erefl (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite; try easy.
    apply slideSp_e; try easy.
    apply tc_sub with (t := x); try easy. apply IHQ1; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
    apply tc_sub with (t := x0); try easy. apply IHQ2; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_d (p_rec (incr_free l.+1 k X m Q)) (incr_free l.+1 k X m Q) T (Gsl ++ Gsr) Gt H (erefl (p_rec (incr_free l.+1 k X m Q)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := x0); try easy.
    apply tc_mu with (t := x); try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H1); intros; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
Qed.

Lemma slideS : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc (tm :: Gs) Gt (incr_free 0 0 X m.+1 Q) T.
Proof.
  intros.
  specialize(slideSp Q X m 0 0 tm [] Gs Gt T H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma _a21_recv_helper : forall llp X m n Q T Gs Gt x x0 ys,
  wtyped Q ->
  onth X Gt = None ->
  typ_proc Gs Gt (incr_free 0 0 m n Q) T ->
  Forall
      (fun P : process =>
       forall (Q : process) (T T' : ltt) (Gs : ctxS) (Gt : ctxT) 
         (X : fin) (Q' : process) (m n : fin),
       wtyped Q ->
       typ_proc Gs (extendT X T Gt) P T' ->
       onth X Gt = None ->
       substitutionP X m n Q P Q' ->
       typ_proc Gs Gt (incr_free 0 0 m n Q) T -> typ_proc Gs Gt Q' T') llp ->
  Forall2
        (fun (u : process) (v : sort * ltt) =>
         typ_proc (Some v.1 :: Gs) (extendT X T Gt) u v.2) llp 
        (zip x0 x) ->
  Forall2 (substitutionP X m n.+1 Q) llp ys ->
  Forall2 (fun (u : process) (v : sort * ltt) => typ_proc (Some v.1 :: Gs) Gt u v.2) ys
  (zip x0 x).
Proof.
  intro llp. induction llp; intros; try easy.
  specialize(Forall2_length H3); intros. simpl in H5.
  specialize(Forall2_length H4); intros. simpl in H6.
  specialize(length_zero_iff_nil (zip x0 x)); intros. destruct H7. specialize(H7 (esym H5)); intros.
  specialize(length_zero_iff_nil ys); intros. destruct H9. specialize(H9 (esym H6)); intros.
  subst. replace (zip x0 x) with (@nil (sort * ltt)). easy.
  
  specialize(Forall2_length H3); intros. simpl in H5.
  specialize(positive_list_length_dst_zip x0 x (length llp) (esym H5)); intros.
  destruct H6. destruct H6. destruct H6. destruct H6.
  replace (zip x0 x) with ((x1, x3) :: zip x2 x4) in *. simpl in *.
  specialize(Forall2_length H4); intros. simpl in H7.
  specialize(positive_list_length_dst ys (length llp) (esym H7)); intros.
  destruct H8. destruct H8. subst. clear H5 H6 H7.
  specialize(Forall2_cons_iff (fun (u : process) (v : sort * ltt) =>
       typ_proc (Some v.1 :: Gs) (extendT X T Gt) u v.2) a (x1,x3) llp (zip x2 x4)); intros.
  destruct H5. specialize(H5 H3); intros. clear H6 H3. destruct H5.
  specialize(Forall2_cons_iff (substitutionP X m n.+1 Q) a x5 llp x6); intros.
  destruct H6. specialize(H6 H4); intros. clear H7 H4. destruct H6.
  specialize(Forall_cons_iff (fun P : process =>
        forall (Q : process) (T T' : ltt) (Gs : ctxS) (Gt : ctxT) 
          (X : fin) (Q' : process) (m n : fin),
        wtyped Q ->
        typ_proc Gs (extendT X T Gt) P T' ->
        onth X Gt = None ->
        substitutionP X m n Q P Q' ->
        typ_proc Gs Gt (incr_free 0 0 m n Q) T -> typ_proc Gs Gt Q' T') a llp); intros.
  destruct H7. specialize(H7 H2); intros. clear H8 H2. destruct H7.
  specialize(H2 Q T (x1, x3).2 (Some (x1, x3).1 :: Gs) Gt X x5 m n.+1 H H3 H0 H4); intros.
  specialize(IHllp X m n Q T Gs Gt x4 x2 x6 H H0 H1 H7 H5 H6); intros.
  apply Forall2_cons; try easy.
  apply H2.
  apply slideS; try easy.
Qed. 

Lemma _a21: forall P Q T T' Gs Gt X Q' m n, wtyped Q 
  -> typ_proc Gs (extendT X T Gt) P T' -> onth X Gt = None 
  -> substitutionP X m n Q P Q' -> typ_proc Gs Gt (incr_free 0 0 m n Q) T
  -> typ_proc Gs Gt Q' T'.
Proof. 

  intros P. induction P using process_ind_ref.
  
  (* var *)
  
  intros.
  inversion H2. subst.
  specialize(_a23_e (p_var n) n T' Gs (extendT n T Gt) H0 (erefl (p_var n))); intros.
  destruct H4. destruct H4.
  specialize(extend_extract n T Gt); intros.
  specialize(eq_trans (esym H4) H6); intros. inversion H7. subst.
  apply tc_sub with (t := T); intros; try easy.
  
  subst.
  specialize(typable_implies_wfC H0); intros; try easy. subst.
  specialize(_a23_e (p_var n) n T' Gs (extendT X T Gt) H0 (erefl (p_var n))); intros.
  destruct H4. destruct H4.
  apply tc_sub with (t := x); try easy.
  apply tc_var.
  apply ssrfun.esym. apply remove_var with (X := X) (T:= T); try easy. destruct H5. easy.
  specialize(typable_implies_wfC H0); intros; try easy.
  
  (* inact *)
  intros.
  inversion H2. subst.
  specialize(_a23_f p_inact T' Gs (extendT X T Gt) H0 (erefl p_inact)); intros. subst.
  apply tc_inact.
  
  (* send *)
  intros. 
  inversion H2. subst.
  specialize(_a23_bf pt lb ex P (p_send pt lb ex P) Gs (extendT X T Gt) T' H0 (erefl (p_send pt lb ex P))); intros. 
  destruct H4. destruct H4. destruct H4. destruct H5. 
  specialize(IHP Q T x0 Gs Gt X Q'0 m n H H5 H1 H13 H3); intros.
  apply tc_sub with (t := (ltt_send pt [(lb, (x, x0))])); try easy.
  apply tc_send; try easy.
  specialize(typable_implies_wfC H0); intros; try easy.
  
  (* recv *)
  intros.
  inversion H3. subst.
  specialize(_a23_a pt llb llp (p_recv pt llb llp) Gs (extendT X T Gt) T' H1 (erefl (p_recv pt llb llp))); intros.
  destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H9. destruct H10.
  apply tc_sub with (t := (ltt_recv pt (zip llb (zip x0 x)))); try easy.
  specialize(eq_trans (esym H5) H6); intros.
  specialize(eq_trans (esym H12) H13); intros.
  specialize(eq_trans H5 H13); intros.
  apply tc_recv; try easy.
  apply _a21_recv_helper with (llp := llp) (m := m) (n := n) (Q := Q) (X := X) (T := T); try easy.
  specialize(typable_implies_wfC H1); intros; try easy.
  
  (* ite *)
  intros. 
  inversion H2. subst.
  specialize(_a23_c (p_ite e P1 P2) e P1 P2 T' Gs (extendT X T Gt) H0 (erefl (p_ite e P1 P2))); intros.
  destruct H4. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. 
  specialize(IHP1 Q T x Gs Gt X Q1 m n H H4 H1 H12 H3); intros.
  specialize(IHP2 Q T x0 Gs Gt X Q2 m n H H5 H1 H13 H3); intros.
  apply tc_ite; intros; try easy.
  apply tc_sub with (t := x); intros; try easy.
  specialize(typable_implies_wfC H0); intros; try easy.
  apply tc_sub with (t := x0); intros; try easy.
  specialize(typable_implies_wfC H0); intros; try easy. 
    
  (* rec *)
  intros.
  inversion H2. subst.
  specialize(_a23_d (p_rec P) P T' Gs (extendT X T Gt) H0 (erefl (p_rec P))); intros.
  destruct H4. destruct H4. destruct H4. destruct H5.
  specialize(IHP Q T x0 Gs (Some x :: Gt) X.+1 Q'0 m.+1 n H H4 H1 H9); intros.
  apply tc_sub with (t := x0); try easy.
  apply tc_mu with (t := x); try easy.
  apply IHP.
  apply slideT; try easy.
  specialize(typable_implies_wfC H4); intros; try easy.
  specialize(typable_implies_wfC H0); intros; try easy. 
Qed.

Lemma Forall2_to_Forall {A B : Type} [P : A -> Prop] [P1 : list A] [P2 : list B] :
  Forall2 (fun u v => P u) P1 P2 -> Forall P P1.
Proof.
  revert P2.
  induction P1. easy.
  intros.
  specialize(Forall2_length H); intros.
  specialize(positive_list_length_dst P2 (length P1) (ssrfun.esym H0)); intros.
  destruct H1. destruct H1. subst.
  specialize(Forall2_cons_iff (fun (u : A) (_ : B) => P u) a x P1 x0); intros. destruct H1.
  specialize(H1 H); intros. clear H2. destruct H1.
  specialize(IHP1 x0 H2); intros.
  apply Forall_cons; try easy.
Qed.

Lemma typable_implies_wtyped [Gs : ctxS] [Gt : ctxT] [P : process] [T : ltt] : typ_proc Gs Gt P T -> wtyped P.
Proof.
  intros. induction H using typ_proc_ind_ref.
  apply wp_inact.
  apply wp_var.
  apply wp_rec. easy.
  apply wp_ite; try easy. easy.
  apply wp_recv; try easy. 
  - specialize(eq_trans H H0); intros; try easy. 
    apply (Forall2_to_Forall H3).
    apply wp_send. easy.
Qed.

Lemma trivial_incrE : forall n ex, (incr_freeE n 0 ex) = ex.
Proof.
  intros n ex. induction ex; intros; try easy.
  - simpl. destruct (n <= n0); try easy.
    specialize(Nat.add_0_r n0); intros. replace (n0 + 0)%coq_nat with n0. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
Qed.

Lemma trivial_incr : forall m n Q, (incr_free m n 0 0 Q) = Q.
Proof.
  intros. revert m n. induction Q using process_ind_ref; intros; simpl; try easy. 
  - destruct (m <= n); try easy.
    specialize(Nat.add_0_r n); intros. replace (n + 0)%coq_nat with n; easy.
  - specialize(trivial_incrE n ex); intros.
    specialize(IHQ m n); intros.
    replace (incr_freeE n 0 ex) with ex. replace (incr_free m n 0 0 Q) with Q. easy.
  - assert (list_map (incr_free m n.+1 0 0) llp = llp).
    {
      induction llp. easy.
      specialize(Forall_cons_iff (fun Q : process => forall m n : fin, incr_free m n 0 0 Q = Q) a llp); intros.
      destruct H0. specialize(H0 H); intros. clear H1 H. destruct H0.
      specialize(IHllp H0); intros.
      simpl.
      specialize(H m n.+1); intros.
      replace (incr_free m n.+1 0 0 a) with a.
      replace (list_map (incr_free m n.+1 0 0) llp) with llp. easy.
    }
    replace (list_map (incr_free m n.+1 0 0) llp) with llp. easy.
  - specialize(trivial_incrE n e); intros. 
    specialize(IHQ1 m n); intros. specialize(IHQ2 m n); intros.
    replace (incr_freeE n 0 e) with e.
    replace (incr_free m n 0 0 Q1) with Q1. 
    replace (incr_free m n 0 0 Q2) with Q2.
    easy.
  - specialize(IHQ m.+1 n); intros. 
    replace (incr_free m.+1 n 0 0 Q) with Q. easy.
Qed.

Lemma _a21f : forall P Q T T' Gs Gt X Q',
     typ_proc Gs (extendT X T Gt) P T' -> onth X Gt = None 
  -> substitutionP X 0 0 Q P Q' -> typ_proc Gs Gt Q T
  -> typ_proc Gs Gt Q' T'.
Proof.
  intros.
  apply _a21 with (P := P) (Q := Q) (T := T) (X := X) (m := 0) (n := 0); try easy.
  apply typable_implies_wtyped with (Gs := Gs) (Gt := Gt) (T := T). easy.
  specialize(trivial_incr 0 0 Q); intros. 
  replace (incr_free 0 0 0 0 Q) with Q. easy.
Qed.
