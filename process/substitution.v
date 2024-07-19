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
  intro n. induction n.
  intros t gt. revert t. induction gt.
  - intros. easy. intros. easy.
  - destruct Gt; try easy. simpl.
    - apply IHn.
    - simpl. apply IHn.
Qed.

Lemma positive_list_length_dst {A} : forall (xs : list A) n, length xs = S(n) -> exists y ys, y::ys = xs.
Proof.
  intros.
  induction xs. easy.
  exists a. exists xs. easy.
Qed.

Lemma SList_map {A} : forall (f : A -> A) lis,  
  SList (list_map (fun u => match u with
    | Some x => Some (f x)
    | None   => None
  end) lis) -> SList lis.
Proof.
  intros f lis. induction lis; intros; try easy. 
  destruct a; try easy. simpl. apply IHlis; try easy.
Qed.

Lemma SList_map2 {A} : forall (f : A -> A) lis, SList lis -> 
  SList (list_map (fun u => match u with
    | Some x => Some (f x)
    | None   => None
  end) lis).
Proof.
  intros f lis. induction lis; intros; try easy.
  destruct a; try easy. simpl. apply IHlis; try easy.
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

Lemma slideT_helper : forall llp Gs Gtl tm Gtr l X m k x,
    length Gtl = l ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (X m l k0 : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : seq (option ltt)) (T : ltt),
           typ_proc Gs (Gtl ++ Gtr) (incr_free l k0 X m k) T ->
           length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k0 X.+1 m k) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ Gtr) p t))
       (list_map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp) x ->
    Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ tm :: Gtr) p t))
      (list_map
         (fun u : option process =>
          match u with
          | Some p' => Some (incr_free l k.+1 X.+1 m p')
          | None => None
          end) llp) x.
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy.
    simpl in *.
    specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ Gtr) p t)) (match a with
        | Some p' => Some (incr_free l k.+1 X m p')
        | None => None
        end) o (list_map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) x); intros. destruct H2. clear H3. specialize(H2 H1). clear H1.
    destruct H2.
    specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (X m l k0 : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : seq (option ltt)) (T : ltt),
            typ_proc Gs (Gtl ++ Gtr) (incr_free l k0 X m k) T ->
            length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k0 X.+1 m k) T
        | None => True
        end) a llp); intros. destruct H3. clear H4. specialize(H3 H0). clear H0. destruct H3.
    apply Forall2_cons; try easy.
    - destruct a; try easy. destruct H1. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. destruct H4. subst.
      right. exists (incr_free (length Gtl) k.+1 X.+1 m p), x1, x2. split. easy. split. easy. 
      inversion H1. subst. apply H0; try easy.
    - destruct H1. destruct H1. subst. left. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. easy.
    apply IHllp; try easy.
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
    apply tc_sub with (t := (ltt_send pt (extendLTT lb [] (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply IHQ. easy. easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_a pt (list_map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) (p_recv pt
          (list_map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp)) Gs (Gtl ++ Gtr) T H0 (erefl (p_recv pt
          (list_map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp)))); intros.
    destruct H2. destruct H2. destruct H3. destruct H4. 
    apply tc_sub with (t := (ltt_recv pt x)); try easy. constructor.
    specialize(Forall2_length H4); intros.
    specialize(map_length (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp); intros.
    specialize(eq_trans (esym H6) H7); intros. clear H6 H7.
    apply eq_trans with (y := length llp); try easy. 
    apply map_length; try easy.
    apply SList_map2 with (f := (incr_free l k.+1 X.+1 m)); try easy.
    specialize(SList_map (incr_free l k.+1 X m) llp H5); intros. easy.
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

Lemma slideS_helper : forall llp l k X m x Gsl Gsr Gt tm,
    length Gsl = k ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (X m l k0 : fin) (tm : option sort) (Gsl Gsr : seq (option sort)) 
             (Gt : ctxT) (T : ltt),
           typ_proc (Gsl ++ Gsr) Gt (incr_free l k0 X m k) T ->
           length Gsl = k0 -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k0 X m.+1 k) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t))
       (list_map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp) x ->
    Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ tm :: Gsr) Gt p t))
      (list_map
         (fun u : option process =>
          match u with
          | Some p' => Some (incr_free l k.+1 X m.+1 p')
          | None => None
          end) llp) x.
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy.
    specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (X m l k0 : fin) (tm : option sort) (Gsl Gsr : seq (option sort)) 
              (Gt : ctxT) (T : ltt),
            typ_proc (Gsl ++ Gsr) Gt (incr_free l k0 X m k) T ->
            length Gsl = k0 -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k0 X m.+1 k) T
        | None => True
        end) a llp); intros. destruct H2. specialize(H2 H0). clear H0 H3. destruct H2.
    simpl in *.
    specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t)) (match a with
        | Some p' => Some (incr_free l k.+1 X m p')
        | None => None
        end) o (list_map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) x); intros.
    destruct H3. specialize(H3 H1). clear H1 H4. destruct H3.
    apply Forall2_cons; try easy.
    - destruct a; try easy. destruct H1. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. inversion H1. subst.
      right. destruct H4. subst. exists (incr_free l (length Gsl).+1 X m.+1 p), x1, x2.
      split. easy. split. easy. 
      specialize(H0 X m l (length Gsl).+1 tm (Some x1 :: Gsl) Gsr Gt x2 H4).
      simpl in H0. apply H0. easy.
    - destruct H1. destruct H1. subst. left; easy.
      destruct H1. destruct H1. destruct H1. destruct H1. easy.
    apply IHllp; try easy.
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
    apply tc_sub with (t := (ltt_send pt (extendLTT lb [] (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply slideSp_e; try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *.
    specialize(_a23_a pt (list_map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) (p_recv pt
       (list_map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp)) (Gsl ++ Gsr) Gt T H0 (erefl (p_recv pt
       (list_map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp)))); intros. 
    destruct H2. destruct H2. destruct H3. destruct H4. 
    apply tc_sub with (t := (ltt_recv pt x)); try easy. 
    constructor.
    specialize(Forall2_length H4); intros. 
    specialize(map_length (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp); intros. 
    specialize(eq_trans (esym H6) H7); intros.
    apply eq_trans with (y := length llp); try easy. apply map_length. clear H2.
    apply SList_map2; try easy.
    specialize(SList_map (incr_free l k.+1 X m) llp H5); intros; try easy.
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

Lemma _a21_recv_helper : forall llp X m n Q T Gs Gt x ys,
  wtyped Q ->
  onth X Gt = None ->
  typ_proc Gs Gt (incr_free 0 0 m n Q) T ->
  Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (Q : process) (T T' : ltt) (Gs : ctxS) (Gt : ctxT) (X : fin) 
             (Q' : process) (m n : fin),
           wtyped Q ->
           typ_proc Gs (extendT X T Gt) k T' ->
           onth X Gt = None ->
           substitutionP X m n Q k Q' -> typ_proc Gs Gt (incr_free 0 0 m n Q) T -> typ_proc Gs Gt Q' T'
       | None => True
       end) llp ->
  Forall2
        (fun u v : option process =>
         u = None /\ v = None \/
         (exists k l : process, u = Some k /\ v = Some l /\ substitutionP X m n.+1 Q k l)) llp ys ->
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (extendT X T Gt) p t)) llp x ->
  Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) Gt p t)) ys x. 
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct ys; try easy. destruct x; try easy.
  - destruct ys; try easy. destruct x; try easy.
  specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (Q : process) (T T' : ltt) (Gs : ctxS) (Gt : ctxT) (X : fin) 
              (Q' : process) (m n : fin),
            wtyped Q ->
            typ_proc Gs (extendT X T Gt) k T' ->
            onth X Gt = None ->
            substitutionP X m n Q k Q' -> typ_proc Gs Gt (incr_free 0 0 m n Q) T -> typ_proc Gs Gt Q' T'
        | None => True
        end) a llp); intros. destruct H5. specialize(H5 H2). clear H2 H6. destruct H5.
  specialize(Forall2_cons_iff (fun u v : option process =>
        u = None /\ v = None \/
        (exists k l : process, u = Some k /\ v = Some l /\ substitutionP X m n.+1 Q k l)) a o llp ys); intros.
  destruct H6. specialize(H6 H3). clear H3 H7. destruct H6.
  specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (extendT X T Gt) p t)) a o0 llp x); intros.
  destruct H7. specialize(H7 H4). clear H4 H8. destruct H7.
  apply Forall2_cons; try easy.
  - destruct H3. destruct H3. subst.
    - destruct H4. destruct H3. subst. left. easy.
    - destruct H3. destruct H3. destruct H3. destruct H3. easy.
  - destruct H3. destruct H3. destruct H3. destruct H8. subst. right.
    - destruct H4. destruct H3. easy.
    - destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. subst.
      exists x1, x3, x4. split. easy. split. easy. inversion H3. subst.
      apply H2 with (Q := Q) (T := T) (X := X) (m := m) (n := n.+1); try easy.
      apply slideS. easy.
  apply IHllp with (X := X) (m := m) (n := n) (Q := Q) (T := T); try easy.
Qed.

Lemma SList_Forall2_a21 : forall llp ys X m n Q,
  SList llp -> 
  Forall2
        (fun u v : option process =>
         u = None /\ v = None \/
         (exists k l : process, u = Some k /\ v = Some l /\ substitutionP X m n.+1 Q k l)) llp ys ->
  SList ys.
Proof.
  intro llp. induction llp; intros; try easy.
  destruct ys; try easy.
  specialize(Forall2_cons_iff (fun u v : option process =>
        u = None /\ v = None \/
        (exists k l : process, u = Some k /\ v = Some l /\ substitutionP X m n.+1 Q k l)) a o llp ys); intros.
  destruct H1. specialize(H1 H0). clear H0 H2.
  destruct H1.
  destruct o; try easy. simpl.
  apply IHllp with (X := X) (m := m) (n := n) (Q := Q); try easy.
  destruct a; try easy.
  destruct H0. destruct H0. easy. destruct H0. destruct H0. destruct H0. destruct H2. easy.
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
  apply tc_sub with (t := (ltt_send pt (extendLTT lb [] (Some (x, x0))))); try easy.
  apply tc_send; try easy.
  specialize(typable_implies_wfC H0); intros; try easy.
  
  (* recv *)
  intros.
  inversion H3. subst.
  specialize(_a23_a pt llp (p_recv pt llp) Gs (extendT X T Gt) T' H1 (erefl (p_recv pt llp))); intros.
  destruct H5. destruct H5. destruct H6. destruct H7.
  apply tc_sub with (t := (ltt_recv pt x)); try easy. constructor.
  specialize(Forall2_length H12); intros; try easy.
  specialize(Forall2_length H7); intros.
  apply eq_trans with (y := length llp); try easy.
  inversion H3. subst.
  apply SList_Forall2_a21 with (llp := llp) (X := X) (m := m) (n := n) (Q := Q); try easy.
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

Lemma typable_implies_wtyped_helper : forall Pr STT,
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wtyped p)) Pr STT ->
  Forall (fun u : option process => u = None \/ (exists k : process, u = Some k /\ wtyped k)) Pr.
Proof.
  intro Pr. induction Pr; intros; try easy.
  destruct STT; try easy.
  specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wtyped p)) a o Pr STT); intros.
  destruct H0. specialize(H0 H). clear H H1. destruct H0.
  apply Forall_cons; try easy.
  destruct H.
  - destruct H. subst. left. easy.
  - destruct H. destruct H. destruct H. destruct H. destruct H1. subst.
    right. exists x. easy.
  apply IHPr with (STT := STT); try easy.
Qed.

Lemma typable_implies_wtyped [Gs : ctxS] [Gt : ctxT] [P : process] [T : ltt] : typ_proc Gs Gt P T -> wtyped P.
Proof.
  intros. induction H using typ_proc_ind_ref.
  apply wp_inact.
  apply wp_var.
  apply wp_rec. easy.
  apply wp_ite; try easy. easy.
  apply wp_recv; try easy. 
  - apply typable_implies_wtyped_helper with (STT := STT); try easy.
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
  - assert (list_map (fun u => match u with 
        | Some u => Some (incr_free m n.+1 0 0 u)
        | None   => None
      end) llp = llp).
    {
      induction llp. easy. simpl in *.
      specialize(Forall_cons_iff (fun u : option process =>
       match u with
       | Some k => forall m n : fin, incr_free m n 0 0 k = k
       | None => True
       end) a llp); intros.
      destruct H0. specialize(H0 H); intros. clear H1 H. destruct H0.
      specialize(IHllp H0); intros.
      simpl.
      destruct a; try easy. 
      specialize(H m n.+1). replace (incr_free m n.+1 0 0 p) with p. 
      replace (list_map
     (fun u : option process =>
      match u with
      | Some u0 => Some (incr_free m n.+1 0 0 u0)
      | None => None
      end) llp) with llp. easy.
      replace (list_map
     (fun u : option process =>
      match u with
      | Some u0 => Some (incr_free m n.+1 0 0 u0)
      | None => None
      end) llp) with llp. easy.
    }
    replace (list_map (fun u : option process =>
        match u with
        | Some u0 => Some (incr_free m n.+1 0 0 u0)
        | None => None
        end) llp) with llp. easy.
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

