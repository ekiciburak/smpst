From SST Require Export src.unscoped src.expressions process.processes process.substitution process.inversion process.typecheck type.global type.local tree.global tree.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Inductive session: Type :=
  | s_ind : part   -> process -> session
  | s_par : session -> session -> session.
  
Notation "p '<--' P"   :=  (s_ind p P) (at level 50, no associativity).
Notation "s1 '|||' s2" :=  (s_par s1 s2) (at level 50, no associativity).
  
(* Inductive sForall (P: session -> Prop) : session -> Prop :=
  | fsind: forall p proc, sForall P (p <-- proc)
  | fspar: forall (S R: session), P S -> P R -> sForall P (S ||| R).
 *)
 
Print Forall.

Inductive ForallT (P : part -> process -> Prop) : session -> Prop := 
  | ForallT_mono : forall pt op, P pt op -> ForallT P (pt <-- op)
  | ForallT_par : forall (M1 M2 : session), ForallT P M1 -> ForallT P M2 -> ForallT P (M1 ||| M2). 
  

Fixpoint InT (pt : part) (M : session) : Prop :=
  match M with 
    | p <-- _ => p = pt 
    | M1 |||  M2 => (InT pt M1) \/ (InT pt M2)
  end.

Inductive typ_sess : session -> gtt -> Prop := 
  | t_sess : forall M G, (forall pt, isgPartsC pt G -> InT pt M) ->
                         ForallT (fun u P => exists T, projectionC G u T /\ typ_proc nil nil P T) M ->
                         typ_sess M G.

Lemma _a23_2 : forall M G, typ_sess M G -> (forall pt, isgPartsC pt G -> InT pt M) /\ 
               ForallT (fun u P => exists T, projectionC G u T /\ typ_proc nil nil P T) M.
Proof.
  intros. inversion H; try easy.
Qed.

(* not done *)
Inductive stepE : relation expr := 
  | ec_var   : forall n, stepE (e_var n) (e_var n)
  | ec_val   : forall v, stepE (e_val v) (e_val v)
  | ec_succ  : forall n, stepE (e_succ (e_val (vint n))) (e_val (vint (n+1))).
   
Inductive scongP : relation process := 
  | pc_inact : scongP p_inact p_inact
  | pc_var   : forall n, scongP (p_var n) (p_var n)
  | pc_mu    : forall X Y, scongP X Y -> scongP (p_rec X) (p_rec Y)
  | pc_ite   : forall e e' X X' Y Y', stepE e e' -> scongP X X' -> scongP Y Y' -> scongP (p_ite e X Y) (p_ite e' X' Y')
  | pc_recv  : forall pt xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists P Q, u = Some P /\ v = Some Q /\ scongP P Q)) xs ys -> scongP (p_recv pt xs) (p_recv pt ys)
  | pc_send  : forall pt lb e e' X X', stepE e e' -> scongP X X' -> scongP (p_send pt lb e X) (p_send pt lb e' X')
  | pc_sub   : forall P Q, substitutionP 0 0 0 (p_rec P) P Q -> scongP (p_rec P) Q
  | pc_trans : forall P Q R, scongP P Q -> scongP Q R -> scongP P R.

Section scongP_ind_ref.
  Variable P : process -> process -> Prop.
  Hypothesis P_inact : P p_inact p_inact.
  Hypothesis P_var   : forall n, P (p_var n) (p_var n).
  Hypothesis P_mu    : forall X Y, P X Y -> P (p_rec X) (p_rec Y).
  Hypothesis P_ite   : forall e e' X X' Y Y', stepE e e' -> P X X' -> P Y Y' -> P (p_ite e X Y) (p_ite e' X' Y').
  Hypothesis P_recv  : forall pt xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists X Y, u = Some X /\ v = Some Y /\ P X Y)) xs ys -> P (p_recv pt xs) (p_recv pt ys).
  Hypothesis P_send  : forall pt lb e e' X X', stepE e e' -> P X X' -> P (p_send pt lb e X) (p_send pt lb e' X').
  Hypothesis P_sub   : forall X Y, substitutionP 0 0 0 (p_rec X) X Y -> P (p_rec X) Y.
  Hypothesis P_trans : forall X Y Z, P X Y -> P Y Z -> P X Z.
  
  Fixpoint scongP_ind_ref (X Y : process) (a : scongP X Y) {struct a} : P X Y.
  Proof.
    refine (match a with
      | pc_inact => P_inact
      | pc_var n => P_var n 
      | pc_mu X Y Hp => P_mu X Y (scongP_ind_ref X Y Hp)
      | pc_ite e e' X X' Y Y' He Hx Hy => P_ite e e' X X' Y Y' He (scongP_ind_ref X X' Hx) (scongP_ind_ref Y Y' Hy)
      | pc_recv pt xs ys Ha => P_recv pt xs ys _
      | pc_send pt lb e e' X X' He Hx => P_send pt lb e e' X X' He (scongP_ind_ref X X' Hx)
      | pc_sub X Y Hs => P_sub X Y Hs
      | pc_trans X Y Z Hxy Hyz => P_trans X Y Z (scongP_ind_ref X Y Hxy) (scongP_ind_ref Y Z Hyz)
    end); try easy.
    revert Ha. apply Forall2_mono. intros.
    destruct H. left. easy.
    destruct H. destruct H. destruct H. destruct H0. subst. right.
    exists x0. exists x1. split; try easy. split; try easy.
    apply scongP_ind_ref; try easy.
  Qed.
End scongP_ind_ref.

Inductive scong: relation session :=
  | sc_multi: forall p P Q M, scongP P Q -> scong (p <-- P ||| M) (p <-- Q ||| M) 
  | sc_par1 : forall p M, scong (p <-- p_inact ||| M) M
  | sc_par2 : forall M M', scong (M ||| M') (M' ||| M)
  | sc_par3 : forall M M' M'', scong ((M ||| M') ||| M'') (M ||| (M' ||| M'')).

Lemma _a22_2_helper : forall pt G, isgPartsC pt G -> projectionC G pt ltt_end -> False.
Admitted.

Lemma expr_typ_cong : forall Gs e e' S, typ_expr Gs e S -> stepE e e' -> typ_expr Gs e' S.
Proof.
Admitted.

Lemma _a22_2_helperP_1 : forall xs x l' Gs Gt,
      Forall2
       (fun u v : option process =>
        u = None /\ v = None \/
        (exists X Y : process,
           u = Some X /\
           v = Some Y /\
           (forall (Gs : ctxS) (Gt : ctxT) (T : ltt), typ_proc Gs Gt X T -> typ_proc Gs Gt Y T))) xs l' ->
      Forall2
        (fun (u : option process) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) Gt p t)) xs x ->
      Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) Gt p t)) l' x.
Proof.
  intro xs. induction xs; intros; try easy.
  inversion H. subst. inversion H0. subst. easy.
  inversion H. subst. inversion H0. subst. clear H H0.
  constructor. destruct H3. left. destruct H4; try easy.
  destruct H. destruct H0. destruct H0. destruct H0. destruct H0. subst. easy.
  right. destruct H. destruct H. destruct H. destruct H0. subst.
  exists x0. destruct H4. easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
  exists x2. exists x3. split; try easy. split; try easy.
  apply H1. inversion H. subst. easy.
  apply IHxs; try easy.
Qed.

Lemma _a22_2_helperP_2 : forall xs l',
      SList xs ->
      Forall2
       (fun u v : option process =>
        u = None /\ v = None \/
        (exists X Y : process,
           u = Some X /\
           v = Some Y /\
           (forall (Gs : ctxS) (Gt : ctxT) (T : ltt), typ_proc Gs Gt X T -> typ_proc Gs Gt Y T))) xs l' ->
      SList l'.
Proof.
  intro xs. induction xs; intros; try easy.
  inversion H0. subst. 
  specialize(SList_f a xs H); intros. destruct H1.
  - apply SList_b. apply IHxs; try easy.
  - destruct H1. destruct H2. subst. inversion H5. subst. destruct H3; try easy.
    destruct H1. destruct H1. destruct H1. destruct H2. subst. easy.
Qed.
  
Lemma _a22_2_helperP_h : forall Gs Gt pt xs ys T,
    typ_proc Gs Gt (p_recv pt xs) T ->
    Forall2
      (fun u v : option process =>
       u = None /\ v = None \/
       (exists X Y : process,
          u = Some X /\
          v = Some Y /\
          (forall (Gs : ctxS) (Gt : ctxT) (T : ltt), typ_proc Gs Gt X T -> typ_proc Gs Gt Y T))) xs ys ->
    typ_proc Gs Gt (p_recv pt ys) T.
Proof.
  intros Gs Gt pt xs. revert Gs Gt pt.
  induction xs; intros; try easy.
  - inversion H0. subst. easy.
  - inversion H0. subst. clear H0.
    specialize(_a23_a pt (a :: xs) (p_recv pt (a :: xs)) Gs Gt T H (eq_refl (p_recv pt (a :: xs)))); intros.
    destruct H0. destruct H0. destruct H1. destruct H2.
    apply tc_sub with (t := ltt_recv pt x); try easy.
    destruct x; try easy.
    apply tc_recv; try easy.
    simpl. apply eq_S.
    inversion H0.
    specialize(Forall2_length H5); intros. easy.
    specialize(SList_f a xs H4); intros. clear H4. destruct H6.
    - apply SList_b.
      apply _a22_2_helperP_2 with (xs := xs); try easy.
    - destruct H4. destruct H6. subst. destruct H3; try easy.
      destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
      inversion H5. subst. easy.
    - constructor. 
      destruct H3. left. destruct H3. inversion H2. subst.
      destruct H10. easy. destruct H3. destruct H3. destruct H3. easy.
      right.
      destruct H3. destruct H3. destruct H3. destruct H6. 
      exists x1.
      inversion H2; subst. destruct H11; try easy.
      destruct H3. destruct H3. destruct H3. destruct H3. destruct H6. subst.
      exists x3. exists x4.
      split; try easy. split; try easy. 
      apply H7. inversion H3. subst. easy.
    - inversion H2. subst. clear H2.
      apply _a22_2_helperP_1 with (xs := xs); try easy.
      apply typable_implies_wfC with (P := (p_recv pt (a :: xs))) (Gs := Gs) (Gt := Gt); try easy.
Qed.

Lemma _a22_2_helperP : forall Gs Gt P Q T, typ_proc Gs Gt P T -> scongP P Q -> typ_proc Gs Gt Q T.
Proof.
  intros. revert H. revert Gs Gt T.
  induction H0 using scongP_ind_ref; intros; try easy.
  - specialize(_a23_d (p_rec X) X T Gs Gt H (eq_refl (p_rec X))); intros.
    destruct H0. destruct H0. 
    specialize(IHscongP Gs (Some x :: Gt) x H0).
    apply tc_sub with (t := x); try easy.
    apply tc_mu; try easy.
    apply typable_implies_wfC with (P := p_rec X) (Gs := Gs) (Gt := Gt); try easy.
  - specialize(_a23_c (p_ite e X Y) e X Y T Gs Gt H0 (eq_refl (p_ite e X Y))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite.
    apply expr_typ_cong with (e := e); try easy.
    apply IHscongP; try easy. apply tc_sub with (t := x); try easy.
    apply typable_implies_wfC with (P := p_ite e X Y) (Gs := Gs) (Gt := Gt); try easy.
    apply IHscongP0; try easy. apply tc_sub with (t := x0); try easy.
    apply typable_implies_wfC with (P := p_ite e X Y) (Gs := Gs) (Gt := Gt); try easy.
  - apply _a22_2_helperP_h with (xs := xs); try easy.
  - specialize(_a23_bf pt lb e X (p_send pt lb e X) Gs Gt T H0 (eq_refl (p_send pt lb e X))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt (extendLTT lb nil (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply expr_typ_cong with (e := e); try easy.
    apply IHscongP; try easy.
    apply typable_implies_wfC with (P := p_send pt lb e X) (Gs := Gs) (Gt := Gt). easy.
  - specialize(_a23_d (p_rec X) X T Gs Gt H0 (eq_refl (p_rec X))); intros.
    destruct H1. destruct H1.  
    specialize(_a21f X (p_rec X)); intros.
    apply tc_sub with (t := x); intros; try easy.
    apply H3 with (T := x); try easy.
    apply tc_mu; intros; try easy.
    apply typable_implies_wfC with (P := p_rec X) (Gs := Gs) (Gt := Gt); try easy.
  - apply IHscongP0; try easy. apply IHscongP; try easy.
Qed.


Lemma _a22_2 : forall M M' G, typ_sess M G -> scong M M' -> typ_sess M' G.
Proof.
  intros. revert H. revert G. induction H0; intros; try easy.
  - inversion H0. subst. inversion H2. subst. clear H2.
    inversion H5. subst. clear H5. destruct H3. destruct H2.
    constructor; try easy. constructor; try easy. constructor; try easy. 
    exists x. split; try easy.
    apply _a22_2_helperP with (P := P); try easy.
  - inversion H. subst. inversion H1. subst. clear H1. 
    constructor; try easy.
    intros. specialize(H0 pt H1).
    simpl in H0. destruct H0; try easy. subst. 
    inversion H4. subst. destruct H2. destruct H0.
    specialize(_a23_f p_inact x nil nil H2 (eq_refl p_inact)); intros. subst. clear H4 H5 H2.
    specialize(_a22_2_helper pt G H1 H0); intros. easy.
  - inversion H; subst. inversion H1; subst. constructor.
    intros. specialize (H0 pt H2); intros. simpl. 
    destruct H0; try easy. right. easy. left. easy.
    constructor; try easy.
  - inversion H; subst. inversion H1; subst. inversion H4; subst. clear H1 H4.
    constructor. 
    - intros. specialize(H0 pt H1). simpl in *. 
      destruct H0. destruct H0. left. easy. 
      right. left. easy.
      right. right. easy.
    constructor; try easy. constructor; try easy.
Qed.



(* Declare Instance Equivalence_pcong : Equivalence scongP. 
Declare Instance Equivalence_scong : Equivalence scong.

Inductive sForall (P: session -> Prop): session -> Prop :=
  | fsind: forall p proc, sForall P (p <-- proc)
  | fspar: forall (S R: session), P S -> P R -> sForall P (S ||| R).
 *)