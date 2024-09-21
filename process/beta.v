From SST Require Export src.expressions process.processes process.sessions process.substitution.
Require Import List String Relations ZArith.
Require Import Setoid Morphisms Coq.Program.Basics.
Import ListNotations.
Require Import Coq.Init.Datatypes.


(* substitute e into e_var n of e1, depth d *)
Fixpoint subst_expr (n d : fin) (e : expr) (e1 : expr) : expr :=
  match e1 with 
    | e_var 0     => if Nat.eqb n 0 then (incr_freeE 0 d e) else e_var 0
    | e_var (S m) => if Nat.eqb (S m) n then (incr_freeE 0 d e) else 
                     if Nat.ltb (S m) n then e_var (S m) else e_var m 
    | e_succ e' => e_succ (subst_expr n d e e')
    | e_neg e' => e_neg (subst_expr n d e e')
    | e_not e' => e_not (subst_expr n d e e')
    | e_gt e' e'' => e_gt (subst_expr n d e e') (subst_expr n d e e'')
    | e_plus e' e'' => e_plus (subst_expr n d e e') (subst_expr n d e e'')
    | e_det e' e'' => e_det (subst_expr n d e e') (subst_expr n d e e'')
    | _ => e1
  end.
  
(* For a choice function, substitutes expr to e_var n (decr vars above n), d keeps track of depth of recv return process continuation
 *)
 
Fixpoint subst_expr_proc (p : process) (e : expr) (n d : fin) : process :=
  match p with 
    | p_send pt l e' P => p_send pt l (subst_expr n d e e') (subst_expr_proc P e n d)
    | p_ite e' P Q     => p_ite (subst_expr n d e e') (subst_expr_proc P e n d) (subst_expr_proc Q e n d)
    | p_recv pt lst    => p_recv pt (map (fun x => match x with
                                                | None => None
                                                | Some y => Some (subst_expr_proc y e (S n) (S d))
                                               end) lst)
    | p_rec P          => p_rec (subst_expr_proc P e n d)
    | _ => p
  end.


Inductive betaP: relation session :=
  | r_comm  : forall p q xs y l e v Q M, 
              onth l xs = Some y -> stepE_multi e v -> 
              betaP ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)) ||| M)
                    ((p <-- subst_expr_proc y v 0 0) ||| (q <-- Q) ||| M)
  | rt_ite  : forall p e P Q M,
              stepE_multi e (e_val (vbool true)) ->
              betaP ((p <-- (p_ite e P Q)) ||| M) ((p <-- P) ||| M)
  | rf_ite  : forall p e P Q M,
              stepE_multi e (e_val (vbool false)) ->
              betaP ((p <-- (p_ite e P Q)) ||| M) ((p <-- Q) ||| M)
  | r_struct: forall M1 M1' M2 M2', scong M1 M1' -> scong M2' M2 -> betaP M1' M2' -> betaP M1 M2.

Definition beta_multistep := multi betaP.

Lemma onth_sless {X} : forall n (Gsl Gsr : list (option X)) x0 S,
      n < length Gsl ->
      onth n (Gsl ++ Some S :: Gsr) = Some x0 ->
      onth n (Gsl ++ Gsr) = Some x0.
Proof.
  intro n. induction n; intros; try easy.
  - destruct Gsl; try easy.
  - destruct Gsl; try easy. apply IHn with (S := S); try easy.
  apply PeanoNat.lt_S_n; try easy.
Qed.

Lemma onth_smore {X} : forall n (Gsl Gsr : list (option X)) x0 o S,
      n <> length Gsl ->
      length Gsl <= n ->
      Some x0 = onth n (Gsl ++ Some S :: Gsr) ->
      Some x0 = onth n (o :: Gsl ++ Gsr).
Proof.
  intro n. induction n; intros; try easy.
  destruct Gsl; try easy.
  simpl in *. destruct Gsl; try easy.
  apply IHn with (S := S); try easy. simpl in *.
  specialize(Nat.succ_inj_wd_neg n (length Gsl)); intros. destruct H2. specialize(H2 H). easy.
  apply le_S_n; try easy.
Qed.

Lemma expr_subst : forall v ex x d Gsl Gsr S,
        typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
        typ_expr (Gsl ++ Some S :: Gsr) ex x ->
        typ_expr (Gsl ++ Gsr) (subst_expr (length Gsl) d v ex) x.
Proof.
  intros v ex. revert v.
  induction ex; intros; try easy.
  - simpl in *.
    specialize(inv_expr_var (e_var n) n (Gsl ++ Some S :: Gsr) x H0 (eq_refl (e_var n))); intros.
    destruct H1. destruct H1. 
    apply sc_sub with (s := x0); try easy.
    - destruct n; try easy.
      case_eq (Nat.eqb (length Gsl) 0); intros; try easy.
      destruct Gsl; try easy. simpl in *. inversion H1. subst. easy.
    - destruct Gsl; try easy. constructor; try easy.
    destruct Gsl.
    - simpl in *. constructor; try easy.
    - simpl in *.
      case_eq (Nat.eqb n (length Gsl)); intros.
      - specialize(onth_exact Gsl Gsr (Some S)); intros.
        specialize(natb_to_prop n (length Gsl) H3); intros. subst.
        specialize(eq_trans (eq_sym H1) H4); intros. inversion H5. subst. easy.
      case_eq (Datatypes.S n <? Datatypes.S (length Gsl))%nat; intros.
      - specialize(Nat.ltb_lt (Datatypes.S n) (Datatypes.S (length Gsl))); intros.
        destruct H5. specialize(H5 H4). clear H4 H6.
        constructor.
        apply eq_sym. apply onth_sless with (S := S); try easy.
        apply PeanoNat.lt_S_n. easy.
      - specialize(Nat.ltb_ge(Datatypes.S n) (Datatypes.S (length Gsl))); intros.
        destruct H5. specialize(H5 H4). clear H4 H6.
        constructor.
        apply onth_smore with (S := S); try easy.
        apply natb_to_propf. easy.
        apply le_S_n. easy.
  - simpl in *.
    specialize(inv_expr_vali (Gsl ++ Some S :: Gsr) (e_val v) x v H0 (eq_refl (e_val v))); intros.
    destruct H1.
    - destruct H1. destruct H1. subst. apply sc_vali.
    - destruct H1. destruct H1. destruct H1. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
    - destruct H1. destruct H1. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ (Gsl ++ Some S :: Gsr) (e_succ ex) x ex H0 (eq_refl (e_succ ex))); intros.
    destruct H1. destruct H2.
    - subst. apply sc_succ. apply IHex with (S := S); try easy.
    - subst. apply sc_sub with (s := snat); try easy. apply sc_succ. apply IHex with (S := S); try easy.
      apply sni.
  - simpl in *.
    specialize(inv_expr_neg (Gsl ++ Some S :: Gsr) (e_neg ex) x ex H0 (eq_refl (e_neg ex))); intros.
    destruct H1. subst. constructor. apply IHex with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_not (Gsl ++ Some S :: Gsr) (e_not ex) x ex H0 (eq_refl (e_not ex))); intros.
    destruct H1. subst. constructor. apply IHex with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_gt (Gsl ++ Some S :: Gsr) (e_gt ex1 ex2) x ex1 ex2 H0 (eq_refl (e_gt ex1 ex2))); intros.
    destruct H1. destruct H2. subst.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_plus (Gsl ++ Some S :: Gsr) (e_plus ex1 ex2) x ex1 ex2 H0 (eq_refl (e_plus ex1 ex2))); intros.
    destruct H1. destruct H2. subst.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_det (Gsl ++ Some S :: Gsr) (e_det ex1 ex2) x ex1 ex2 H0 (eq_refl (e_det ex1 ex2))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x0); try easy.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
Qed.

Lemma SList_map_a24 {A} : forall (llp : list (option process)) v d (Gsl : list A),
  SList llp ->
  SList
  (map
     (fun x0 : option process =>
      match x0 with
      | Some y =>
          Some
            (subst_expr_proc y v (Datatypes.S (length Gsl)) (Datatypes.S d))
      | None => None
      end) llp).
Proof.
  intro llp. induction llp; intros; try easy.
  specialize(SList_f a llp H); intros. destruct H0; subst; try easy.
  apply SList_b. apply IHllp; try easy.
  destruct H0. destruct H1. subst. easy.
Qed.

Lemma slideE : forall v Gs d S x0,
               typ_expr Gs (incr_freeE 0 d v) S ->
               typ_expr (Some x0 ::Gs) (incr_freeE 0 (Datatypes.S d) v) S.
Proof.
  intro v. induction v; intros; try easy.
  - simpl in H.
    specialize(inv_expr_var (e_var (n + d)) (n + d) Gs S H (eq_refl (e_var (n + d)))); intros.
    destruct H0. destruct H0. apply sc_sub with (s := x); try easy.
    constructor. simpl.
    specialize(Nat.add_succ_r n d); intros.
    replace (n + Datatypes.S d) with (Datatypes.S (n + d)). simpl. easy.
  - simpl in *.
    specialize(inv_expr_vali Gs (e_val v) S v H (eq_refl (e_val v))); intros.
    - destruct H0. destruct H0. destruct H0. subst. apply sc_vali.
    - destruct H0. destruct H0. destruct H0. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
    - destruct H0. destruct H0. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ Gs (e_succ (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (eq_refl (e_succ (incr_freeE 0 d v)))); intros.
    destruct H0. destruct H1. subst. constructor. apply IHv; try easy.
    subst. apply sc_sub with (s := snat). constructor. apply IHv; try easy. apply sni.
  - simpl in *.
    specialize(inv_expr_neg Gs (e_neg (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (eq_refl (e_neg (incr_freeE 0 d v)))); intros.
    destruct H0. subst. constructor. apply IHv; try easy.
  - simpl in *.
    specialize(inv_expr_not Gs (e_not (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (eq_refl (e_not (incr_freeE 0 d v)))); intros.
    destruct H0. subst. constructor. apply IHv; try easy.
  - simpl in *.
    specialize(inv_expr_gt Gs (e_gt (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (eq_refl (e_gt (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. subst. constructor. apply IHv1; try easy. apply IHv2; try easy.
  - simpl in *.
    specialize(inv_expr_plus Gs (e_plus (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (eq_refl (e_plus (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. subst. constructor. apply IHv1; try easy. apply IHv2; try easy.
  - simpl in *.
    specialize(inv_expr_det Gs (e_det (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (eq_refl (e_det (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. destruct H0. destruct H1.
    apply sc_sub with (s := x); try easy. constructor. apply IHv1; try easy. apply IHv2; try easy.
Qed.


Lemma _a24_helper_recv : forall llp Gsl Gsr Gt d v x S,
    typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (v : expr) (d : fin) (Gsl Gsr : list (option sort)) (Gt : ctxT) (S : sort) (T : ltt),
           typ_proc (Gsl ++ Some S :: Gsr) Gt k T ->
           typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
           typ_proc (Gsl ++ Gsr) Gt (subst_expr_proc k v (length Gsl) d) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Some S :: Gsr) Gt p t)) llp x ->
    Forall2
        (fun (u : option process) (v0 : option (sort * ltt)) =>
         u = None /\ v0 = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\ v0 = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t))
        (map
           (fun x0 : option process =>
            match x0 with
            | Some y =>
                Some
                  (subst_expr_proc y v (Datatypes.S (length Gsl)) (Datatypes.S d))
            | None => None
            end) llp) x.
Proof.
  intro llp.
  induction llp; intros; try easy.
  inversion H1; subst. easy.
  inversion H1; subst. clear H1. 
  constructor. 
  destruct a; try easy.
  - right. destruct H4; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. 
    inversion H1. subst.
    exists (subst_expr_proc x v (Datatypes.S (length Gsl)) (Datatypes.S d)).
    exists x0. exists x1. split; try easy. split; try easy. clear H1.
    inversion H0; subst. clear H0.
    specialize(H4 v (Datatypes.S d) (Some x0 :: Gsl) Gsr Gt S x1).
    apply H4; try easy.
    apply slideE; try easy.
  - left. split; try easy.
    destruct H4; try easy. destruct H1. destruct H1. destruct H1. easy.
  - apply IHllp with (S := S); try easy.
    inversion H0; subst. easy.
Qed.

Lemma _a24_helper : forall v d P Gsl Gsr Gt S T, 
        typ_proc (Gsl ++ Some S :: Gsr) Gt P T -> 
        typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S -> 
        typ_proc (Gsl ++ Gsr) Gt (subst_expr_proc P v (length Gsl) d) T.
Proof.
  intros v d P. revert v d.
  induction P using process_ind_ref; intros; try easy.
  - specialize(_a23_e (p_var n) n T (Gsl ++ Some S :: Gsr) Gt H (eq_refl (p_var n))); intros.
    destruct H1. destruct H1. destruct H2.
    simpl. apply tc_sub with (t := x); intros; try easy.
    constructor; try easy.
    specialize(typable_implies_wfC H); easy.
  - specialize(_a23_f p_inact T (Gsl ++ Some S :: Gsr) Gt H (eq_refl (p_inact))); intros.
    subst. simpl. constructor.
  - simpl.
    specialize(_a23_bf pt lb ex P (p_send pt lb ex P) (Gsl ++ Some S :: Gsr) Gt T H (eq_refl (p_send pt lb ex P))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. 
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); intros; try easy.
    constructor; try easy.
    apply expr_subst with (S := S); try easy.
    apply IHP with (S := S); try easy.
    specialize(typable_implies_wfC H); try easy.
  - specialize(_a23_a pt llp (p_recv pt llp) (Gsl ++ Some S :: Gsr) Gt T H0 (eq_refl (p_recv pt llp))); intros.
    destruct H2. destruct H2. destruct H3. destruct H4.
    apply tc_sub with (t := ltt_recv pt x); intros; try easy. 
    constructor; try easy.
    apply eq_trans with (y := length llp); try easy.
    apply map_length; try easy. 
    apply SList_map_a24; try easy.
    apply _a24_helper_recv with (S := S); try easy.
    specialize(typable_implies_wfC H0); try easy.
  - specialize(_a23_c (p_ite e P1 P2) e P1 P2 T (Gsl ++ Some S :: Gsr) Gt H (eq_refl (p_ite e P1 P2))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    specialize(typable_implies_wfC H); intros.
    constructor.
    apply expr_subst with (S := S); try easy.
    apply IHP1 with (S := S); try easy.
    apply tc_sub with (t := x); try easy.
    apply IHP2 with (S := S); try easy.
    apply tc_sub with (t := x0); try easy.
  - specialize(_a23_d (p_rec P) P T (Gsl ++ Some S :: Gsr) Gt H (eq_refl (p_rec P))); intros.
    destruct H1. destruct H1.
    apply tc_sub with (t := x); try easy.
    simpl in *. constructor. apply IHP with (S := S); try easy.
    specialize(typable_implies_wfC H); try easy. 
Qed.

Lemma _a24 : forall v Gs Gt P S T,
        typ_proc (Some S :: Gs) Gt P T -> 
        typ_expr Gs v S -> 
        typ_proc Gs Gt (subst_expr_proc P v 0 0) T.
Proof.
  intros. 
  specialize(_a24_helper v 0 P nil Gs Gt S T); intros. simpl in H1. apply H1; try easy.
  specialize(trivial_incrE 0 v); intros. replace (incr_freeE 0 0 v) with v. easy.
Qed.
    

(* 
#[global] Declare Instance RW_scong3: Proper (scong ==> scong ==> impl) betaP.
#[global] Declare Instance RW_scong4: Proper (scong ==> scong ==> impl) beta_multistep.
 *)
(* Definition PAlice: process := 
  p_send "Bob" 1 (e_val (vint 50)) (p_recv "Carol" [None; None; None; Some p_inact]).

Definition PBob: process :=
  p_recv "Alice" [None; Some (p_send "Carol" 2 (e_val (vint 100)) p_inact); None; None; 
                  Some (p_send "Carol" 2 (e_val (vint 2)) p_inact)
                 ].

Definition PCarol: process :=
  p_recv "Bob" [None; None; Some (p_send "Alice" 3 (e_plus (e_var 0) (e_val (vint 1))) p_inact)].

Definition MS: session := ("Alice" <-- Some PAlice) ||| ("Bob" <-- Some PBob) ||| ("Carol" <-- Some PCarol).

Definition MS': session := ("Alice" <-- Some p_inact) ||| ("Bob" <-- Some p_inact) ||| ("Carol" <-- Some p_inact). *)

(* 
Example redMS: beta_multistep MS MS'.
Proof. unfold beta_multistep, MS, MS', PAlice, PBob.

       setoid_rewrite sc_par3.
       setoid_rewrite sc_par2.
       setoid_rewrite sc_par4.
       setoid_rewrite <- sc_par3.
       
       apply multi_step with
       (y := ((("Bob" <-- Some (p_send "Carol" 2 (e_val (vint 100)) p_inact)) |||
              ("Alice" <-- Some (p_recv "Carol" [None; None; None; Some p_inact]))) ||| ("Carol" <-- Some PCarol))
       ).
       apply r_comm.
       unfold PCarol.

       setoid_rewrite sc_par2.
       setoid_rewrite <- sc_par3.
       apply multi_step with
       (y := ((("Carol" <-- Some (p_send "Alice" 3 (e_plus (e_val (vint 100)) (e_val (vint 1)))  p_inact)) |||
              ("Bob" <-- Some p_inact)) ||| ("Alice" <-- Some (p_recv "Carol" [None; None; None; Some p_inact])))
       ).
       apply r_comm.

       setoid_rewrite sc_par2.
       setoid_rewrite <- sc_par3.
       apply multi_step with
       (y := ((("Alice" <-- Some p_inact) |||
              ("Carol" <-- Some p_inact)) ||| ("Bob" <-- Some p_inact))
       ). simpl.
       apply r_comm.
       apply multi_refl.
Qed.
 *)

