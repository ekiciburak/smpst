From mathcomp Require Import all_ssreflect.
From SST Require Import aux.unscoped aux.expressions type.global tree.global tree.local. 
Require Import List String Datatypes ZArith Relations Setoid Morphisms.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat. 
Require Import JMeq.

Section process.

Inductive process : Type := 
  | p_var : fin -> process
  | p_inact : process
  | p_send : part -> label -> expr -> process -> process
  | p_recv : part -> list label -> list process -> process 
  | p_ite : expr -> process -> process -> process 
  | p_rec : process -> process.

Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt llb llp, Forall P llp -> P (p_recv pt llb llp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall pr, P pr -> P (p_rec pr).
  
  Fixpoint process_ind_ref p : P p.
  Proof.
    destruct p.
    - apply (P_var n).
    - apply (P_inact).
    - apply (P_send s n e p (process_ind_ref p)).
    - apply (P_recv).
      induction l0 as [ | c l0 IH].
      clear process_ind_ref. 
      - easy.
      - apply (Forall_cons); intros. 
        - generalize (process_ind_ref c); intros. apply H.
        - apply IH.
    - apply (P_ite e p1 p2 (process_ind_ref p1) (process_ind_ref p2)).
    - apply (P_rec p (process_ind_ref p)). 
  Qed.
End process_ind_ref.

Compute (length []) <> 0%nat.

Inductive SSortedNList : list fin -> Prop :=
  | sort1 : forall a, SSortedNList [a]
  | sort2 : forall (z1 z2 : fin), forall l, le z1 z2 -> SSortedNList (z2 :: l) -> SSortedNList (z1 :: z2 :: l).
  
(* Lemma test : not (SSortedNList []).
Proof. 
  intros. intuition.
  inversion H.
Qed. *)

Inductive wtyped : process -> Prop := 
  | wp_var : forall n, wtyped (p_var n)
  | wp_inact : wtyped p_inact
  | wp_send: forall pt lb ex pr, wtyped pr -> wtyped (p_send pt lb ex pr)
  | wp_recv : forall pt llb llp, length llb = length llp -> SSortedNList llb -> List.Forall wtyped llp -> wtyped (p_recv pt llb llp)
  | wp_ite : forall e P1 P2, wtyped P1 -> wtyped P2 -> wtyped (p_ite e P1 P2)
  | wp_rec : forall pr, wtyped pr -> wtyped (p_rec pr).

Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Lemma list_fst_snd_len {A B: Type} : forall (lis : list (A*B)), length (list_map fst lis) = length (list_map snd lis).
Proof.
  intros.
  induction lis.
  easy.
  simpl. 
  replace (length (list_map fst lis)) with (length (list_map snd lis)).
  easy.
Qed.

Lemma unzip_zip {A B : Type} : forall (lis : list (A*B)), lis = zip (list_map fst lis) (list_map snd lis).
Proof.
  intros.
  induction lis.
  - easy.
  - simpl. replace lis with (zip (list_map fst lis) (list_map snd lis)) at 1.
    specialize(surjective_pairing a); intros. 
    replace a with (a.1,a.2). easy.
Qed.

Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, lt k m -> P k) -> P m) ->
    forall n, P n.
Proof.
  intros H n; enough (H0: forall p, le p n -> P p).
    - apply H0, Nat.le_refl.
    - induction n.
      + intros. apply H. inversion H0. easy.
      + intros. apply H. intros. apply IHn.  inversion H0. 
        * rewrite H2 in H1. apply PeanoNat.lt_n_Sm_le in H1. assumption.
        * specialize (PeanoNat.Nat.lt_le_trans k p n H1 H3). apply PeanoNat.Nat.lt_le_incl.
Qed.

Fixpoint process_size (P : process) : fin := 
  match P with 
    | p_var n => 0 
    | p_inact => 0
    | p_send pt lb e p => 1 + process_size p 
    | p_recv pt llb lp => 
      let fix mx_siz lis := 
        match lis with 
          | x::xs => max (process_size x) (mx_siz xs)
          | [] => 0
        end
      in 1 + mx_siz lp
    | p_ite e p1 p2 => 1 + max (process_size p1) (process_size p2)
    | p_rec p => 1 + (process_size p)
  end.

Lemma psize_exists : forall P, exists n, process_size P = n.
Proof.
  intro P. 
  exists (process_size P). easy.
Qed.

Fixpoint incr_freeE (fv m : fin) (e : expr) :=
  match e with
    | e_var n    => e_var (if fv <= n then (n + m)%coq_nat else n)
    | e_val v    => e_val v 
    | e_succ n   => e_succ (incr_freeE fv m n)
    | e_neg n    => e_neg (incr_freeE fv m n)
    | e_not n    => e_not (incr_freeE fv m n)
    | e_gt u v   => e_gt (incr_freeE fv m u) (incr_freeE fv m v)
    | e_plus u v => e_plus (incr_freeE fv m u) (incr_freeE fv m v) 
  end. 

Fixpoint incr_free (fvP fvE m k : fin) (P : process) : process :=
  match P with 
    | p_var n          => p_var (if fvP <= n then ((n + m)%coq_nat) else n)
    | p_inact          => p_inact
    | p_send p l e P'  => p_send p l (incr_freeE fvE k e) (incr_free fvP fvE m k P')
    | p_recv p llb llp => p_recv p llb (list_map (incr_free fvP (S fvE) m k) llp)
    | p_ite e P1 P2    => p_ite (incr_freeE fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
    | p_rec P'         => p_rec (incr_free (S fvP) fvE m k P')
  end.

Section substitution.

Definition subst_relation (A : Type) : Type := fin -> fin -> fin -> A -> A -> A -> Prop.


(* relation of sub_from, sub_to, proc_before_sub, proc_after_sub, rec case, ensures is fresh in both x and P *)
Inductive substitutionP : subst_relation process :=
  | sub_var_is   : forall P x m n,              substitutionP x m n P (p_var x) (incr_free 0 0 m n P)
  | sub_var_not  : forall P x y m n, x <> y ->  substitutionP x m n P (p_var y) (p_var y)
  | sub_inact    : forall P x m n,              substitutionP x m n P (p_inact) (p_inact)
  | sub_send     : forall P x m n pt l e P' Q', substitutionP x m n P P' Q' -> substitutionP x m n P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x m n pt llb xs ys, length llb = length xs -> length llb = length ys -> SSortedNList llb -> 
  List.Forall2 (substitutionP x m (S n) P) xs ys -> substitutionP x m n P (p_recv pt llb xs) (p_recv pt llb ys)
  | sub_ite       : forall P x m n e P1 P2 Q1 Q2, substitutionP x m n P P1 Q1 -> substitutionP x m n P P2 Q2 -> substitutionP x m n P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x m n P' Q', substitutionP (S x) (S m) n P P' Q' -> substitutionP x m n P (p_rec P') (p_rec Q').

(* 
Section substitutionP_ind_ref.
  
  Variable P : fin -> fin -> process -> process -> process -> Prop.
  Hypothesis P_var_is :  forall Pr X N, P X N Pr (p_var X) (incr_free 0 0 X N Pr).
  Hypothesis P_var_not : forall Pr X Y N, X <> Y -> P X N Pr (p_var Y) (p_var Y).
  Hypothesis P_inact :   forall Pr X N, P X N Pr p_inact p_inact.
  Hypothesis P_send :    forall Pr X N pt l e P' Q', P X N Pr P' Q' -> P X N Pr (p_send pt l e P') (p_send pt l e Q').
  Hypothesis P_recv :    forall Pr X N pt llb xs ys, length llb = length xs -> length llb = length ys -> SSortedNList llb 
                              -> List.Forall2 (P X (S N) Pr) xs ys -> P X N Pr (p_recv pt llb xs) (p_recv pt llb ys).
  Hypothesis P_ite :     forall Pr X N e P1 P2 Q1 Q2, P X N Pr P1 Q1 -> P X N Pr P2 Q2 -> P X N Pr (p_ite e P1 P2) (p_ite e Q1 Q2).
  Hypothesis P_rec :     forall Pr X N P1 Q1, P (S X) N Pr P1 Q1 -> P X N Pr (p_rec P1) (p_rec Q1).
  Fixpoint substitutionP_ind_ref (X N : fin) (Pr P1 P2 : process) (a : substitutionP X N Pr P1 P2) {struct a} : P X N Pr P1 P2 :=
    match a with 
      | sub_var_is p x n => P_var_is p x n
      | sub_var_not p x y n Hn => P_var_not p x y n Hn
      | sub_inact p x n => P_inact p x n
      | sub_send p x n pt l e P' Q' H => P_send p x n pt l e P' Q' (substitutionP_ind_ref x n p P' Q' H)
      | sub_recv p x n pt llb xs ys Hbx Hby HSb Lxy => P_recv p x n pt llb xs ys Hbx Hby HSb (Forall2_mono (substitutionP_ind_ref x n p) xs ys Lxy)
      | sub_ite p x n e p1 p2 q1 q2 H1 H2 => P_ite p x n e p1 p2 q1 q2 (substitutionP_ind_ref x n p p1 q1 H1) (substitutionP_ind_ref x n p p2 q2 H2)
      | sub_rec p x n p1 q1 Hsb => P_rec p x n p1 q1 (substitutionP_ind_ref (S x) (S n) p p1 q1 Hsb)
    end.

End substitutionP_ind_ref.
 *)

(* Lemma inv_subst_send : forall x P Q1 Q2 P' pt l e, substitutionP x P Q1 Q2 -> (Q1 = p_send pt l e P') -> exists 
   *)
  

(* Example alpha_subst : substitutionP (p_var 0) (p_var 1) (p_rec 1 (p_ite (e_var 100) (p_var 0) (p_var 1))) (p_rec 2 (p_ite (e_var 100) (p_var 1) (p_var 2))).
Proof.
  apply sub_alpha with 
  (P1 := (p_rec 2 (p_ite (e_var 100) (p_var 0) (p_var 2)))).
  - apply a_recl. unfold fresh_in. simpl. easy.
  - unfold p_rename. unfold rename_force. simpl. easy.
  apply sub_rec. 
  - easy.
  - unfold fresh_in. simpl. easy.
  repeat constructor. easy.
Qed.
 *)
(* 
Inductive scongP : relation process := 
  | sc_subst    : forall P x Q, substitutionP (p_var x) (p_rec x P) P Q -> scongP (p_rec x P) Q
  | sc_alpha    : forall P Q, alphaP P Q -> scongP P Q
  | sc_send : forall p l e P P', scongP P P' -> scongP (p_send p l e P) (p_send p l e P')
  | sc_recv : forall p xs ys, length xs = length ys -> List.Forall (fun u => (fst (fst u)) = (fst (snd u)) /\ scongP (snd (fst u)) (snd (snd u))) (zip xs ys) -> scongP (p_recv p xs) (p_recv p ys)
  | sc_ite  : forall e P1 P2 Q1 Q2, scongP P1 Q1 -> scongP P2 Q2 -> scongP (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sc_rec  : forall x P Q, scongP P Q -> scongP (p_rec x P) (p_rec x Q).

Declare Instance Equivalence_scongP : Equivalence scongP.

Example simple_mu_cong : scongP (p_rec 0 (p_send "Alice" 1 (e_val (vnat 100)) (p_var 0))) 
                                         (p_send "Alice" 1 (e_val (vnat 100)) (p_rec 0 (p_send "Alice" 1 (e_val (vnat 100)) (p_var 0)))).
Proof.
  apply sc_subst.
  repeat constructor.
Qed.


Lemma congr_p_inact  : p_inact  = p_inact  .
Proof. congruence. Qed.

Lemma congr_p_send  { s0 : part   } { s1 : label   } { s2 : expr   } { s3 : process   } { t0 : part   } { t1 : label   } { t2 : expr   } { t3 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : p_send  s0 s1 s2 s3 = p_send  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_p_recv  { s0 : part   } { s1 : list (prod (label  ) (process  )) } { t0 : part   } { t1 : list (prod (label  ) (process  )) } (H1 : s0 = t0) (H2 : s1 = t1) : p_recv  s0 s1 = p_recv  t0 t1 .
Proof. congruence. Qed.

Lemma congr_p_ite  { s0 : expr   } { s1 : process   } { s2 : process   } { t0 : expr   } { t1 : process   } { t2 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : p_ite  s0 s1 s2 = p_ite  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_p_rec  { s1 : fin} {t1 : fin} { s2 : process} { t2 : process}  (H2 : s1 = t1) (H3 : s2 = t2) : p_rec s1 s2 = p_rec t1 t2.
Proof. congruence. Qed.


(* substitute e into e_var 0 of e1, assuming e has no occurence of e_var*)
Fixpoint subst_expr (e : expr) (e1 : expr) : expr :=
  match e1 with 
    | e_var n => (e .: e_var) n
    | e_succ e' => e_succ (subst_expr e e')
    | e_neg e' => e_neg (subst_expr e e')
    | e_not e' => e_not (subst_expr e e')
    | e_gt e' e'' => e_gt (subst_expr e e') (subst_expr e e'')
    | e_plus e' e'' => e_plus (subst_expr e e') (subst_expr e e'')
    | _ => e1
  end.
  
(* For a choice function, substitutes expr to e_var 0 (decr everything else), return process continuation of choice with label l with e substituted for e_var 0. anything else is kept as is. If label doesn't appear in the list we return p
 *)
Definition subst_expr_proc (p : process) (l : label) (e : expr) : (option process) :=
  match p with
    | p_recv pt xs => 
      let fix next lst := 
        match lst with
          | (lbl,P)::ys => 
            if Nat.eqb lbl l then 
              let fix rec p' :=
                match p' with 
                  | p_send pt' l' e' P' => p_send pt' l' (subst_expr e e') (rec P')
                  | p_ite e' P' Q' => p_ite (subst_expr e e') (rec P') (rec Q')
                  | p_recv pt' lst' => p_recv pt' (list_map (prod_map (fun x => x) (rec)) lst')
                  | p_rec n P' => p_rec n (rec P')
                  | _ => p'
                end 
              in Some (rec P)
            else next ys 
          | _ => None
        end
      in next xs
    | _ => None
  end.


 *)

End substitution.

End process.

