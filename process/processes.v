From mathcomp Require Import all_ssreflect.
From SST Require Import src.expressions type.global type.local type.isomorphism. 
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
  | p_recv : part -> list (option process) -> process 
  | p_ite : expr -> process -> process -> process 
  | p_rec : process -> process.

Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt llp, Forall (fun u => 
      match u with 
        | Some k => P k 
        | None   => True 
      end) llp -> P (p_recv pt llp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall pr, P pr -> P (p_rec pr).
  
  Fixpoint process_ind_ref p : P p.
  Proof.
    destruct p.
    - apply (P_var n).
    - apply (P_inact).
    - apply (P_send s n e p (process_ind_ref p)).
    - apply (P_recv).
      induction l as [ | c l IH].
      clear process_ind_ref. 
      - easy.
      - apply (Forall_cons); intros. destruct c. 
        - generalize (process_ind_ref p); intros. easy. easy.
        - apply IH.
    - apply (P_ite e p1 p2 (process_ind_ref p1) (process_ind_ref p2)).
    - apply (P_rec p (process_ind_ref p)). 
  Qed.
End process_ind_ref.

Inductive wtyped : process -> Prop := 
  | wp_var : forall n, wtyped (p_var n)
  | wp_inact : wtyped p_inact
  | wp_send: forall pt lb ex pr, wtyped pr -> wtyped (p_send pt lb ex pr)
  | wp_recv : forall pt llp, SList llp -> List.Forall (fun u => (u = None) \/ (exists k, u = Some k /\ wtyped k)) llp -> wtyped (p_recv pt llp)
  | wp_ite : forall e P1 P2, wtyped P1 -> wtyped P2 -> wtyped (p_ite e P1 P2)
  | wp_rec : forall pr, wtyped pr -> wtyped (p_rec pr).

Lemma list_fst_snd_len {A B: Type} : forall (lis : list (A*B)), length (List.map fst lis) = length (List.map snd lis).
Proof.
  intros.
  induction lis.
  easy.
  simpl. 
  replace (length (List.map fst lis)) with (length (List.map snd lis)).
  easy.
Qed.

Lemma unzip_zip {A B : Type} : forall (lis : list (A*B)), lis = zip (List.map fst lis) (List.map snd lis).
Proof.
  intros.
  induction lis.
  - easy.
  - simpl. replace lis with (zip (List.map fst lis) (List.map snd lis)) at 1.
    specialize(surjective_pairing a); intros. 
    replace a with (a.1,a.2). easy.
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
    | e_det u v  => e_det (incr_freeE fv m u) (incr_freeE fv m v)
  end. 

Fixpoint incr_free (fvP fvE m k : fin) (P : process) : process :=
  match P with 
    | p_var n          => p_var (if fvP <= n then ((n + m)%coq_nat) else n)
    | p_inact          => p_inact
    | p_send p l e P'  => p_send p l (incr_freeE fvE k e) (incr_free fvP fvE m k P')
    | p_recv p llp     => p_recv p (List.map (
        fun u => match u with 
          | Some p' => Some (incr_free fvP (S fvE) m k p')
          | None    => None
        end) llp)
    | p_ite e P1 P2    => p_ite (incr_freeE fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
    | p_rec P'         => p_rec (incr_free (S fvP) fvE m k P')
  end.

Section substitution.

Definition subst_relation (A : Type) : Type := fin -> fin -> fin -> A -> A -> A -> Prop.

(* relation of sub_from, sub_to, proc_before_sub, proc_after_sub, rec case, ensures is fresh in both x and P *)
Inductive substitutionP : subst_relation process :=
  | sub_var_is   : forall P x m n,              substitutionP x m n P (p_var x) (incr_free 0 0 m n P)
  | sub_var_notz : forall P x m n, x <> 0 ->    substitutionP x m n P (p_var 0) (p_var 0)
  | sub_var_not1 : forall P x y m n, x <> S y -> x <= y -> substitutionP x m n P (p_var (S y)) (p_var y)
  | sub_var_not2 : forall P x y m n, x <> S y -> y < x  -> substitutionP x m n P (p_var (S y)) (p_var (S y))
  | sub_inact    : forall P x m n,              substitutionP x m n P (p_inact) (p_inact)
  | sub_send     : forall P x m n pt l e P' Q', substitutionP x m n P P' Q' -> substitutionP x m n P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x m n pt xs ys, 
  List.Forall2 (fun u v => 
    (u = None /\ v = None) \/
    (exists k l, u = Some k /\ v = Some l /\ substitutionP x m (S n) P k l)  
  ) xs ys -> substitutionP x m n P (p_recv pt xs) (p_recv pt ys)
  | sub_ite       : forall P x m n e P1 P2 Q1 Q2, substitutionP x m n P P1 Q1 -> substitutionP x m n P P2 Q2 -> substitutionP x m n P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x m n P' Q', substitutionP (S x) (S m) n P P' Q' -> substitutionP x m n P (p_rec P') (p_rec Q').



End substitution.

End process.

