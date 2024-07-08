From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive.std.
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
  | p_rec : fin -> process -> process.

Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt lb pr llb llp, Forall P llp -> P (p_recv pt lb pr llb llp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall n pr, P pr -> P (p_rec n pr).
  
  Fixpoint process_ind_ref p : P p.
  Proof.
    destruct p.
    - apply (P_var n).
    - apply (P_inact).
    - apply (P_send s n e p (process_ind_ref p)).
    - apply (P_recv).
      - apply (process_ind_ref p). 
      induction l as [ | c l IH].
      clear process_ind_ref.
      - intros. apply ForallR_nil.
      - specialize(ForallR_cons P (fst c) (snd c) l); intros.
        - generalize (process_ind_ref (snd c)). intros. 
          specialize(H H0 IH); intros.
          specialize(surjective_pairing c); intros.
          replace c with (c.1, c.2). easy.
    - apply (P_ite e p1 p2 (process_ind_ref p1) (process_ind_ref p2)).
    - apply (P_rec n p (process_ind_ref p)). 
  Qed.
End process_ind_ref.


Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt lb pr llbp, ForallR P llbp -> P (p_recv pt lb pr llbp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall n pr, P pr -> P (p_rec n pr).
  
  Fixpoint process_ind_ref p : P p.
  Proof.
    destruct p.
    - apply (P_var n).
    - apply (P_inact).
    - apply (P_send s n e p (process_ind_ref p)).
    - apply (P_recv).
      - apply (process_ind_ref p). 
      induction l as [ | c l IH].
      clear process_ind_ref.
      - intros. apply ForallR_nil.
      - specialize(ForallR_cons P (fst c) (snd c) l); intros.
        - generalize (process_ind_ref (snd c)). intros. 
          specialize(H H0 IH); intros.
          specialize(surjective_pairing c); intros.
          replace c with (c.1, c.2). easy.
    - apply (P_ite e p1 p2 (process_ind_ref p1) (process_ind_ref p2)).
    - apply (P_rec n p (process_ind_ref p)). 
  Qed.
End process_ind_ref.


Fixpoint vars (P : process) : list fin :=
  match P with
    | p_var x => [x]
    | p_send p l e P' => vars P'
    | p_recv p _ ct llbp => 
       let fix next xs :=
         match xs with 
          | (_,p)::ys => vars p ++ next ys
          | [] => []
         end
       in next llbp ++ vars ct
    | p_ite e p q => (vars p) ++ (vars q)
    | p_rec n p => n :: vars p
    | _ => []
  end.


Fixpoint rename_force (from : fin) (to : fin) (P : process) : process := 
  match P with 
    | p_var x => if Nat.eqb x from then p_var to else p_var x
    | p_send p l e P' => p_send p l e (rename_force from to P')
    | p_recv p lb ct llbp => p_recv p lb (rename_force from to ct) (list_map (fun x => (fst x, rename_force from to (snd x))) llbp)
    | p_ite e p1 p2 => p_ite e (rename_force from to p1) (rename_force from to p2)
    | p_rec x P' => if Nat.eqb from x then P else p_rec x (rename_force from to P')
    | _ => P
  end. 


Definition fresh_in (x : fin) (P : process) : Prop :=
  let fix isin x lis :=
    match lis with
      | y::ys => x <> y /\ isin x ys
      | _ => True
    end
  in isin x (vars P).

Lemma freshness_in_rec : forall (x y : fin) (P : process), fresh_in y (p_rec x P) -> (y <> x).
Proof.
  intros x y P.
  unfold fresh_in. unfold vars.
  easy.
Qed.
  
Definition p_rename (from : fin) (to : fin) (P : process) (Q : process) : Prop := 
  rename_force from to P = Q.
  
Section alphaP.

 
Inductive alphaP : relation process :=
  | a_inact : alphaP (p_inact) (p_inact)
  | a_var : forall n, alphaP (p_var n) (p_var n)
  | a_send : forall p l e P P', alphaP P P' -> alphaP (p_send p l e P) (p_send p l e P')
  | a_recv : forall p llb xs ys lb x y, length llb = length xs -> length llb = length ys -> alphaP x y -> List.Forall2 alphaP xs ys -> alphaP (p_recv p lb x (zip llb xs)) (p_recv p lb y (zip llb ys))
  | a_ite  : forall e P1 P2 Q1 Q2, alphaP P1 Q1 -> alphaP P2 Q2 -> alphaP (p_ite e P1 P2) (p_ite e Q1 Q2)
  | a_recl  : forall x y P Q, fresh_in y (p_rec x P) -> p_rename x y P Q -> alphaP P Q -> alphaP (p_rec x P) (p_rec y Q)
  | a_recr  : forall x y P Q, fresh_in x (p_rec y Q) -> p_rename y x Q P -> alphaP P Q -> alphaP (p_rec x P) (p_rec y Q)
  | a_rec2  : forall x P Q, alphaP P Q -> alphaP (p_rec x P) (p_rec x Q).


Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Section alphaP_ind_ref.
  
  Variable P : process -> process -> Prop.
  Hypothesis P_inact : P p_inact p_inact.
  Hypothesis P_var  : forall n, P (p_var n) (p_var n).
  Hypothesis P_send : forall p l e P1 P2, P P1 P2 -> P (p_send p l e P1) (p_send p l e P2).
  Hypothesis P_recv : forall p lb x y llb xs ys, length llb = length xs -> length llb = length ys -> P x y 
                      -> List.Forall2 P xs ys -> P (p_recv p lb x (zip llb xs)) (p_recv p lb y (zip llb ys)).
  Hypothesis P_ite  : forall e P1 P2 Q1 Q2, P P1 Q1 -> P P2 Q2 -> P (p_ite e P1 P2) (p_ite e Q1 Q2).
  Hypothesis P_recl : forall x y P1 P2, fresh_in y (p_rec x P1) -> p_rename x y P1 P2 -> P P1 P2 -> P (p_rec x P1) (p_rec y P2).
  Hypothesis P_recr : forall x y P1 P2, fresh_in x (p_rec y P2) -> p_rename y x P2 P1 -> P P1 P2 -> P (p_rec x P1) (p_rec y P2).
  Hypothesis P_recn : forall x P1 P2, P P1 P2 -> P (p_rec x P1) (p_rec x P2). 

  Fixpoint alphaP_ind_ref (P1 P2 : process) (a : alphaP P1 P2) {struct a} : P P1 P2 :=
    match a with 
      | a_inact => P_inact
      | a_var n => P_var n
      | a_send p l e P1 P2 H => P_send p l e P1 P2 (alphaP_ind_ref P1 P2 H) 
      | a_recv p llb xs ys lb x y Hlx Hly Ha La => P_recv p lb x y llb xs ys Hlx Hly (alphaP_ind_ref x y Ha) (Forall2_mono alphaP_ind_ref xs ys La)
      | a_ite e P1 P2 Q1 Q2 H1 H2 => P_ite e P1 P2 Q1 Q2 (alphaP_ind_ref P1 Q1 H1) (alphaP_ind_ref P2 Q2 H2)
      | a_recl x y P1 P2 Hfy Hr Ha => P_recl x y P1 P2 Hfy Hr (alphaP_ind_ref P1 P2 Ha)
      | a_recr x y P1 P2 Hfy Hr Ha => P_recr x y P1 P2 Hfy Hr (alphaP_ind_ref P1 P2 Ha)
      | a_rec2 x P1 P2 Ha => P_recn x P1 P2 (alphaP_ind_ref P1 P2 Ha)
    end.

End alphaP_ind_ref.


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

Lemma refl_alphaP : forall P, alphaP P P.
Proof.
  intros. 
  induction P using process_ind_ref.
  - specialize(a_var n); intros; try easy.
  - specialize(a_inact); intros; try easy.
  - specialize(a_send pt lb ex P P IHP); intros; try easy.
  - specialize(a_recv); intros.
    induction llbp.
      - specialize(H0 pt [] [] [] lb P P); intros. 
        specialize(H0 (Logic.eq_refl (length [])) (Logic.eq_refl (length [])) IHP); intros.
        assert(Forall2 alphaP [] []). { easy. }
        specialize(H0 H1); intros; try easy.
        specialize(H0 pt (list_map fst (a::llbp)) (list_map snd (a::llbp)) (list_map snd (a::llbp)) lb P P); intros.
        specialize((list_fst_snd_len (a::llbp))); intros.
        specialize(H0 H1 H1 IHP); intros.
        specialize(unzip_zip (a::llbp)); intros. 
        replace (zip (list_map fst (a :: llbp)) (list_map snd (a :: llbp))) with (a::llbp) in H0.
        clear H1 H2.
        
        
        
        specialize( IHP); intros.
      -  

Lemma sym_alphaP : forall P Q, alphaP P Q -> alphaP Q P.
Proof.
  intros.
  induction H using alphaP_ind_ref; intros; try easy.
  - specialize(a_inact); intros. easy.
  - specialize(a_var n); intros. easy.
  - specialize(a_send p l e P2 P1 IHalphaP); intros. easy.
  - assert(Forall2 alphaP ys xs).
    {
      specialize(Forall2_flip H1); intros.
      simpl in H2. easy.
    }
    specialize(a_recv p llb ys xs lb y x H0 H IHalphaP H2); intros. easy.
  - specialize(a_ite e Q1 Q2 P1 P2 IHalphaP IHalphaP0); intros. easy.
  - specialize(a_recr y x P2 P1 H H0 IHalphaP); intros. easy.
  - specialize(a_recl y x P2 P1 H H0 IHalphaP); intros. easy.
  - specialize(a_rec2 x P2 P1 IHalphaP); intros. easy.
Qed.



Lemma alphaP_inv_send : forall P P' p l e, alphaP P (p_send p l e P') 
  -> exists Q, P = p_send p l e Q /\ alphaP Q P'.
Proof.
  intros. inversion H. exists P'. split; try easy. apply (a_refl P').
  exists P0. easy. 
Qed.

Lemma zipeq {A : Type} : forall (x y : A) (xs : list A), In (x,y) (zip xs xs) -> x = y.
  intros x y xs.
  induction xs.
  easy. 
  simpl. 
  intros. destruct H. 
  specialize(pair_equal_spec a x a y); intros. destruct H0. specialize(H0 H); intros.
  destruct H0. subst. easy.
  specialize(IHxs H); intros.
  easy.
Qed.
  
Lemma alphaP_cong_recv : forall P p lb x llb xs, alphaP P (p_recv p lb x llb xs) 
  -> exists y ys, P = p_recv p lb y llb ys /\ alphaP x y /\ List.Forall (fun u => alphaP (fst u) (snd u)) (zip xs ys).
Proof.
  intros. inversion H. exists x. exists xs. 
  split. easy. split. apply (a_refl x). 
  apply Forall_forall. intros.
  specialize(surjective_pairing x0); intros.
  specialize(zipeq x0.1 x0.2 xs); intros.
  replace (x0.1,x0.2) with x0 in H4.
  specialize(H4 H2); intros. specialize(a_refl x0.1); intros.
  replace x0.1 with x0.2 in *. easy.
  exists x0. exists xs0.
  split. easy. split. 
  admit.
  admit.
Admitted.
     

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Definition alpha_multistep : relation process := multi alphaP.

End alphaP.

Lemma transitive_multi {X : Type} : forall (R : relation X) (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros R x y z H.
  revert z.
  induction H; intros. easy.
  specialize(IHmulti z0 H1).
  specialize(@multi_step X R); intros.
  apply H2 with (y := y). easy. easy.
Qed.


Definition quaternary_relation (A : Type) : Type := A -> A -> A -> A -> Prop.

Print relation.
Print quaternary_relation.

(* relation of sub_from, sub_to, proc_before_sub, proc_after_sub, rec case, ensures is fresh in both x and P *)
Inductive substitutionP : quaternary_relation process :=
  | sub_var_is   : forall P x, substitutionP (p_var x) P (p_var x) P
  | sub_var_not  : forall P x y, x <> y -> substitutionP (p_var x) P (p_var y) (p_var y)
  | sub_inact    : forall P x, substitutionP (p_var x) P (p_inact) (p_inact)
  | sub_send     : forall P x pt l e P' Q', substitutionP (p_var x) P P' Q' -> substitutionP (p_var x) P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x pt lb ct1 ct2 llb xs ys, length xs = length ys -> substitutionP (p_var x) P ct1 ct2 ->
  List.Forall (fun u => substitutionP (p_var x) P (fst u) (snd u)) (zip xs ys) -> substitutionP (p_var x) P (p_recv pt lb ct1 llb xs) (p_recv pt lb ct2 llb ys)
  | sub_ite       : forall P x e P1 P2 Q1 Q2, substitutionP (p_var x) P P1 Q1 -> substitutionP (p_var x) P P2 Q2 -> substitutionP (p_var x) P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x y P' Q', x <> y -> fresh_in y P -> substitutionP (p_var x) P P' Q' -> substitutionP (p_var x) P (p_rec y P') (p_rec y Q')
  | sub_alpha     : forall P x P1 P2 Q, alpha_multistep P1 P2 -> substitutionP (p_var x) P P1 Q -> substitutionP (p_var x) P P2 Q.
 (* | sub_alpha     : forall P x P' Q1 Q2, substitutionP (p_var x) P P' Q1 -> alphaP Q1 Q2 -> substitutionP (p_var x) P P' Q2. *)
  

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

End process.

