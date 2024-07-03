From mathcomp Require Import all_ssreflect.
From SST Require Import aux.unscoped aux.expressions type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations Setoid Morphisms .
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat.

Section process.
(* lambda appr *) 

Inductive process : Type := 
  | p_var : fin -> process
  | p_inact : process
  | p_send : part -> label -> expr -> process -> process
  | p_recv : part -> list (prod label process) -> process 
  | p_ite : expr -> process -> process -> process 
  | p_rec : fin -> process -> process.


Example simple_mu : process := 
  p_rec 0 (p_send "Alice" 1 (e_val (vnat 100)) (p_var 0)).
  
Example Pcomplex_mu : process := 
  p_rec 0 (p_recv "Alice" [
    (0, p_var 0);
    (1, p_rec 1 (p_recv "Bob" [
       (3, p_var 0);
       (4, p_var 1);
       (5, p_inact)
    ]));
    (2, p_inact)
  ]).
  

CoFixpoint Tcomplex_mu : ltt := 
  ltt_recv "Alice" [
    (0, sbool, Tcomplex_mu);
    (1, sbool, complex_mu_1);
    (2, sbool, ltt_end)
  ]
  with complex_mu_1 : ltt :=
    ltt_recv "Bob" [(3, sbool, Tcomplex_mu); (4, sbool, complex_mu_1); (5, sbool, ltt_end)].

Example recursive_mu : process :=
  p_rec 0 (p_send "A" 0 (e_val (vnat 1)) (
    p_rec 1 (p_recv "B" [
      (1, p_var 0); 
      (2, p_send "C" 2 (e_val (vnat 2)) (p_var 1))
    ])
  )).
  
Example subst_mu : process := 
  p_rec 0 (p_recv "Alice" [
    (0, p_var 0);
    (1, p_recv "Bob" [
       (3, p_var 0);
       (4, p_var 15);
       (5, p_var 16);
       (6, p_rec 2 p_inact)
    ]);
    (2, p_inact)
  ]).
  

Fixpoint fv (P : process) : list fin := 
  match P with
    | p_var x => [x]
    | p_send p l e P' => fv P'
    | p_recv p lis => 
       let fix next xs :=
         match xs with 
          | (_,p)::ys => (fv p) ++ next ys
          | _ => []
         end
       in next lis 
    | p_ite e p q => (fv p) ++ (fv q)
    | p_rec n p => 
      let fix fil k xs :=
        match xs with
          | x::ys => if Nat.eqb x k then fil k ys else x::(fil k ys)
          | _ => []
        end
      in fil n (fv p)
    | _ => []
   end.
   
Fixpoint vars (P : process) : list fin :=
  match P with
    | p_var x => [x]
    | p_send p l e P' => vars P'
    | p_recv p lis => 
       let fix next xs :=
         match xs with 
          | (_,p)::ys => (vars p) ++ next ys
          | [] => []
         end
       in next lis 
    | p_ite e p q => (fv p) ++ (fv q)
    | p_rec n p => n :: vars p
    | _ => []
  end.
   
Definition fresh_from_list (lis : list fin) : fin :=
  match lis with 
    | [] => 0
    | _ => 
      let fix max_lis xs :=
        match xs with
          | x::ys => max x (max_lis ys)
          | _ => 0
        end
      in 1 + (max_lis lis)
    end.

Definition fresh (lis : list process) : fin := 
  let fix max_lis xs :=
    match xs with
      | x::ys => max x (max_lis ys)
      | _ => 0
    end
  in max_lis (list_map (fun x => (fresh_from_list (vars x))) lis).

Fixpoint rename_force (from : fin) (to : fin) (P : process) : process := 
  match P with 
    | p_var x => if Nat.eqb x from then p_var to else p_var x
    | p_send p l e P' => p_send p l e (rename_force from to P')
    | p_recv p lis => p_recv p (list_map (prod_map (fun x => x) (fun x => rename_force from to x)) lis)
    | p_ite e p1 p2 => p_ite e (rename_force from to p1) (rename_force from to p2)
    | p_rec x P' => if Nat.eqb from x then P else p_rec x (rename_force from to P')
    | _ => P
  end.

(* Takes outermost p_rec and renames that and all variables binded to it to a fresh one*)
Definition rename_fresh (P : process) (avoid : list fin) : process := 
  match P with 
    | p_rec x P' => 
        let fre := max (fresh [P']) (fresh_from_list avoid)
        in p_rec fre (rename_force x fre P') 
    | _ => P
  end.


Compute rename_fresh recursive_mu [2;3;4].

(* when fresh variables are generated, overrides previous mappings of that variable (effectively deletes them, acknowledging different binder)*)
Definition rename_pseudo_bruijn (P : process) (avoid : list fin) : process := 
  let fix ren p av mp := 
    match p with
      | p_var x => 
          let fix maps_using xs x := 
            match xs with 
              | (from,to)::ys => if Nat.eqb from x then to else maps_using ys x
              | [] => x
            end 
          in p_var (maps_using mp x)
      | p_send p l e P' => p_send p l e (ren P' av mp)
      | p_recv p lis => p_recv p (list_map (prod_map (fun x => x) (fun x => ren x av mp)) lis)
      | p_ite e p1 p2 => p_ite e (ren p1 av mp) (ren p2 av mp)
      | p_rec x P' => 
          let fre := fresh_from_list av
          in p_rec fre (ren P' (fre::av) ((x,fre)::mp))
      | _ => p
    end
  in ren P (avoid ++ (fv P)) [].
 

Compute rename_pseudo_bruijn recursive_mu [].
Compute recursive_mu.

Definition expr_eq_dec : forall (x y : expr), { x = y } + { x <> y }.
Proof.
decide equality.
decide equality.
decide equality. decide equality. decide equality. decide equality. decide equality. decide equality. decide equality.
Defined.

Definition balpha_equiv (P : process) (Q : process) : bool :=
  let fix syntax_eq P1 P2 :=
    match P1 with 
    | p_var x =>
        match P2 with 
          | p_var y => (Nat.eqb x y)
          | _ => false
        end
    | p_inact =>
        match P2 with
          | p_inact => true 
          | _ => false
        end 
    | p_send p l e P' =>
        match P2 with
          | p_send q l' e' Q' => (eqb p q) && (Nat.eqb l l') && (expr_eq_dec e e') && (syntax_eq P' Q')
          | _ => false 
        end
    | p_recv p lis =>
        match P2 with
          | p_recv q lis' => 
            let fix all_true xs ys := 
              match xs with
                | (l,p')::xs' => 
                  match ys with 
                    | [] => false 
                    | (l',q')::ys' => (Nat.eqb l l') && (syntax_eq p' q') && (all_true xs' ys')
                  end
                | [] => 
                  match ys with
                    | [] => true
                    | _ => false
                  end
              end
            in (eqb p q) && (all_true lis lis')
          | _ => false
        end
    | p_ite e p1 p2 =>
        match P2 with 
          | p_ite e' q1 q2 => (expr_eq_dec e e') && (syntax_eq p1 q1) && (syntax_eq p2 q2)
          | _ => false 
        end
    | p_rec x P' =>
        match P2 with 
          | p_rec y Q' => if Nat.eqb x y then syntax_eq P' Q' else false
          | _ => false 
        end
   end
  in syntax_eq (rename_pseudo_bruijn P (fv P ++ fv Q)) (rename_pseudo_bruijn Q (fv P ++ fv Q)).

Definition fresh_in (x : fin) (P : process) : Prop :=
  let fix isin x lis :=
    match lis with
      | y::ys => x <> y /\ isin x ys
      | _ => True
    end
  in isin x (vars P).
  
Definition p_rename (from : fin) (to : fin) (P : process) (Q : process) : Prop := 
  rename_force from to P = Q.
 
Inductive alphaP : relation process :=
  | a_send : forall p l e P P', alphaP P P' -> alphaP (p_send p l e P) (p_send p l e P')
  | a_recv : forall p xs ys, length xs = length ys -> List.Forall (fun u => (fst (fst u)) = (fst (snd u)) /\ alphaP (snd (fst u)) (snd (snd u))) (zip xs ys) -> alphaP (p_recv p xs) (p_recv p ys)
  | a_ite  : forall e P1 P2 Q1 Q2, alphaP P1 Q1 -> alphaP P2 Q2 -> alphaP (p_ite e P1 P2) (p_ite e Q1 Q2)
  | a_rec1  : forall x y P Q, fresh_in y (p_rec x P) -> p_rename x y P Q -> alphaP (p_rec x P) (p_rec y Q)
  | a_rec2  : forall x P Q, alphaP P Q -> alphaP (p_rec x P) (p_rec x Q).
  
   
Lemma freshness_in_rec : forall (x y : fin) (P : process), fresh_in y (p_rec x P) -> (y <> x).
Proof.
  intros x y P.
  unfold fresh_in. unfold vars.
  easy.
Qed.

Declare Instance Equivalence_alpha : Equivalence alphaP.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Definition alpha_multistep : relation process := multi alphaP.

Definition al1 := p_rec 0 (p_rec 1 (p_recv "Alice " [(1, p_var 0); (2, p_var 1)])).
Definition al2 := p_rec 1 (p_rec 0 (p_recv "Alice " [(1, p_var 1); (2, p_var 0)])).
Definition al3 := p_rec 20 (p_rec 13 (p_recv "Alice " [(1, p_var 20); (2, p_var 13)])).
Definition al4 := p_rec 0 (p_rec 1 (p_recv "Alice " [(1, p_var 1); (2, p_var 1)])).

Compute balpha_equiv al1 al2.
Compute balpha_equiv al1 al4.
Compute rename_pseudo_bruijn (p_rec 20 (p_rec 13 (p_var 20))) [].

(* Example t : 2 <> 3.
Proof.
  simpl. easy. *)
(*
Lemma stronger_multi {X : Type} (R : relation X) : forall (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros x y z.
   *)
  

Example al1_al3 : alpha_multistep al1 al3. 
Proof.
  unfold al1, al3.
  unfold alpha_multistep.
  apply multi_step with 
  (y := (p_rec 20 (p_rec 1 (p_recv "Alice " [(1, p_var 20); (2, p_var 1)])))).
  apply a_rec1. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename. unfold rename_force. simpl. easy.
  
  apply multi_step with 
  (y := (p_rec 20 (p_rec 13 (p_recv "Alice " [(1, p_var 20); (2, p_var 13)])))).
  apply a_rec2. apply a_rec1. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename; unfold rename_force. simpl. easy.
  
  apply multi_refl.
  
Qed.

Example al3_al2 : alpha_multistep al3 al2. 
Proof.
  unfold al3, al2.
  unfold alpha_multistep.
  apply multi_step with 
  (y := (p_rec 1 (p_rec 13 (p_recv "Alice " [(1, p_var 1); (2, p_var 13)])))).
  apply a_rec1. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename. unfold rename_force. simpl. easy.
  
  apply multi_step with 
  (y := (p_rec 1 (p_rec 0 (p_recv "Alice " [(1, p_var 1); (2, p_var 0)])))).
  apply a_rec2. apply a_rec1. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename; unfold rename_force. simpl. easy.
  
  apply multi_refl.
  
Qed.

Lemma transitive_multi {X : Type} : forall (R : relation X) (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros R x y z H.
  revert z.
  
(*   inversion H. subst.
  easy. subst. inversion H0. subst. easy. subst. *)
  induction H; intros. easy.
  specialize(IHmulti z0 H1).
  specialize(@multi_step X R); intros.
  apply H2 with (y := y). easy. easy.
Qed.

Example al1_al2 : alpha_multistep al1 al2.
Proof. 
  unfold al1, al2.
  apply transitive_multi with 
  (y := al3).
  apply al1_al3.
  apply al3_al2.
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
  | sub_recv     : forall P x pt xs ys, length xs = length ys -> List.Forall (fun u => (fst (fst u)) = (fst (snd u)) /\ substitutionP (p_var x) P (snd (fst u)) (snd (snd u))) (zip xs ys) -> substitutionP (p_var x) P (p_recv pt xs) (p_recv pt ys)
 | sub_ite       : forall P x e P1 P2 Q1 Q2, substitutionP (p_var x) P P1 Q1 -> substitutionP (p_var x) P P2 Q2 -> substitutionP (p_var x) P (p_ite e P1 P2) (p_ite e Q1 Q2)
 | sub_rec       : forall P x y P' Q', x <> y -> fresh_in y P -> substitutionP (p_var x) P P' Q' -> substitutionP (p_var x) P (p_rec y P') (p_rec y Q')
 | sub_alpha     : forall P x P1 P2 Q, alphaP P1 P2 -> substitutionP (p_var x) P P1 Q -> substitutionP (p_var x) P P2 Q.
 (* | sub_alpha     : forall P x P' Q1 Q2, substitutionP (p_var x) P P' Q1 -> alphaP Q1 Q2 -> substitutionP (p_var x) P P' Q2. *)
  

Example alpha_subst : substitutionP (p_var 0) (p_var 1) (p_rec 1 (p_ite (e_var 100) (p_var 0) (p_var 1))) (p_rec 2 (p_ite (e_var 100) (p_var 1) (p_var 2))).
Proof.
  apply sub_alpha with 
  (P1 := (p_rec 2 (p_ite (e_var 100) (p_var 0) (p_var 2)))).
  - apply a_rec1. unfold fresh_in. simpl. easy.
  - unfold p_rename. unfold rename_force. simpl. easy.
  apply sub_rec. 
  - easy.
  - unfold fresh_in. simpl. easy.
  repeat constructor. easy.
Qed.

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

End process.



