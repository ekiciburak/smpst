From SST Require Import aux.unscoped aux.expressions type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

(* Todo: extract P' from muY.P, prove they are the same <- subst and show equal
      dependecy: fv, fv generator
      legal types either bottom up constr or top down induct.
 *)

Section process.
(* Locally closed approach
 *)
Inductive process : Type := 
  | p_bvar : fin -> process
  | p_fvar : fin -> process
  | p_inact : process
  | p_send : part -> label -> expr -> process -> process
  | p_recv : part -> list (prod (prod label sort) process) -> process 
  | p_ite : expr -> process -> process -> process 
  | p_rec : process -> process.
  

(* Fixpoint fv (P : process) : list fin := 
  match P with
    | p_bvar x => []
    | p_fvar x => [x]
    | p_inact => []
    | p_send p l e P' => fv P'
    | p_recv p [] => []
    | p_recv p (((l,s),p') :: xs) => fv (p') ++  fv (p_recv p xs)
    | p_ite e P1 P2 => fv (P1) ++ fv (P2)
    | p_rec P' => fv P'
   end. *)
(* Compute fv (p_inact).
Compute (eq_nat 5 6). *)



(* Definition fresh_free : 
 *)

(* Helper Function *)
Fixpoint increase_bound_depth (P: process) : process :=
  match P with 
    | p_bvar x => p_bvar (x+1)
    | p_send p l e P' => p_send p l e (increase_bound_depth P')
    | p_recv p lis => p_recv p (list_map (fun x => (fst x, increase_bound_depth (snd x))) lis)
    | p_ite e p1 p2 => p_ite e (increase_bound_depth p1) (increase_bound_depth p2) 
    | p_rec P' => p_rec (increase_bound_depth P')
    | _ => P
  end.
  
Fixpoint subst_proc (n : fin) (P : process) (Q: process) : process :=
  match P with
    | p_bvar x => p_bvar x 
    | p_fvar x => if (Nat.eqb x n) then Q else (p_fvar x) 
    | p_inact => p_inact 
    | p_send p l e P' => p_send p l e (subst_proc n P' Q)
    | p_recv p lis => p_recv p (list_map (fun x => (fst x, subst_proc n (snd x) Q)) lis)
    | p_ite e p1 p2 => p_ite e (subst_proc n p1 Q) (subst_proc n p2 Q)
    | p_rec P' => p_rec (subst_proc n P' (increase_bound_depth Q))
  end.
  
Compute ((p_rec p_inact) .: p_fvar).


Fixpoint subst_proc_bound (P : process) (Q : process) : process := 
  match P with 
    | p_bvar x => (Q .: p_bvar) x
    | p_send p l e P' => p_send p l e (subst_proc_bound P' Q)
    | p_recv p lis => p_recv p (list_map (fun x => (fst x, subst_proc_bound (snd x) Q)) lis)
    | p_ite e p1 p2 => p_ite e (subst_proc_bound p1 Q) (subst_proc_bound p2 Q) 
    | p_rec P' => p_rec (subst_proc_bound P' (increase_bound_depth Q))
    | _ => P
  end.
   
   
(*    definition kind of depends on how you want to unfold rec 
 *)
 
 (* Illegal stuff is allowed, like we can do p_bvar 3 without 4 p_recs on the outside, should probably define locally closed
   *)

 
Fixpoint unfold_rec (P : process) : process :=
  match P with 
    | p_send p l e P' => p_send p l e (unfold_rec P')
    | p_recv p lis => p_recv p (list_map (fun x => (fst x, unfold_rec (snd x))) lis)
    | p_ite e p1 p2 => p_ite e (unfold_rec p1) (unfold_rec p2)
    | p_rec P' => subst_proc_bound P' P
    | _ => P
  end.

Definition unfold_outer_rec (P : process) : process :=
  match P with 
    | p_rec P' => subst_proc_bound P' P
    | _ => P
  end.


Example simple_mu : process := 
  p_rec (p_send "Alice" 1 (e_val (vnat 100)) (p_bvar 0)).
  
Compute unfold_rec (unfold_rec simple_mu).

Example Pcomplex_mu : process := 
  p_rec (p_recv "Alice" [
    (0, sbool, p_bvar 0);
    (1, sbool, p_rec (p_recv "Bob" [
       (3, sbool, p_bvar 0);
       (4, sbool, p_bvar 1);
       (5, sbool, p_inact)
    ]));
    (2, sbool, p_inact)
  ]).
  

CoFixpoint Tcomplex_mu : ltt := 
  ltt_recv "Alice" [
    (0, sbool, Tcomplex_mu);
    (1, sbool, complex_mu_1);
    (2, sbool, ltt_end)
  ]
  with complex_mu_1 : ltt :=
    ltt_recv "Bob" [(3, sbool, Tcomplex_mu); (4, sbool, complex_mu_1); (5, sbool, ltt_end)].

Compute unfold_rec Pcomplex_mu.


(* Example _complex_mu_ : typ_proc 0 0 empty Pcomplex_mu Tcomplex_mu.
Proof. unfold PG_agency.
  rewrite(ltt_eq TG_agency). simpl.
  constructor.
 *)


Example recursive_mu : process :=
  p_rec (p_send "A" 0 (e_val (vnat 1)) (
    p_rec (p_recv "B" [
      (1, sbool, p_bvar 0); 
      (2, sbool, p_send "C" 2 (e_val (vnat 2)) (p_bvar 1))
    ])
  )).

Compute unfold_rec recursive_mu.

Example subst_mu : process := 
  p_rec (p_recv "Alice" [
    (0, sbool, p_bvar 0);
    (1, sbool, p_recv "Bob" [
       (3, sbool, p_bvar 0);
       (4, sbool, p_fvar 15);
       (5, sbool, p_fvar 16);
       (6, sbool, p_inact)
    ]);
    (2, sbool, p_inact)
  ]).
 
Compute subst_proc 15 subst_mu Pcomplex_mu. 

Lemma congr_p_inact  : p_inact  = p_inact  .
Proof. congruence. Qed.

Lemma congr_p_send  { s0 : part   } { s1 : label   } { s2 : expr   } { s3 : process   } { t0 : part   } { t1 : label   } { t2 : expr   } { t3 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : p_send  s0 s1 s2 s3 = p_send  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_p_recv  { s0 : part   } { s1 : list (prod (prod (label  ) (sort  )) (process  )) } { t0 : part   } { t1 : list (prod (prod (label  ) (sort  )) (process  )) } (H1 : s0 = t0) (H2 : s1 = t1) : p_recv  s0 s1 = p_recv  t0 t1 .
Proof. congruence. Qed.

Lemma congr_p_ite  { s0 : expr   } { s1 : process   } { s2 : process   } { t0 : expr   } { t1 : process   } { t2 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : p_ite  s0 s1 s2 = p_ite  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_p_rec  { s1 : process   } { t1 : process   }  (H2 : s1 = t1) : p_rec  s1 = p_rec t1 .
Proof. congruence. Qed.


