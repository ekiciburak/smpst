From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local.
Require Import List String Coq.Arith.PeanoNat Relations. 
Import ListNotations. 

Inductive gnode : Type := 
  | gnode_end : gnode
  | gnode_pq : part -> part -> gnode
  | gnode_s  : sort -> gnode.

Inductive gttmap : global -> list fin -> option fin -> gnode -> Prop := 
  | gmap_end : gttmap g_end nil None gnode_end
  | gmap_pq  : forall p q xs, gttmap (g_send p q xs) nil None (gnode_pq p q)
  | gmap_con : forall n lis xs p q st gk s gn, onth n xs = Some (st, gk) -> gttmap gk lis s gn -> gttmap (g_send p q xs) (n :: lis) s gn
  | gmap_st  : forall n xs p q st gk, onth n xs = Some (st, gk) -> gttmap (g_send p q xs) nil (Some n) (gnode_s st)
  | gmap_mu  : forall lis g Q s gn, subst_global 0 0 (g_rec g) g Q -> gttmap (g_rec g) lis s gn -> gttmap Q lis s gn. 


(* global trees with context holes *)
Inductive gtth: Type :=
  | gtth_hol    : fin -> gtth
  | gtth_send   : part -> part -> list (option (sort * gtth)) -> gtth.

Section gtth_ind_ref.
  Variable P : gtth -> Prop.
  Hypothesis P_hol : forall n, P (gtth_hol n).
  Hypothesis P_send : forall p q xs, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ P g)) xs -> P (gtth_send p q xs).
  
  Fixpoint gtth_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_hol.
    - apply P_send.
      induction l; intros; try easy.
      constructor; try easy.
      destruct a. 
      - destruct p. right. exists s1. exists g. split. easy. apply gtth_ind_ref.
      - left. easy.
  Qed.

End gtth_ind_ref.

Definition balancedG (G : global) := forall G w w' p q gn,
  gttmap G w None gn -> gttmap G (w ++ w') None (gnode_pq p q) -> 
  (exists k, forall w', gttmap G (w ++ w') None (gnode_end) \/ 
                        (List.length w' = k /\ exists w2 w0, w' = w2 ++ w0 /\ exists r, 
                        gttmap G (w ++ w2) None (gnode_pq p r) \/ gttmap G (w ++ w2) None (gnode_pq r p))) /\
  (exists k, forall w', gttmap G (w ++ w') None (gnode_end) \/
                        (List.length w' = k /\ exists w2 w0, w' = w2 ++ w0 /\ exists r,
                        gttmap G (w ++ w2) None (gnode_pq q r) \/ gttmap G (w ++ w2) None (gnode_pq r q))).

Definition wfgT G := wfG G /\ (forall n, exists m, guardG n m G) /\ balancedG G.

Definition wfgC G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G') /\ balancedG G'. 

Definition wfC T := exists T', lttTC T' T /\ wfL T' /\ (forall n, exists m, guardL n m T').