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
  | p_rec : fin -> process -> process.

Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt llb llp, Forall P llp -> P (p_recv pt llb llp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall n pr, P pr -> P (p_rec n pr).
  
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
    - apply (P_rec n p (process_ind_ref p)). 
  Qed.
End process_ind_ref.

Compute (length []) <> 0%nat.

Inductive SSortedNList : list fin -> Prop :=
  | sort1 : forall a, SSortedNList [a]
  | sort2 : forall (z1 z2 : fin), forall l, le z1 z2 -> SSortedNList (z2 :: l) -> SSortedNList (z1 :: z2 :: l).
  
Lemma test : not (SSortedNList []).
Proof. 
  intros. intuition.
  inversion H.
Qed.

Inductive wtyped : process -> Prop := 
  | wp_var : forall n, wtyped (p_var n)
  | wp_inact : wtyped p_inact
  | wp_send: forall pt lb ex pr, wtyped pr -> wtyped (p_send pt lb ex pr)
  | wp_recv : forall pt llb llp, length llb = length llp -> SSortedNList llb -> List.Forall wtyped llp -> wtyped (p_recv pt llb llp)
  | wp_ite : forall e P1 P2, wtyped P1 -> wtyped P2 -> wtyped (p_ite e P1 P2)
  | wp_rec : forall n pr, wtyped pr -> wtyped (p_rec n pr).

Fixpoint vars (P : process) : list fin :=
  match P with
    | p_var x => [x]
    | p_send p l e P' => vars P'
    | p_recv p llb llp => 
       let fix next xs :=
         match xs with 
          | p::ys => vars p ++ next ys
          | [] => []
         end
       in next llp
    | p_ite e p q => (vars p) ++ (vars q)
    | p_rec n p => n :: vars p
    | _ => []
  end.


Fixpoint rename_force (from : fin) (to : fin) (P : process) : process := 
  match P with 
    | p_var x => if Nat.eqb x from then p_var to else p_var x
    | p_send p l e P' => p_send p l e (rename_force from to P')
    | p_recv p llb llp => p_recv p llb (list_map (rename_force from to) llp)
    | p_ite e p1 p2 => p_ite e (rename_force from to p1) (rename_force from to p2)
    | p_rec x P' => if Nat.eqb from x then P else p_rec x (rename_force from to P')
    | _ => P
  end. 


Fixpoint fresh_in (x : fin) (P : process) : Prop :=
  match P with 
    | p_inact => True 
    | p_var n => x <> n
    | p_send p l e P'  => fresh_in x P'
    | p_recv p llb llp => 
        let fix next_lis lis := 
          match lis with 
            | [] => True 
            | y::ys => fresh_in x y /\ next_lis ys 
          end
        in next_lis llp
    | p_ite e p1 p2 => fresh_in x p1 /\ fresh_in x p2
    | p_rec y P' => x <> y /\ fresh_in x P'
  end.   

Lemma not_vars_implies_fresh_list : forall x pt llb llp, (Forall (fun P : process => ~ In x (vars P) -> fresh_in x P) llp) -> 
               ~ In x (vars (p_recv pt llb llp)) -> fresh_in x (p_recv pt llb llp).
Proof.
  intros x pt llb llp. induction llp; intros; try easy.
  specialize(Forall_cons_iff (fun P : process => ~ In x (vars P) -> fresh_in x P) a llp); intros. destruct H1.
  specialize(H1 H); intros. clear H2. destruct H1.
  specialize(IHllp H2); intros. clear H2.
  simpl in H0. specialize(in_app_iff (vars a) (vars (p_recv pt llb llp)) x); intros. destruct H2.
  specialize(contra_not H3); intros. clear H2 H3.
  specialize(H4 H0); intros. 
  specialize(Decidable.not_or (In x (vars a)) (In x (vars (p_recv pt llb llp))) H4); intros. destruct H2.
  specialize(H1 H2); intros.
  specialize(IHllp H3); intros.
  simpl. split. easy. easy.
Qed.

Lemma not_vars_implies_fresh : forall x P, not (In x (vars P)) -> fresh_in x P.
Proof.
  intros x P. induction P using process_ind_ref; intros; try easy.
  - simpl in *. specialize(Decidable.not_or (n = x) False H); intros. destruct H0. easy.
  - simpl in H. specialize(IHP H); intros. simpl. easy.
  - apply not_vars_implies_fresh_list. easy. easy.
  - simpl. simpl in H. 
    specialize(in_app_iff (vars P1) (vars P2) x); intros. destruct H0.
    specialize(contra_not H1); intros. specialize(H2 H); intros.
    specialize(Decidable.not_or (In x (vars P1)) (In x (vars P2)) H2); intros. destruct H3.
    specialize(IHP1 H3); intros. specialize(IHP2 H4); intros; try easy.
  - simpl. simpl in H. specialize(Decidable.not_or (n = x) (In x (vars P)) H); intros. destruct H0.
    specialize(IHP H1); intros. easy.
Qed.

Fixpoint mx_list (lis : list fin) : fin :=
  match lis with 
    | x::xs => max x (mx_list xs)
    | []    => 0
  end.

Search (Forall).

Lemma succ_max_not_in_list : forall lis, not (In (mx_list lis + 1) lis).
Admitted.

Lemma exists_not_in_var : forall P, exists k, not (In k (vars P)).
Proof.
  intros. exists (mx_list (vars P) +1).
  specialize(succ_max_not_in_list (vars P)). easy.
Qed.

Lemma exists_fresh : forall P, exists k, fresh_in k P.
Proof.
    intros.
    specialize(exists_not_in_var P); intros.
    destruct H.
    specialize(not_vars_implies_fresh x P H); intros.
    exists x. easy.
Qed.

Lemma freshness_in_rec : forall (x y : fin) (P : process), fresh_in y (p_rec x P) -> (y <> x).
Proof.
  intros x y P.
  simpl. easy.
Qed.
  
Lemma freshness_in_var : forall n m, fresh_in n (p_var m) -> n <> m.
Proof.
  intros. 
  unfold fresh_in in H. unfold vars in H. easy.
Qed.

Lemma freshness_in_send : forall m pt lb ex P, fresh_in m (p_send pt lb ex P) -> fresh_in m P.
Proof.
  intros. easy.
Qed.

Lemma freshness_in_recv : forall m pt llb llp, fresh_in m (p_recv pt llb llp) -> List.Forall (fresh_in m) llp.
Proof.
  intros m pt llb llp. induction llp.
  - intros. easy.
  - intros. specialize(Forall_cons_iff (fresh_in m) a llp); intros. destruct H0.
    apply H1. split. simpl in H. destruct H. easy.
    assert(fresh_in m (p_recv pt llb llp)).
    {
      simpl.
      simpl in H. destruct H. easy.
    }
    specialize(IHllp H2); intros. easy.
Qed.

Definition p_rename (from : fin) (to : fin) (P : process) (Q : process) : Prop := 
  rename_force from to P = Q.
  
Section alphaP.




Inductive alphaP : relation process :=
  | a_inact : alphaP (p_inact) (p_inact)
  | a_var : forall n, alphaP (p_var n) (p_var n)
  | a_send : forall p l e P P', alphaP P P' -> alphaP (p_send p l e P) (p_send p l e P')
  | a_recv : forall p llb xs ys, List.Forall2 alphaP xs ys -> alphaP (p_recv p llb xs) (p_recv p llb ys)
  | a_ite  : forall e P1 P2 Q1 Q2, alphaP P1 Q1 -> alphaP P2 Q2 -> alphaP (p_ite e P1 P2) (p_ite e Q1 Q2)
  | a_rec  : forall x y z P Q, fresh_in z (p_rec x P) -> fresh_in z (p_rec y Q) -> alphaP (rename_force x z P) (rename_force y z Q) -> alphaP (p_rec x P) (p_rec y Q).

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
  Hypothesis P_recv : forall p llb xs ys, List.Forall2 P xs ys -> P (p_recv p llb xs) (p_recv p llb ys).
  Hypothesis P_ite  : forall e P1 P2 Q1 Q2, P P1 Q1 -> P P2 Q2 -> P (p_ite e P1 P2) (p_ite e Q1 Q2).
  Hypothesis P_rec  : forall x y z P1 P2, fresh_in z (p_rec x P1) -> fresh_in z (p_rec y P2) -> P (rename_force x z P1) (rename_force y z P2) -> P (p_rec x P1) (p_rec y P2).

  Fixpoint alphaP_ind_ref (P1 P2 : process) (a : alphaP P1 P2) {struct a} : P P1 P2 :=
    match a with 
      | a_inact => P_inact
      | a_var n => P_var n
      | a_send p l e P1 P2 H => P_send p l e P1 P2 (alphaP_ind_ref P1 P2 H) 
      | a_recv p llb xs ys La => P_recv p llb xs ys (Forall2_mono alphaP_ind_ref xs ys La)
      | a_ite e P1 P2 Q1 Q2 H1 H2 => P_ite e P1 P2 Q1 Q2 (alphaP_ind_ref P1 Q1 H1) (alphaP_ind_ref P2 Q2 H2)
      | a_rec x y z P1 P2 Hfx Hfy Hr => P_rec x y z P1 P2 Hfx Hfy (alphaP_ind_ref (rename_force x z P1) (rename_force y z P2) Hr)
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

Lemma refl_alphaP_helper : forall llp, Forall wtyped llp -> Forall (fun P : process => wtyped P -> alphaP P P) llp -> Forall2 alphaP llp llp.
Proof.
  intro llp.
  induction llp.
  intros. easy.
  intros. specialize(Forall_cons_iff); intros.
  specialize(H1 process wtyped a llp); intros. destruct H1.
  specialize(H1 H); intros. clear H H2. destruct H1.
  specialize(Forall_cons_iff); intros.
  specialize(H2 process (fun P : process => wtyped P -> alphaP P P) a llp); intros. destruct H2.
  specialize(H2 H0); intros. clear H0 H3. destruct H2.
  specialize(IHllp H1 H2); intros.
  specialize(H0 H); intros. clear H H1.
  
  specialize(Forall2_cons_iff); intros. 
  specialize(H process process alphaP a a llp llp); intros. destruct H.
  apply H1. split. easy. easy.
Qed.

Lemma alphaP_sym : forall P Q, alphaP P Q -> alphaP Q P.
Proof.
  intros.
  induction H using alphaP_ind_ref; intros; try easy.
  - specialize(a_inact); intros. easy.
  - specialize(a_var n); intros. easy.
  - specialize(a_send p l e P2 P1 IHalphaP); intros. easy.
  - assert(Forall2 alphaP ys xs).
    {
      specialize(Forall2_flip H); intros.
      simpl in H0. easy.
    }
    specialize(a_recv p llb ys xs H0); intros. easy.
  - specialize(a_ite e Q1 Q2 P1 P2 IHalphaP IHalphaP0); intros. easy.
  - specialize(a_rec y x z P2 P1 H0 H IHalphaP); intros. easy.
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
    | p_rec n p => 1 + (process_size p)
  end.

Lemma psize_exists : forall P, exists n, process_size P = n.
Proof.
  intro P. 
  exists (process_size P). easy.
Qed.

Lemma size_cons_rename : forall m n P, process_size P = process_size (rename_force m n P).
Proof.
  intros. induction P using process_ind_ref; intros; try easy.
  - simpl. case_eq (Nat.eqb n0 m); intros. easy. easy.
  - simpl. replace (process_size P) with (process_size (rename_force m n P)). easy.
  - induction llp. 
    - simpl. easy.
    - simpl. specialize(Forall_cons_iff (fun P : process =>
       process_size P = process_size (rename_force m n P)) a llp); intros. destruct H0.
      specialize(H0 H); intros. clear H1. destruct H0. 
      replace (process_size (rename_force m n a)) with (process_size a).
      specialize(IHllp H1); intros.
      simpl in IHllp. specialize(eq_add_S ((fix mx_siz (lis : seq process) : fin :=
           match lis with
           | [] => 0
           | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
           end) llp) ((fix mx_siz (lis : seq process) : fin :=
           match lis with
           | [] => 0
           | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
           end) (list_map (rename_force m n) llp)) IHllp); intros.
      replace ((fix mx_siz (lis : seq process) : fin :=
      match lis with
      | [] => 0
      | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
      end) (list_map (rename_force m n) llp)) with ((fix mx_siz (lis : seq process) : fin :=
      match lis with
      | [] => 0
      | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
      end) llp). easy.
  - simpl. 
    replace (process_size P1) with (process_size (rename_force m n P1)).
    replace (process_size P2) with (process_size (rename_force m n P2)). easy.
  - simpl. case_eq (Nat.eqb m n0); intros.
    - simpl. easy.
    - simpl. replace (process_size P) with (process_size (rename_force m n P)). easy.
Qed.

Lemma wtyped_renaming_helper : forall k p q, (k < 1 + q)%coq_nat -> (k < 1 + max p q)%coq_nat.
Proof.
        intros. specialize(Nat.le_max_r p q); intros.
        specialize(PeanoNat.lt_n_Sm_le k q H); intros.
        specialize(Nat.le_succ_l k (1 + Init.Nat.max p q)); intros. destruct H2. apply H2. clear H2 H3.
        specialize(Nat.le_trans k q (Nat.max p q) H1 H0); intros.
        apply le_n_S. easy.
Qed.

Lemma wtyped_renaming_helper2 : forall k p q, (k < 1 + p)%coq_nat -> (k < 1 + max p q)%coq_nat.
Proof.
        intros. specialize(Nat.le_max_l p q); intros.
        specialize(PeanoNat.lt_n_Sm_le k p H); intros.
        specialize(Nat.le_succ_l k (1 + Init.Nat.max p q)); intros. destruct H2. apply H2. clear H2 H3.
        specialize(Nat.le_trans k p (Nat.max p q) H1 H0); intros.
        apply le_n_S. easy.
Qed.


Lemma alphaP_refl_list : forall x s l l0,
    (forall k : fin,
    (k < x)%coq_nat ->
    forall P : process, process_size P = k -> alphaP P P) -> process_size (p_recv s l l0) = x ->  Forall2 alphaP l0 l0.
Proof.
  intros x s l l0. induction l0.
  intros. easy.
  intros.
  specialize(IHl0 H); intros.
  
  
  Admitted.

Lemma alphaP_refl : forall P, alphaP P P.
Proof.
  intro P.
  specialize(psize_exists P); intros.
  destruct H. revert H. revert P. 
  induction x using strong_ind.
  destruct P. intros; try easy.
  - apply a_var.
  - intros. apply a_inact.
  - intros. apply a_send. simpl in H0.
    specialize(H (process_size P)); intros. 
    replace x with (1 + process_size P) in H. 
    specialize(H (Nat.lt_succ_diag_r (process_size P)) P); intros.
    apply H. easy.
  - intros. apply a_recv.
    specialize(alphaP_refl_list x s l l0 H H0); intros. easy.
  - intros. apply a_ite. simpl in H0.
    specialize(wtyped_renaming_helper2 (process_size P1) (process_size P1) (process_size P2)); intros.
    apply H with (k := (process_size P1)); intros; try easy. subst. apply H1.
    apply Nat.lt_succ_diag_r.
    specialize(wtyped_renaming_helper (process_size P2) (process_size P1) (process_size P2)); intros.
    apply H with (k := process_size P2); intros; try easy. subst. apply H1. 
    apply Nat.lt_succ_diag_r.
  - intros. specialize(exists_fresh (p_rec n P)); intros. destruct H1.
    apply a_rec with (z := x0); intros; try easy.
    apply H with (k := process_size (rename_force n x0 P)); intros; try easy. subst. simpl.
    specialize(size_cons_rename n x0 P); intros. replace (process_size (rename_force n x0 P)) with (process_size P); intros.
    apply Nat.lt_succ_diag_r.
Qed.

Lemma inv_alphaP_inact : forall P, alphaP P p_inact -> P = p_inact.
Proof.
  intros. inversion H. easy.
Qed.

Lemma inv_alphaP_var : forall P n, alphaP P (p_var n) -> P = p_var n.
Proof.
  intros. inversion H. easy.
Qed. 

Lemma inv_alphaP_send : forall P P' p l e, alphaP P (p_send p l e P') 
  -> exists Q, P = p_send p l e Q /\ alphaP Q P'.
Proof.
  intros. inversion H. exists P0. 
  split. easy. easy.
Qed.

Lemma positive_list_length_dst {A} : forall (xs : list A) n, length xs = S(n) -> exists y ys, y::ys = xs.
Proof.
  intros.
  induction xs. easy.
  exists a. exists xs. easy.
Qed.

Lemma forall2_alphaP_sym : forall xs ys, List.Forall2 alphaP xs ys -> List.Forall2 alphaP ys xs.
Proof.
  intro xs. induction xs.
  intros. 
  specialize(Forall2_length H); intros. simpl in *. 
  specialize(length_zero_iff_nil ys); intros.  destruct H1.
  specialize(H1 (esym H0)). subst. easy.
  intros.
  specialize(Forall2_length H); intros. simpl in *.
  specialize(positive_list_length_dst ys (length xs) (esym H0)); intros.
  destruct H1. destruct H1. subst. simpl in *.
  specialize(Forall2_cons_iff alphaP a x xs x0); intros. destruct H1. 
  specialize(H1 H); intros.
  destruct H1.
  specialize(IHxs x0 H3); intros.
  specialize(alphaP_sym a x H1); intros. 
  specialize(Forall2_cons x a H4 IHxs); intros. easy.
Qed.

Lemma inv_alphaP_recv : forall P pt llb llp, alphaP P (p_recv pt llb llp) -> exists Q, P = p_recv pt llb Q /\ List.Forall2 alphaP llp Q.
Proof.
  intros. inversion H. exists xs. 
  split. easy. subst.
  specialize(forall2_alphaP_sym xs llp H2); intros. easy.
Qed.

Lemma inv_alphaP_ite : forall P e P1 P2, alphaP P (p_ite e P1 P2) -> exists Q1 Q2, P = p_ite e Q1 Q2 /\ alphaP P1 Q1 /\ alphaP P2 Q2.
Proof.
  intros. inversion H. subst. exists P0. exists P3. split. easy.
  split. 
  specialize(alphaP_sym P0 P1 H3); intros; try easy.
  specialize(alphaP_sym P3 P2 H5); intros; try easy.
Qed.

Lemma list_renaming_invariance : forall llp n, Forall (fun P : process => forall n : fin, rename_force n n P = P) llp -> (list_map (rename_force n n) llp) = llp.
Proof.
  intro llp. induction llp.
  intros. easy. 
  specialize(Forall_cons_iff (fun P : process => forall n : fin, rename_force n n P = P) a llp); intros.
  destruct H. specialize(H H0); intros. clear H0 H1. destruct H.
  simpl.
  specialize(IHllp n H0); intros. 
  replace (list_map (rename_force n n) llp) with llp.
  specialize(H n); intros.
  replace (rename_force n n a) with a. easy.
Qed.

Lemma renaming_invariance : forall P n, rename_force n n P = P.
Proof.
  intro P. induction P using process_ind_ref; intros; try easy.
  - case_eq (Nat.eqb n n0); intros.
    - simpl. replace (n =? n0)%nat with true. 
      specialize(Nat.eqb_eq n n0); intros. destruct H0. specialize(H0 H); intros. subst. easy.
    - simpl. replace (n =? n0)%nat with false. easy.
  - simpl. specialize(IHP n); intros. replace (rename_force n n P) with P. easy.
  - simpl. specialize(list_renaming_invariance llp n H); intros. 
    replace (list_map (rename_force n n) llp) with llp.
    easy.
  - simpl. specialize(IHP1 n); intros. specialize(IHP2 n); intros.
    replace (rename_force n n P1) with P1. replace (rename_force n n P2) with P2. easy.
  - simpl. case_eq(Nat.eqb n0 n); intros.
    - easy.
    - simpl. specialize(IHP n0); intros.
      replace (rename_force n0 n0 P) with P. easy.
Qed.

Lemma inv_alphaP_rec : forall P n Q, alphaP P (p_rec n Q) -> exists m z Q', P = p_rec m Q' /\ 
        (alphaP (rename_force n z Q) (rename_force m z Q') /\ fresh_in z (p_rec n Q) /\ fresh_in z (p_rec m Q')).
Proof.
  intros. inversion H.
  - subst. exists x. exists z. exists P0. split. easy. split. 
    specialize(alphaP_sym (rename_force x z P0) (rename_force n z Q) H5); intros. easy. easy.
Qed.

Lemma wtyped_alphaP_helper : forall llp x, Forall
      (fun P : process => forall Q : process, alphaP P Q -> wtyped P -> wtyped Q)
      llp -> Forall2 alphaP llp x -> Forall wtyped llp -> Forall wtyped x.
Proof.
  intro llp. induction llp.
  intros. 
  - specialize(Forall2_length H0); intros. simpl in *.
    specialize(length_zero_iff_nil x); intros. destruct H3.
    specialize(H3 (esym H2)); intros. subst. easy.
  - intros.
    specialize(Forall2_length H0); intros. simpl in *.
    specialize(positive_list_length_dst x (length llp) (esym H2)); intros.
    destruct H3. destruct H3. subst.
    specialize(IHllp x1); intros.
    specialize(Forall_cons_iff (fun P : process => forall Q : process, alphaP P Q -> wtyped P -> wtyped Q) a llp); intros.
    destruct H3. specialize(H3 H); intros. clear H4.
    destruct H3.
    specialize(IHllp H4); intros.
    specialize(Forall2_cons_iff alphaP a x0 llp x1); intros. destruct H5.
    specialize(H5 H0); intros. clear H6.
    destruct H5.
    specialize(Forall_cons_iff wtyped a llp); intros. destruct H7. clear H8. 
    specialize(H7 H1); intros. destruct H7.
    specialize(IHllp H6 H8); intros.
    specialize(H3 x0 H5 H7); intros.
    specialize(Forall_cons x0 H3 IHllp); intros. easy.
Qed.

Lemma wtyped_renaming : forall m n P, wtyped P -> wtyped (rename_force m n P).
Proof.
  intros m n P.
  specialize(psize_exists P); intros.
  destruct H.
  revert H H0. revert m n P. 
  induction x using strong_ind.
  intros. destruct P; try easy.
  - simpl. case_eq (Nat.eqb n0 m); intros. 
    apply wp_var. apply wp_var.
  - simpl. apply wp_send. simpl in H0.
    specialize(H (process_size P)); intros. 
    inversion H1. subst. 
    specialize(Nat.lt_succ_diag_r (process_size P)); intros.
    specialize(H H0 m n P); intros. apply H. easy. easy.
  - simpl. 
    inversion H1. subst. 
    apply wp_recv; try easy. specialize(map_length (rename_force m n) l0); intros.
    specialize(eq_trans H5 (esym H0)); intros. easy.
    clear H1 H5 H6. 
    induction l0. easy.
    assert((forall k : fin,
        (k < process_size (p_recv s l l0))%coq_nat ->
        forall (m n : fin) (P : process),
        process_size P = k -> wtyped P -> wtyped (rename_force m n P))).
    
    {
      intros. specialize(H k); intros.
      simpl in H.
      
      specialize(wtyped_renaming_helper k (process_size a) ((fix mx_siz (lis : seq process) : fin :=
           match lis with
           | [] => 0
           | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
           end) l0)%coq_nat H0); intros.
      specialize(H H3 m0 n0 P H1 H2); intros. easy. 
    }
    specialize(IHl0 H0); intros.
    specialize(Forall_cons_iff wtyped a l0); intros. destruct H1.
    specialize(H1 H7); intros. destruct H1.
    specialize(H (process_size a)); intros. clear H0 H2.
    specialize(IHl0 H3); intros. clear H3.
    simpl in H.
    specialize(wtyped_renaming_helper2 (process_size a) (process_size a) 
       (((fix mx_siz (lis : seq process) : fin :=
           match lis with
           | [] => 0
           | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
           end) l0))%coq_nat); intros.
    specialize(Nat.lt_succ_diag_r (process_size a)); intros.
    specialize(H0 H2); intros. clear H2.
    specialize(H H0 m n a); intros.
    specialize(H (erefl (process_size a)) H1); intros. clear H0.
    specialize(Forall_cons_iff wtyped (rename_force m n a) (list_map (rename_force m n) l0)); intros.
    destruct H0.
    apply H2. split. easy. easy.
  - simpl. inversion H1. subst. apply wp_ite. 
    apply H with (k := process_size P1); try easy.
    simpl. specialize(wtyped_renaming_helper2 (process_size P1) (process_size P1) (process_size P2)); intros.
    apply H0. apply Nat.lt_succ_diag_r.
    apply H with (k := process_size P2); try easy.
    simpl. specialize(wtyped_renaming_helper (process_size P2) (process_size P1) (process_size P2)); intros.
    apply H0. apply Nat.lt_succ_diag_r.
  - simpl. case_eq (Nat.eqb m n0); intros. easy.
    apply wp_rec. inversion H1. subst.
    apply H with (k := (process_size P)); intros; try easy.
    simpl.
    apply Nat.lt_succ_diag_r.
Qed.
    
Lemma wtyped_renamingb : forall m n P, wtyped (rename_force m n P) -> wtyped P.
Proof.
  intros m n P. 
  induction P using process_ind_ref; intros; try easy.
  - apply wp_var.
  - apply wp_send. simpl in H. inversion H. subst. 
    specialize(IHP H1); intros; try easy.
  - inversion H0. subst.
    apply wp_recv; try easy.
    specialize(map_length (rename_force m n) llp); intros.
    specialize(eq_trans H4 H1); intros; try easy.
    clear H0 H4 H5.
    specialize(Forall_map (rename_force m n) wtyped llp); intros.
    destruct H0. specialize(H0 H6); intros.
    clear H1.
    induction llp. easy.
    specialize(Forall_cons_iff (fun P : process => wtyped (rename_force m n P) -> wtyped P) a llp); intros.
    destruct H1. specialize(H1 H); intros. clear H2.
    specialize(Forall_cons_iff wtyped (rename_force m n a) (list_map (rename_force m n) llp)); intros.
    destruct H2. specialize(H2 H6); intros. clear H3. destruct H1. destruct H2.
    specialize(Forall_cons_iff (fun x : process => wtyped (rename_force m n x)) a llp); intros.
    destruct H5. specialize(H5 H0); intros. destruct H5. clear H7.
    specialize(IHllp H3 H4 H8); intros.
    specialize(H1 H2); intros.
    apply Forall_cons; try easy.
  - inversion H. subst. 
    apply wp_ite. specialize(IHP1 H2); intros; try easy. specialize(IHP2 H4); intros; try easy.
  - simpl in H. case_eq (Nat.eqb m n0); intros.
    - replace (m =? n0)%nat with true in *. easy.
    - replace (m =? n0)%nat with false in *. inversion H. subst.
      specialize(IHP H2); intros. 
      apply wp_rec. easy.
Qed.

Lemma wtyped_alphaP_list : forall s l l0 x0,
    (forall k : fin,
    (k < process_size (p_recv s l l0))%coq_nat ->
    forall P : process,
    process_size P = k ->
    forall Q : process, alphaP P Q -> wtyped P -> wtyped Q) -> Forall2 alphaP l0 x0 -> Forall wtyped l0 -> Forall wtyped x0.
Proof.
  intros s l l0. revert l. induction l0.
  intros. specialize(Forall2_length H0); intros.
  simpl in H1. specialize(length_zero_iff_nil x0); intros.
  destruct H3. specialize(H3 (esym H2)); intros. subst. easy.
  intros.
  specialize (Forall2_length H0); intros. simpl in H2.
  specialize (positive_list_length_dst x0 (length l0) (esym H2)); intros.
  destruct H3. destruct H3. subst.
  specialize(IHl0 l x1); intros.
  assert ((forall k : fin,
        (k < process_size (p_recv s l l0))%coq_nat ->
        forall P : process,
        process_size P = k ->
        forall Q : process, alphaP P Q -> wtyped P -> wtyped Q)).
  {
    intros. 
    specialize(H k); intros. simpl in H.
    specialize(wtyped_renaming_helper k (process_size a) ((((fix mx_siz (lis : seq process) : fin :=
           match lis with
           | [] => 0
           | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
           end) l0))%coq_nat) H3); intros.
    specialize(H H7 P H4 Q H5 H6); intros. clear H7. easy.
  }
  specialize(IHl0 H3); intros.
  specialize(H (process_size a)); intros.
  simpl in H.
  specialize(wtyped_renaming_helper2 (process_size a) (process_size a) ((((fix mx_siz (lis : seq process) : fin :=
           match lis with
           | [] => 0
           | (x :: xs)%list => Init.Nat.max (process_size x) (mx_siz xs)
           end) l0))%coq_nat)); intros.
  specialize(H4 (Nat.lt_succ_diag_r (process_size a))); intros.
  specialize(H H4 a); intros. clear H4.
  specialize(Forall2_cons_iff alphaP a x l0 x1); intros. destruct H4. specialize(H4 H0); intros. destruct H4.
  specialize(H (erefl (process_size a)) x H4); intros. 
  specialize(Forall_cons_iff wtyped a l0); intros. destruct H7. specialize (H7 H1); intros. destruct H7.
  specialize(H H7); intros. clear H7 H8 H5.
  specialize(IHl0 H6 H9); intros.
  apply Forall_cons; try easy.
Qed.


Lemma wtyped_alphaP : forall P Q, alphaP P Q -> wtyped P -> wtyped Q.
Proof.
  intro P. specialize(psize_exists P); intro. 
  destruct H. revert H. revert P.
  induction x using strong_ind.
  intros.
  destruct P.
  - specialize(inv_alphaP_var Q n); intros.
    specialize(alphaP_sym (p_var n) Q H1); intros.
    specialize(H3 H4); intros. subst. easy.
  - specialize(inv_alphaP_inact Q); intros.
    specialize(alphaP_sym p_inact Q H1); intros.
    specialize(H3 H4); intros; subst. easy.
  - specialize(inv_alphaP_send Q P s n e (alphaP_sym (p_send s n e P) Q H1)); intros.
    destruct H3. destruct H3. subst.
    specialize(H (process_size P)); intros. simpl in H.
    specialize(Nat.lt_succ_diag_r (process_size P)); intros.
    specialize(H H0 P (erefl (process_size P)) x0 (alphaP_sym x0 P H4)); intros.
    inversion H2. subst.
    apply wp_send. specialize(H H5). easy.
  - specialize(inv_alphaP_recv Q s l l0 (alphaP_sym (p_recv s l l0) Q H1)); intros.
    destruct H3. destruct H3. subst. revert H.
    inversion H2. subst. intros.
    apply wp_recv; try easy.
    specialize(Forall2_length H4); intros.
    specialize(eq_trans H5 H0); intros. easy.
    inversion H1. subst.
    specialize(wtyped_alphaP_list s l l0 x0 H H3 H7); intros. easy.
  - specialize(inv_alphaP_ite Q e P1 P2 (alphaP_sym (p_ite e P1 P2) Q H1)); intros.
    destruct H3. destruct H3. destruct H3. destruct H4. subst.
    inversion H2. subst.
    apply wp_ite.
    apply H with (k := process_size P1) (P := P1); intros; try easy. simpl.
    specialize(wtyped_renaming_helper2 (process_size P1) (process_size P1) (process_size P2)); intros.
    specialize(H0 (Nat.lt_succ_diag_r (process_size P1))); intros; try easy.
    apply H with (k := process_size P2) (P := P2); intros; try easy. simpl.
    specialize(wtyped_renaming_helper (process_size P2) (process_size P1) (process_size P2)); intros.
    specialize(H0 (Nat.lt_succ_diag_r (process_size P2))); intros; try easy.
  - specialize(inv_alphaP_rec Q n P (alphaP_sym (p_rec n P) Q H1)); intros.
    destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. destruct H5.
    subst. apply wp_rec.
    apply wtyped_renamingb with (m := x0) (n := x1).
    inversion H2. subst. specialize(wtyped_renaming n x1 P H3); intros. 
    apply H with (k := process_size (rename_force n x1 P)) (P := (rename_force n x1 P)); try easy.
    specialize(size_cons_rename n x1 P); intros. simpl.
    replace (process_size (rename_force n x1 P)) with (process_size P).
    apply Nat.lt_succ_diag_r.
Qed.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x 
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.
  
Lemma transitive_multi {X : Type} : forall (R : relation X) (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros R x y z H.
  revert z.
  induction H; intros. easy.
  specialize(IHmulti z0 H1).
  specialize(@multi_step X R); intros.
  apply H2 with (y := y). easy. easy.
Qed.

Definition alpha_multistep : relation process := multi alphaP.


End alphaP.


Section substitution.

Definition quaternary_relation (A : Type) : Type := fin -> A -> A -> A -> Prop.

(* relation of sub_from, sub_to, proc_before_sub, proc_after_sub, rec case, ensures is fresh in both x and P *)
Inductive substitutionP : quaternary_relation process :=
  | sub_var_is   : forall P x,             substitutionP x P (p_var x) P
  | sub_var_not  : forall P x y, x <> y -> substitutionP x P (p_var y) (p_var y)
  | sub_inact    : forall P x,             substitutionP x P (p_inact) (p_inact)
  | sub_send     : forall P x pt l e P' Q', substitutionP x P P' Q' -> substitutionP x P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x pt llb xs ys, length llb = length xs -> length llb = length ys -> SSortedNList llb -> 
  List.Forall2 (substitutionP x P) xs ys -> substitutionP x P (p_recv pt llb xs) (p_recv pt llb ys)
  | sub_ite       : forall P x e P1 P2 Q1 Q2, substitutionP x P P1 Q1 -> substitutionP x P P2 Q2 -> substitutionP x P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x y P' Q', x <> y -> fresh_in y P -> substitutionP x P P' Q' -> substitutionP x P (p_rec y P') (p_rec y Q')
  | sub_alpha     : forall P x P1 P2 Q1 Q2, alphaP P1 P2 -> alphaP Q1 Q2 -> substitutionP x P P1 Q1 -> substitutionP x P P2 Q2.
 (* | sub_alpha     : forall P x P' Q1 Q2, substitutionP (p_var x) P P' Q1 -> alphaP Q1 Q2 -> substitutionP (p_var x) P P' Q2. *)


Section substitutionP_ind_ref.
  
  Variable P : fin -> process -> process -> process -> Prop.
  Hypothesis P_var_is : forall Pr X, P X Pr (p_var X) Pr.
  Hypothesis P_var_not : forall Pr X Y, X <> Y -> P X Pr (p_var Y) (p_var Y).
  Hypothesis P_inact : forall Pr X, P X Pr p_inact p_inact.
  Hypothesis P_send : forall Pr X pt l e P' Q', P X Pr P' Q' -> P X Pr (p_send pt l e P') (p_send pt l e Q').
  Hypothesis P_recv : forall Pr X pt llb xs ys, length llb = length xs -> length llb = length ys -> SSortedNList llb 
                              -> List.Forall2 (P X Pr) xs ys -> P X Pr (p_recv pt llb xs) (p_recv pt llb ys).
  Hypothesis P_ite : forall Pr X e P1 P2 Q1 Q2, P X Pr P1 Q1 -> P X Pr P2 Q2 -> P X Pr (p_ite e P1 P2) (p_ite e Q1 Q2).
  Hypothesis P_rec : forall Pr X Y P1 Q1, X <> Y -> fresh_in Y Pr -> P X Pr P1 Q1 -> P X Pr (p_rec Y P1) (p_rec Y Q1).
  Hypothesis P_alpha : forall Pr X P1 P2 Q1 Q2, alphaP P1 P2 -> alphaP Q1 Q2 -> P X Pr P1 Q1 -> P X Pr P2 Q2.
  
  Fixpoint substitutionP_ind_ref (X : fin) (Pr P1 P2 : process) (a : substitutionP X Pr P1 P2) {struct a} : P X Pr P1 P2 :=
    match a with 
      | sub_var_is p x => P_var_is p x
      | sub_var_not p x y Hn => P_var_not p x y Hn
      | sub_inact p x => P_inact p x
      | sub_send p x pt l e P' Q' H => P_send p x pt l e P' Q' (substitutionP_ind_ref x p P' Q' H)
      | sub_recv p x pt llb xs ys Hbx Hby HSb Lxy => P_recv p x pt llb xs ys Hbx Hby HSb (Forall2_mono (substitutionP_ind_ref x p) xs ys Lxy)
      | sub_ite p x e p1 p2 q1 q2 H1 H2 => P_ite p x e p1 p2 q1 q2 (substitutionP_ind_ref x p p1 q1 H1) (substitutionP_ind_ref x p p2 q2 H2)
      | sub_rec p x y p1 q1 Hn Hfy Hsb => P_rec p x y p1 q1 Hn Hfy (substitutionP_ind_ref x p p1 q1 Hsb)
      | sub_alpha p x p1 p2 q1 q2 Hap Haq Hsb => P_alpha p x p1 p2 q1 q2 Hap Haq (substitutionP_ind_ref x p p1 q1 Hsb)  
    end.

End substitutionP_ind_ref.



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

