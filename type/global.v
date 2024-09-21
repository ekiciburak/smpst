From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header.
Require Import List String Coq.Arith.PeanoNat Relations. 
Import ListNotations. 

Notation part := string (only parsing).
Notation label := nat (only parsing).

Section gtt.

(* global session trees *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (option (sort*gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.


Inductive global  : Type :=
  | g_var : fin -> global 
  | g_end : global 
  | g_send : part -> part -> list (option (sort * global)) -> global 
  | g_rec : global -> global.
  
Section global_ind_ref.
  Variable P : global -> Prop.
  Hypothesis P_var : forall n, P (g_var n).
  Hypothesis P_end : P (g_end).
  Hypothesis P_send : forall p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (g_send p q lis).
  Hypothesis P_rec : forall g, P g -> P (g_rec g).
  
  Fixpoint global_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_var.
    - apply P_end.
    - apply P_send.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s1. exists g. split; try easy.
      left. easy.
    - apply P_rec. easy.
  Qed.
End global_ind_ref.


Fixpoint incr_freeG (fv m : fin) (G : global) := 
  match G with 
    | g_var n        => g_var (if fv <= n then (n + m) else n)
    | g_end          => g_end 
    | g_send p q lis => g_send p q (map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeG fv m g)
            | None        => None
          end) lis)
    | g_rec g        => g_rec (incr_freeG (S fv) m g)
  end.

Inductive subst_global : fin -> fin -> global -> global -> global -> Prop := 
  | subg_var_is   : forall G t m,                            subst_global t m G (g_var t) (incr_freeG 0 m G)
  | subg_var_notz : forall G t m, t <> 0 ->                  subst_global t m G (g_var 0) (g_var 0)
  | subg_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_global t m G (g_var (S t')) (g_var (t'))
  | subg_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_global t m G (g_var (S t')) (g_var (S t'))
  | subg_end      : forall G t m,                            subst_global t m G g_end g_end
  | subg_send     : forall G t m p q xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_global t m G g g')
                                                  ) xs ys -> subst_global t m G (g_send p q xs) (g_send p q ys)
  | subg_rec      : forall G t m P Q, subst_global (S t) (S m) G P Q -> subst_global t m G (g_rec P) (g_rec Q). 


Inductive betaG : relation global := 
  | lttS : forall G G', subst_global 0 0 (g_rec G) G G' -> betaG (g_rec G) G'.

Inductive gttT (R : global -> gtt -> Prop) : global -> gtt -> Prop := 
  | gttT_end  : gttT R g_end gtt_end
  | gttT_send : forall p q xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> gttT R (g_send p q xs) (gtt_send p q ys)
  | gttT_rec  : forall G Q G', subst_global 0 0 (g_rec G) G Q -> R Q G' -> gttT R (g_rec G) G'.

Definition gttTC G G' := paco2 gttT bot2 G G'.

Inductive wfG : global -> Prop := 
  | wfg_var : forall n, wfG (g_var n)
  | wfg_end : wfG g_end
  | wfg_send : forall p q lis, SList lis -> p <> q -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) lis -> wfG (g_send p q lis)
  | wfg_rec : forall g, wfG g -> wfG (g_rec g).

Inductive guardG : fin -> fin -> global -> Prop :=  
  | gg_nil : forall m G, guardG 0 m G
  | gg_end : forall n m, guardG n m g_end
  | gg_send : forall n m p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardG n m g)) lis -> guardG (S n) m (g_send p q lis)
  | gg_rec : forall n m g Q, subst_global 0 0 (g_rec g) g Q -> guardG n m Q -> guardG n (S m) (g_rec g).



Lemma guardL_more : forall n m k G, guardG n m G -> m <= k -> guardG n k G.
Proof.
  induction n; intros; try easy.
  - apply gg_nil.
  - revert IHn H H0. revert n k G. induction m; intros; try easy.
    inversion H. subst. 
    - apply gg_end.
    - subst. apply gg_send; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - destruct G.
      - inversion H.
      - apply gg_end.
      - apply gg_send.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gg_send. easy.
      - inversion H. subst.
        destruct k; try easy.
        apply gg_rec with (Q := Q); try easy.
        apply IHm; try easy.
Qed.

CoFixpoint Ga : gtt := gtt_send "Alice" "Bob" [Some (snat, Ga)].

Example Grec : gttTC (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])) Ga.
Proof.
  pcofix CIH.
  pfold. apply gttT_rec with (Q := g_send "Alice" "Bob" [(Some (snat, (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)]))))]).
  constructor. constructor. right.
  exists snat. exists (g_var 0). exists (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])).
  split; try easy. split; try easy. constructor. easy.
  
  rewrite (gtt_eq Ga). simpl.
  left. pfold.
  constructor. constructor. right. exists snat. exists (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])). exists Ga.
  split; try easy. split; try easy.
  right. easy. easy.
Qed.
  

End gtt.







