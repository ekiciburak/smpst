From SST Require Import src.expressions process.processes process.typecheck type.global process.sessions process.substitution.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Definition PAlice: process := p_send "Bob" 0 (e_val(vnat 50)) (p_recv "Carol" [None; None; Some(p_inact)]).

Definition PBob: process := p_recv "Alice" [Some(p_send "Carol" 1 (e_val(vnat 100)) p_inact); None; None; Some(p_send "Carol" 1 (e_val(vnat 2)) p_inact)].

Definition PCarol: process := p_recv "Bob" [None; Some(p_send "Alice" 2 (e_succ(e_val(vnat 2))) p_inact)].

Definition TAlice: ltt := ltt_send "Bob" [Some(snat, ltt_recv "Carol" [None; None; Some(snat, ltt_end)])].

Definition T'Alice: ltt := ltt_send "Bob" [Some(snat, ltt_recv "Carol" [None; None; Some(snat, ltt_end)]); None; None; Some(snat, ltt_recv "Carol" [None; None; Some(snat, ltt_end)])].

Definition TBob: ltt := ltt_recv "Alice" [Some(snat, ltt_send "Carol" [None; Some(snat, ltt_end)]); None; None; Some(snat, ltt_send "Carol" [None; Some(snat, ltt_end)])].

Definition TCarol: ltt := ltt_recv "Bob" [None; Some(snat, ltt_send "Alice" [None; None; Some(snat, ltt_end)])].

Definition GABC: gtt := gtt_send "Alice" "Bob" [Some(snat, gtt_send "Bob" "Carol" [None; Some(snat, gtt_send "Carol" "Alice" [None; None; Some(snat, gtt_end)])]); None; None; Some(snat, gtt_send "Bob" "Carol" [None; Some(snat, gtt_send "Carol" "Alice" [None; None; Some(snat, gtt_end)])])].

(* TAlice is a subtype of T'Alice *)
(* do we have a lemma for subtyping receives and sends? *)
Example TAliceSubtype: subtypeC TAlice T'Alice.
Proof.
  unfold subtypeC, TAlice, T'Alice.
  pcofix CIH.
  pfold. constructor. constructor.
  apply srefl.
  constructor. constructor. pfold.
  apply sub_in. constructor. apply srefl.
  split. constructor. pfold. apply sub_end.
  constructor. constructor.
Qed.

Example PAliceTAlice: typ_proc [] [] PAlice TAlice.
Proof.
  unfold PAlice, TAlice.
  specialize (tc_send [] [] "Bob" 0 (e_val(vnat 50)) (p_recv "Carol" [None; None; Some p_inact]) snat (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])). intros. simpl in H. apply H. 
  apply sc_valn.
  apply tc_recv. easy. easy.
  apply Forall2_cons. left. easy.
  apply Forall2_cons. left. easy.
  apply Forall2_cons. right.
  exists p_inact, snat, ltt_end. split. easy. split. easy. apply tc_inact. easy.
Qed.

Example PCarolTCarol: typ_proc [] [] PCarol TCarol.
Proof.
  unfold PCarol, TCarol.
  specialize (tc_recv [] [] "Bob" [None; Some(snat, ltt_send "Alice" [None; None; Some(snat, ltt_end)])] [None; Some (p_send "Alice" 2 (e_succ (e_val (vnat 2))) p_inact)]).
  constructor. easy. easy.
  apply Forall2_cons. left. easy.
  apply Forall2_cons. right.
  exists (p_send "Alice" 2 (e_succ (e_val (vnat 2))) p_inact).
  exists snat. exists (ltt_send "Alice" [None; None; Some (snat, ltt_end)]). split. easy. split. easy.
  specialize (tc_send [Some snat] [] "Alice" 2 (e_succ (e_val (vnat 2))) p_inact snat ltt_end). intros H1. apply H1.
  constructor. constructor. constructor. easy.
Qed.

Example PBobTBob: typ_proc [] [] PBob TBob.
Proof.
  unfold PBob, TBob.
  specialize (tc_recv [] [] "Alice" [Some (snat, ltt_send "Carol" [None; Some (snat, ltt_end)]); None; None; Some (snat, ltt_send "Carol" [None; Some (snat, ltt_end)])] [Some (p_send "Carol" 1 (e_val (vnat 100)) p_inact); None; None; Some (p_send "Carol" 1 (e_val (vnat 2)) p_inact)]). intros. apply H. easy. easy.
  apply Forall2_cons. right.
  exists (p_send "Carol" 1 (e_val (vnat 100)) p_inact).
  exists snat.
  exists (ltt_send "Carol" [None; Some (snat, ltt_end)]).
  split. easy. split. easy.
  specialize (tc_send [Some snat] [] "Carol" 1 (e_val (vnat 100)) p_inact snat ltt_end). intros H1. apply H1.
  apply sc_valn. apply tc_inact.
  apply Forall2_cons. left. easy.
  apply Forall2_cons. left. easy.
  apply Forall2_cons. right.
  exists (p_send "Carol" 1 (e_val (vnat 2)) p_inact).
  exists snat.
  exists (ltt_send "Carol" [None; Some (snat, ltt_end)]).
  split. easy. split. easy.
  specialize (tc_send [Some snat] [] "Carol" 1 (e_val (vnat 2)) p_inact snat ltt_end).
  intros H1. simpl in H1.
  apply H1. apply sc_valn. apply tc_inact.
  easy.
Qed.

Lemma some_onth_implies_In: forall {A B: Type} n (lis: list (option (A*B))) a,
  onth n lis = Some a ->
  In (Some a) lis.
Proof. intros A B n lis.
       revert n.
       induction lis; intros.
       - case_eq n; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - simpl.
         case_eq n; intros.
         + subst. simpl in H. left. easy.
         + subst. simpl in H. right.
           apply IHlis with (n := n0). easy.
Qed.

Lemma isgParts_depth_exists : forall r Gl,
    isgParts r Gl -> exists n, isgParts_depth n r Gl.
Proof.
  induction Gl using global_ind_ref; intros; try easy.
  inversion H0.
  - subst. exists 0. constructor.
  - subst. exists 0. constructor.
  - subst.
    specialize(some_onth_implies_In n lis (s, g) H7); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (isgParts r g -> exists n : fin, isgParts_depth n r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1).
    destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
    specialize(H2 H8). destruct H2.
    exists (S x1). apply dpth_c with (s := x) (g := x0) (k := n); try easy.
  - inversion H. subst. specialize(IHGl H2). destruct IHGl. exists (S x). constructor. easy.
Qed.

Lemma isgParts_depth_back : forall G n r,
      isgParts_depth n r G -> isgParts r G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  inversion H0.
  - subst. constructor.
  - subst. constructor.
  - subst.
    specialize(some_onth_implies_In k lis (s, g) H8); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (n : fin) (r : string),
           isgParts_depth n r g -> isgParts r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1). destruct H2; try easy. destruct H. destruct H. destruct H.
    inversion H. subst.
    specialize(H2 n0 r H9).
    apply pa_sendr with (n := k) (s := x) (g := x0); try easy.
  inversion H. subst.
  - specialize(IHG n0 r H3). constructor. easy.
Qed.

Lemma subst_parts_helper : forall k0 xs s g0 r n0 lis m n g,
      onth k0 xs = Some (s, g0) ->
      isgParts_depth n0 r g0 ->
      Forall2
       (fun u v : option (sort * global) =>
        u = None /\ v = None \/
        (exists (s : sort) (g0 g' : global),
           u = Some (s, g0) /\ v = Some (s, g') /\ subst_global m n (g_rec g) g0 g')) xs lis ->
      Forall
      (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (m n k : fin) (r : string) (g0 g' : global),
           isgParts_depth k r g' -> subst_global m n (g_rec g0) g' g -> isgParts_depth k r g))) lis ->
      exists g', onth k0 lis = Some (s, g') /\ isgParts_depth n0 r g'.
Proof.
  induction k0; intros; try easy.
  - destruct xs; try easy.
    simpl in H. subst. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    clear H4 H7. destruct H5; try easy. destruct H. destruct H. destruct H. destruct H.
    destruct H1. inversion H. subst.
    destruct H3; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
    specialize(H3 m n n0 r g x0 H0 H2).
    exists x3. split; try easy.
  - destruct xs; try easy. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    specialize(IHk0 xs s g0 r n0 lis m n g). apply IHk0; try easy.
Qed.

Lemma subst_parts_depth : forall m n k r g g' Q,
      subst_global m n (g_rec g) g' Q ->
      isgParts_depth k r g' ->
      isgParts_depth k r Q.
Proof.
  intros. revert H0 H. revert m n k r g g'.
  induction Q using global_ind_ref; intros; try easy.
  inversion H.
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy.
  - inversion H. subst. inversion H0.
  - inversion H1. subst.
    inversion H0.
    - subst. constructor.
    - subst. constructor.
    - subst.
      specialize(subst_parts_helper k0 xs s g0 r n0 lis m n g H10 H11 H7 H); intros.
      destruct H2. destruct H2.
      apply dpth_c with (n := n0) (s := s) (g := x) (k := k0); try easy.
  - inversion H. subst. inversion H0.
  - subst. inversion H0. subst.
    constructor. specialize(IHQ m.+1 n.+1 n0 r g P). apply IHQ; try easy.
Qed.

Lemma part_break_s : forall G pt,
    isgPartsC pt G ->
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. pose proof H as H0.
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl.
  specialize(isgParts_depth_exists pt Gl H1); intros. destruct H2. rename x into n.

  clear H.
  clear H1.
  revert H2 H0. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H2. subst.
    exists (g_send pt q lis). split. easy. split. constructor. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. right. exists p. exists pt. exists lis. easy.
  - inversion H2. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H3 H1); intros.
    apply IHn with (Gl := Q); try easy.
    apply gttT_mon.
  - subst.
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy.
    right. exists p. exists q. exists lis. easy.
Qed.

Lemma ispartsend: forall p,
  isgPartsC p (gtt_end) -> False.
Proof. intros.
       specialize(part_break_s gtt_end p H); intro HH.
       destruct HH as (g, (Ha,(Hb,[Hc | (r,(s,(xs,Hxs)))]))).
       subst. inversion Hb.
       subst.
       pinversion Ha.
       apply gttT_mon.
Qed. 

(* Projections *)
Example GABCProjTCarol: projectionC GABC "Carol" TCarol.
Proof.
  unfold GABC, TCarol.
  pcofix CIH0. pfold.
  specialize (proj_cont (upaco3 projection r) "Alice" "Bob" "Carol" [Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]); None; None; Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])])]
  [Some(ltt_recv "Bob" [None; Some(snat, ltt_send "Alice" [None; None; Some(snat, ltt_end)])]); None; None; Some(ltt_recv "Bob" [None; Some(snat, ltt_send "Alice" [None; None; Some(snat, ltt_end)])])]).
  intros H0. simpl in H0. apply H0.
  discriminate. discriminate. discriminate.
  constructor. right.
  exists snat.
  exists (gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]).
  exists (ltt_recv "Bob" [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])]).
  split. reflexivity. split. reflexivity.
  constructor. pcofix CIH1. pfold.
  specialize (proj_in (upaco3 projection r0) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])]).
  intros H1. simpl in H1. apply H1.
  discriminate. constructor.
  left. split. reflexivity. reflexivity.
  constructor. right.
  exists snat.
  exists (gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)]).
  exists (ltt_send "Alice" [None; None; Some (snat, ltt_end)]).
  split. reflexivity.
  split. reflexivity.
  constructor. pcofix CIH2. pfold.
  constructor. discriminate.
  constructor. left. split. reflexivity. reflexivity.
  constructor. left. split. reflexivity. reflexivity.
  constructor. right.
  exists snat.
  exists gtt_end.
  exists ltt_end.
  split. reflexivity.
  split. reflexivity.
  constructor. pcofix CIH3. pfold.
  specialize proj_end.
  intros H2. simpl in H2. apply H2.
  apply ispartsend. (* this is admitted *)
  constructor. constructor. constructor.
  left. split. reflexivity. reflexivity.
  constructor.
  left. split. reflexivity. reflexivity.
  constructor.
  right.
  exists snat.
  exists (gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]).
  exists (ltt_recv "Bob" [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])]).
  split.
  reflexivity. split. reflexivity.
  constructor. pcofix CIH4. pfold.
  specialize (proj_in (upaco3 projection r0) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])]).
  intros H1. simpl in H1. apply H1.
  discriminate. constructor.
  left. split. reflexivity. reflexivity.
  constructor. right.
  exists snat.
  exists (gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)]).
  exists (ltt_send "Alice" [None; None; Some (snat, ltt_end)]).
  split. reflexivity. split. reflexivity.
  constructor. pcofix CIH5. pfold.
  specialize (proj_out (upaco3 projection r1) "Carol" "Alice" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)]).
  constructor. discriminate.
  constructor. left. split. reflexivity. reflexivity.
  constructor. left. split. reflexivity. reflexivity.
  constructor. right.
  exists snat.
  exists gtt_end.
  exists ltt_end.
  split. reflexivity. split. reflexivity.
  constructor. pcofix CIH6. pfold.
  specialize (proj_end (upaco3 projection r2) gtt_end "Carol").
  intro H2. apply H2.
  apply ispartsend.
  constructor. constructor. constructor.
  apply (mconss (ltt_recv "Bob" [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])])).
  constructor. constructor. constructor. constructor.
Qed. (* need to check size is the same *)

Example GABCProjTBob: projectionC GABC "Bob" TBob.
Proof.
  unfold GABC, TBob.
  pcofix CIH0. pfold.
  specialize (proj_in (upaco3 projection r) "Alice" "Bob" [Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]); None; None; Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])])] [Some (snat, ltt_send "Carol" [None; Some (snat, ltt_end)]); None; None; Some (snat, ltt_send "Carol" [None; Some (snat, ltt_end)])]).
  intros H0. simpl in H0. apply H0.
  discriminate. constructor. right.
  exists snat.
  exists (gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]).
  exists (ltt_send "Carol" [None; Some (snat, ltt_end)]).
  split. reflexivity. split. reflexivity. clear H0. 
  constructor. pcofix CIH1. pfold.
  specialize (proj_out (upaco3 projection r) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_end)]).
  intros H1. simpl in H1. apply H1.
  discriminate. constructor. left. easy.
  constructor. right.
  exists snat.
  exists (gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)]).
  exists ltt_end.
  split. reflexivity. split. reflexivity. clear H1.
  constructor. pcofix CIH2. pfold.
  specialize (proj_cont (upaco3 projection r) "Carol" "Alice" "Bob" [None; None; Some (snat, gtt_end)] [None; None; Some (ltt_end)] ltt_end).
  intros H2. simpl in H2. apply H2.
  discriminate. discriminate. discriminate.
  constructor. left. easy.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists gtt_end.
  exists ltt_end.
  split. reflexivity. split. reflexivity. clear H2.
  constructor. pcofix CIH3. pfold.
  specialize (proj_end (upaco3 projection r) gtt_end "Bob").
  intros H3. constructor.
  apply ispartsend.
  constructor. apply (mconsn ltt_end). apply (mconsn ltt_end). constructor.
  constructor. constructor. left. easy.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists (gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]).
  exists (ltt_send "Carol" [None; Some (snat, ltt_end)]).
  split. reflexivity.
  split. reflexivity.
  clear H0. constructor. pcofix CIH4. pfold.
  specialize (proj_out (upaco3 projection r) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_end)]).
  intros H4. simpl in H4. apply H4.
  discriminate.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists (gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)]).
  exists ltt_end.
  split. reflexivity. split. reflexivity.
  clear H4. constructor. pcofix CIH5. pfold.
  specialize (proj_cont (upaco3 projection r) "Carol" "Alice" "Bob" [None; None; Some (snat, gtt_end)] [None; None; Some (ltt_end)] ltt_end).
  intros H5. simpl in H5. apply H5.
  discriminate. discriminate. discriminate.
  constructor. left. easy.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists gtt_end.
  exists ltt_end.
  split. reflexivity. split. reflexivity.
  clear H5. constructor. pcofix CIH6. pfold.
  specialize (proj_end (upaco3 projection r) gtt_end "Bob").
  intros H6. constructor. apply ispartsend.
  constructor. apply (mconsn ltt_end). apply (mconsn ltt_end). constructor.
  constructor. constructor.
Qed.

Example GABCProjTAlice: projectionC GABC "Alice" T'Alice.
Proof.
  unfold GABC, T'Alice.
  pcofix CIH0. pfold.
  specialize (proj_out (upaco3 projection r) "Alice" "Bob" [Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]); None; None; Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])])] [Some (snat, ltt_recv "Carol" [None; None; Some (snat, ltt_end)]); None; None; Some (snat, ltt_recv "Carol" [None; None; Some (snat, ltt_end)])]).
  intros H0. simpl in H0. apply H0.
  discriminate.
  constructor. right.
  exists snat.
  exists (gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]).
  exists (ltt_recv "Carol" [None; None; Some (snat, ltt_end)]).
  split. reflexivity.
  split. reflexivity.
  clear H0.
  constructor. pcofix CIH1. pfold.
  specialize (proj_cont (upaco3 projection r) "Bob" "Carol" "Alice" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])] (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])).
  intros H1. apply H1.
  discriminate. discriminate. discriminate.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists (gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)]).
  exists (ltt_recv "Carol" [None; None; Some (snat, ltt_end)]).
  split. reflexivity.
  split. reflexivity.
  clear H1.
  constructor. pcofix CIH2. pfold.
  specialize (proj_in (upaco3 projection r) "Carol" "Alice" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)]).
  intros H2. apply H2.
  discriminate.
  constructor. left. easy.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists gtt_end.
  exists ltt_end.
  split. reflexivity. split. reflexivity.
  clear H2.
  constructor. pcofix CIH3. pfold.
  constructor.
  apply ispartsend.
  constructor.
  constructor.
  apply mconsn.
  constructor.
  constructor. left. easy.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists (gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]).
  exists (ltt_recv "Carol" [None; None; Some (snat, ltt_end)]).
  split. reflexivity.
  split. reflexivity.
  clear H0.
  constructor. pcofix CIH3. pfold.
  specialize (proj_cont (upaco3 projection r) "Bob" "Carol" "Alice" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])] (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])).
  intros H3. apply H3.
  discriminate. discriminate. discriminate.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists (gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)]).
  exists (ltt_recv "Carol" [None; None; Some (snat, ltt_end)]).
  split. reflexivity.
  split. reflexivity.
  clear H3.
  constructor. pcofix CIH4. pfold.
  constructor.
  discriminate.
  constructor. left. easy.
  constructor. left. easy.
  constructor. right.
  exists snat.
  exists gtt_end.
  exists ltt_end.
  split. reflexivity.
  split. reflexivity.
  constructor. pcofix CIH5. pfold.
  constructor.
  apply ispartsend.
  constructor.
  constructor. constructor. constructor.
  constructor.
Qed.