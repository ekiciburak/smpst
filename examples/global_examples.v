From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Definition PAlice: process := p_send "Bob" 0 (e_val(vnat 50)) (p_recv "Carol" [None; None; Some(p_inact)]).

Definition PBob: process := p_recv "Alice" [Some(p_send "Carol" 1 (e_val(vnat 100)) p_inact); None; None; Some(p_send "Carol" 1 (e_val(vnat 2)) p_inact)].

(* how do i access the variable x? *)
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

(* Projections *)
Example GABCProjTCarol: projectionC GABC "Carol" TCarol.
Proof.
  unfold GABC, TCarol.
  pcofix CIH0. pfold.
  specialize (proj_cont (upaco3 projection r) "Alice" "Bob" "Carol" [Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]); None; None; Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])])] [Some(snat, ltt_recv "Bob" [None; Some(snat, ltt_send "Alice" [None; None; Some(snat, ltt_end)])]); None; None; Some(snat, ltt_recv "Bob" [None; Some(snat, ltt_send "Alice" [None; None; Some(snat, ltt_end)])])] snat (ltt_recv "Bob" [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])])).
  intros H0. simpl in H0. apply H0. clear H0.
  discriminate. discriminate. discriminate. split. reflexivity. easy.
  split. reflexivity. split.
  constructor. pcofix CIH1. pfold.
  specialize (proj_in (upaco3 projection r0) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])]).
  intros H1. simpl in H1. apply H1. clear H1.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH2. pfold.
  specialize (proj_out (upaco3 projection r1) "Carol" "Alice" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)]).
  intros H2. simpl in H2. apply H2. clear H2.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH3. pfold.
  specialize (proj_end (upaco3 projection r2) gtt_end "Carol").
  intros H3. constructor. intros H4. inversion H4. easy. easy. easy. easy.
  split. reflexivity. split. constructor. pcofix CIH4. pfold.
  specialize (proj_in (upaco3 projection r0) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_send "Alice" [None; None; Some (snat, ltt_end)])]).
  intros H1. simpl in H1. apply H1. clear H1.
  discriminate. split. reflexivity. split. constructor. pcofix CIH5. pfold.
  specialize (proj_out (upaco3 projection r1) "Carol" "Alice" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)]).
  intros H2. simpl in H2. apply H2. clear H2.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH6. pfold.
  specialize (proj_end (upaco3 projection r2) gtt_end "Carol").
  intros H3. constructor. intros H4. inversion H4. easy. easy. easy. easy. easy.
  left. reflexivity.
Qed.

Example GABCProjTAlice: projectionC GABC "Alice" T'Alice.
Proof.
  unfold GABC, T'Alice.
  pcofix CIH0. pfold.
  specialize (proj_out (upaco3 projection r) "Alice" "Bob" [Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]); None; None; Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])])] [Some (snat, ltt_recv "Carol" [None; None; Some (snat, ltt_end)]); None; None;
      Some (snat, ltt_recv "Carol" [None; None; Some (snat, ltt_end)])]).
  intros H0. simpl in H0. apply H0. clear H0.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH1. pfold.
  specialize (proj_cont (upaco3 projection r0) "Bob" "Carol" "Alice" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some(snat, ltt_recv "Carol" [None; None; Some (snat, ltt_end)])] snat (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])).
  intros H1. simpl in H1. apply H1. clear H1.
  discriminate. discriminate. discriminate. easy. split. reflexivity. split.
  constructor. pcofix CIH2. pfold.
  specialize (proj_in (upaco3 projection r1) "Carol" "Alice" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)]).
  intros H2. simpl in H2. apply H2. clear H2.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH3. pfold.
  specialize (proj_end (upaco3 projection r2) gtt_end "Alice").
  intros H3. constructor. intros H4. inversion H4. easy. easy. easy. easy.
  right. left. reflexivity.
  split. reflexivity. split.
  constructor. pcofix CIH4. pfold.
  specialize (proj_cont (upaco3 projection r0) "Bob" "Carol" "Alice" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some(snat, ltt_recv "Carol" [None; None; Some (snat, ltt_end)])] snat (ltt_recv "Carol" [None; None; Some (snat, ltt_end)])).
  intros H1. simpl in H1. apply H1. clear H1.
  discriminate. discriminate. discriminate. easy. split. reflexivity. split.
  constructor. pcofix CIH5. pfold.
  specialize (proj_in (upaco3 projection r1) "Carol" "Alice" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)]).
  intros H2. simpl in H2. apply H2. clear H2.
  discriminate. split. reflexivity. split.
  specialize (proj_end (upaco3 projection r1) gtt_end "Alice").
  intros H3. constructor. pcofix CIH6. pfold. 
  specialize (proj_end (upaco3 projection r1) gtt_end "Alice").
  intros H4. constructor. intros H5. inversion H5. easy. easy. easy. easy.
  right. left. reflexivity. easy.
Qed.

Example GABCProjTBob: projectionC GABC "Bob" TBob.
Proof.
  unfold GABC, TBob.
  pcofix CIH0. pfold.
  specialize (proj_in (upaco3 projection r) "Alice" "Bob" [Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])]); None; None; Some (snat, gtt_send "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])])] [Some (snat, ltt_send "Carol" [None; Some (snat, ltt_end)]); None; None; Some (snat, ltt_send "Carol" [None; Some (snat, ltt_end)])]).
  intros H0. simpl in H0. apply H0. clear H0.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH1. pfold.
  specialize (proj_out (upaco3 projection r0) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_end)]).
  intros H1. simpl in H1. apply H1. clear H1.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH2. pfold.
  specialize (proj_cont (upaco3 projection r1) "Carol" "Alice" "Bob" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)] snat ltt_end).
  intros H2. simpl in H2. apply H2. clear H2.
  discriminate. discriminate. discriminate. easy. split. reflexivity. split.
  constructor. pcofix CIH3. pfold.
  specialize (proj_end (upaco3 projection r2) gtt_end "Bob").
  intros H3. constructor. intros H4. inversion H4. easy. easy. easy.
  right. right. left. reflexivity. easy.
  split. reflexivity. split.
  constructor. pcofix CIH4. pfold.
  specialize (proj_out (upaco3 projection r0) "Bob" "Carol" [None; Some (snat, gtt_send "Carol" "Alice" [None; None; Some (snat, gtt_end)])] [None; Some (snat, ltt_end)]).
  intros H4. simpl in H4. apply H4. clear H4.
  discriminate. split. reflexivity. split.
  constructor. pcofix CIH5. pfold.
  specialize (proj_cont (upaco3 projection r1) "Carol" "Alice" "Bob" [None; None; Some (snat, gtt_end)] [None; None; Some (snat, ltt_end)] snat ltt_end).
  intros H5. simpl in H5. apply H5. clear H5.
  discriminate. discriminate. discriminate. easy. split. reflexivity. split.
  constructor. pcofix CIH6. pfold.
  specialize (proj_end (upaco3 projection r2) gtt_end "Bob").
  intros H6. constructor. intros H7. inversion H7. easy. easy. easy.
  right. right. left. reflexivity. easy. easy.
Qed.

(* long specialize crashes VsCoq. what is the meaning of sort in proj_cont? need to write documentation *)