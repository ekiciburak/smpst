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

Lemma ispartsend: forall p, isgPartsC p gtt_end -> False.
Proof.
  intros. inversion H. destruct H0. inversion H1. Admitted.

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