From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.

Lemma projection_cont_p : forall G x6 p q l x,
    gttstepC G x6 q p l -> projectionC G p (ltt_recv q x) -> exists T, projectionC x6 p T.
Proof.
  
  
Admitted.

Lemma projection_cont_q : forall G x6 p q l x0,
    gttstepC G x6 q p l -> projectionC G q (ltt_send p x0) -> exists T, projectionC x6 q T.
Admitted.

Lemma projection_cont_r : forall G x6 q p0 l s x,
    projectionC G s x ->
    gttstepC G x6 q p0 l -> 
    q <> s ->
    p0 <> s ->
    exists T, projectionC x6 s T.
Admitted.

Lemma projection_wfc_p : forall G l p q x4 x8 x9, 
        wfC (ltt_recv q x4) ->
        projectionC G p (ltt_recv q x4) ->
        gttstepC G x8 q p l ->
        projectionC x8 p x9 ->
        wfC x9.
Admitted.

Lemma projection_wfc_q : forall G l p q x x8 x9,
        wfC (ltt_send p x) ->
        projectionC G q (ltt_send p x) ->
        gttstepC G x8 q p l ->
        projectionC x8 q x9 ->
        wfC x9.
Admitted.

Lemma projection_wfc_r : forall G l p0 q s x x0 x6,
        wfC x ->
        q <> s ->
        p0 <> s ->
        projectionC G s x ->
        gttstepC G x6 q p0 l ->
        projectionC x6 s x0 ->
        wfC x0.
Admitted.

Lemma _3_19_h : forall p q l G L1 L2 S T xs y,
  projectionC G p (ltt_send q L1) -> 
  subtypeC (ltt_send q (extendLis l (Datatypes.Some(S,T)))) (ltt_send q L1) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l xs = Some y ->
  subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
  exists G', gttstepC G G' p q l.
Proof.
  intros. 
  pinversion H0. subst.
  pinversion H1; subst; try easy.
  - admit.
  - admit.
Admitted.

Lemma _3_19_1 : forall p q l G G' L1 L2 S T,
  projectionC G p (ltt_send q L1) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S,T)))) (ltt_send q L1) ->
  gttstepC G G' p q l ->
  projectionC G' p L2 ->
  subtypeC T L2.
Admitted.

Lemma _3_19_2 : forall p q l G G' L1 L2 S T xs,
  projectionC G q (ltt_recv p L1) -> 
  subtypeC (ltt_recv p xs) (ltt_recv p L1) ->
  onth l xs = Some (S, T) ->
  gttstepC G G' p q l -> 
  projectionC G' q L2 ->
  subtypeC T L2.
Admitted.

Lemma _3_19_3 : forall p q r l G G' L1 L2,
  r <> p -> r <> q ->
  projectionC G r L1 ->
  gttstepC G G' p q l -> 
  projectionC G' r L2 -> 
  subtypeC L1 L2.
Proof.
  
Admitted.

Lemma onth_follow : forall l xs y x1,
  onth l xs = Some y ->
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t))
       xs x1 ->
  exists s t, onth l x1 = Some (s, t).
Proof.
  induction l; intros; try easy.
  destruct xs; subst. easy.
  inversion H0; subst. clear H0. simpl in *. subst. 
  - destruct H3. easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. inversion H0. subst.
    exists x0. exists x1. easy.
  - destruct xs. easy.
    destruct x1; try easy.
    simpl in *.
    inversion H0. subst. clear H0. apply IHl with (xs := xs) (y := y); try easy.
Qed.

Lemma _3_21_1_helper : forall l x1 xs x4 x5 y,
    onth l x1 = Some (x4, x5) ->
    onth l xs = Some y ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t))
       xs x1 ->
    typ_proc (Some x4 :: nil) nil y x5.
Proof.
  induction l; intros; try easy.
  - destruct x1. try easy. destruct xs. try easy.
    simpl in *. subst.
    inversion H1. subst. destruct H3. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. inversion H0. subst. easy.
  - destruct x1; try easy. destruct xs; try easy.
    simpl in *. apply IHl with (x1 := x1) (xs := xs); try easy.
    inversion H1; try easy.
Qed.

Lemma noin_cat_and {A} : forall pt (l1 l2 : list A), ~ In pt (l1 ++ l2) -> ~ (In pt l1 \/ In pt l2).
Proof.
  induction l1; intros; try easy.
  simpl in *. apply Classical_Prop.and_not_or. split; try easy.
  simpl in *. specialize(Classical_Prop.not_or_and (a = pt) (In pt (l1 ++ l2)) H); intros.
  destruct H0. 
  apply Classical_Prop.and_not_or.
  specialize(IHl1 l2 H1).
  specialize(Classical_Prop.not_or_and (In pt l1) (In pt l2) IHl1); intros. destruct H2.
  split; try easy. apply Classical_Prop.and_not_or. split; try easy.
Qed.

Lemma _3_21_3_helper : forall M p q x6 G l,
    ForallT
       (fun (u : string) (P : process) =>
        exists T : ltt, projectionC G u T /\ typ_proc nil nil P T) M ->
    gttstepC G x6 q p l ->
    ~ InT q M ->
    ~ InT p M ->
    ForallT
      (fun (u : string) (P : process) =>
       exists T : ltt, projectionC x6 u T /\ typ_proc nil nil P T) M.
Proof.
  intro M. induction M; intros; try easy.
  - constructor; try easy.
    inversion H. subst. destruct H4. destruct H3.
    specialize(projection_cont_r G x6 q p0 l s x H3 H0); intros.
    assert (q <> s). { 
      unfold InT in H1. simpl in H1. 
      specialize(Classical_Prop.not_or_and (s = q) False H1); intros. destruct H6.
      easy.
    }
    assert (p0 <> s). {
      unfold InT in H2. simpl in H2.
      specialize(Classical_Prop.not_or_and (s = p0) False H2); intros. destruct H7.
      easy.
    }
    specialize(H5 H6 H7). destruct H5.
    exists x0.
    split; try easy.
    apply tc_sub with (t := x); try easy.
    specialize(_3_19_3 q p0 s l G x6 x x0); intros.
    apply H8; try easy.
    assert (wfC x0). { 
        specialize(projection_wfc_r G l p0 q s x x0 x6); intros.
        apply H8; try easy.
        specialize(typable_implies_wfC H4). easy.
    } easy. 
  - inversion H. subst. simpl in *.
    unfold InT in *. simpl in *.
    specialize(noin_cat_and q (flattenT M1) (flattenT M2) H1); intros.
    specialize(noin_cat_and p (flattenT M1) (flattenT M2) H2); intros.
    specialize(Classical_Prop.not_or_and (InT q M1) (InT q M2) H3); intros. destruct H7. 
    specialize(Classical_Prop.not_or_and (InT p M1) (InT p M2) H4); intros. destruct H9.
    constructor. apply IHM1 with (p := p) (q := q) (G := G) (l := l); try easy.
    apply IHM2 with (p := p) (q := q) (G := G) (l := l); try easy.
Qed.

Lemma _3_21_ssort_helper : forall l x x2 x3,
      Forall2R
        (fun u v : option (sort * ltt) =>
         u = None \/
         (exists (s s' : sort) (t t' : ltt),
            u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
        (extendLis l (Some (x2, x3))) x ->
      exists y z, onth l x = (Some (y, z)) /\ subsort x2 y.
Proof.
  induction l; intros; try easy.
  - destruct x; try easy. simpl in *.
    destruct o. destruct p. exists s. exists l. split; try easy.
    inversion H. subst. destruct H3; try easy. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    inversion H0. inversion H1. subst. easy.
    inversion H. subst. destruct H3; try easy.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. easy.
  - destruct x; try easy. simpl in *.
    inversion H. subst. apply IHl with (x3 := x3); try easy.
Qed.

Lemma _3_21_ssort_helper2 : forall G p q x x8,
      projectionC G p (ltt_recv q x8) ->
      projectionC G q (ltt_send p x) ->
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s,t) /\ v = Some(s,t'))) x8 x.
Proof.
  
Admitted.


Lemma gttstep_wfc : forall G x8 q p l,
    wfgC G ->
    gttstepC G x8 q p l -> 
    wfgC x8.
Proof.
    intros.
Admitted.

Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst. rename H4 into H100. rename H5 into H101. rename H6 into H102.
  rename H7 into H4. clear H1. inversion H3. subst. clear H3.
  inversion H4. subst. clear H4. inversion H5. subst. clear H5.
  - inversion H4. subst. destruct H3. destruct H1. inversion H9. subst. destruct H10. destruct H5. 
  - specialize(_a23_a q xs (p_recv q xs) nil nil x H3 (eq_refl (p_recv q xs))); intros.
    destruct H11. destruct H11. destruct H12. destruct H13. 
  - specialize(_a23_bf p l e Q (p_send p l e Q) nil nil x0 H10 (eq_refl (p_send p l e Q))); intros.
    destruct H15. destruct H15. destruct H15. destruct H16.
  - specialize(subtype_recv x q x1 H12); intros.
    destruct H18. subst.
    specialize(subtype_recv_inv q x1 x4 H12); intros.
    specialize(subtype_send x0 p (extendLis l (Some (x2, x3))) H17); intros.
    destruct H19. subst.
    specialize(subtype_send_inv p (extendLis l (Some (x2, x3))) x H17); intros.
    specialize(_3_21_ssort_helper l x x2 x3 H19); intros.
    destruct H20. destruct H20. destruct H20.
  specialize(onth_follow l xs y x1 H H13); intros. destruct H22. destruct H22.
  specialize(_3_19_h q p l G x x4 x2 x3 x1 (x6, x7) H5 H17 H1 H22 H12); intros. 
  destruct H23. exists x8.
  split.
  specialize(wfgC_after_step G x8 q p l H23); intros. unfold wfgC in H24. (* flagged pf *)
  destruct H24 as [G' H105].
  apply t_sess with (Gl := G'); intros; try easy. 
  - apply H2; try easy. 
    admit.
  - simpl in *. constructor. simpl.
    apply Classical_Prop.and_not_or.
    specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H6); intros. destruct H20.
    split; try easy. easy.
  constructor. constructor. constructor.
  - specialize(_3_19_2 q p l G x8); intros.
    specialize(projection_cont_p G x8 p q l x4 H23 H1); intros.
    destruct H25. 
    specialize(H24 x4 x9 x6 x7 x1 H1 H12 H22 H23 H25). 
    exists x9. split; try easy.
    apply _a24 with (S := x6); try easy.
    apply tc_sub with (t := x7); intros; try easy.
    apply _3_21_1_helper with (l := l) (x1 := x1) (xs := xs); try easy.
    assert(wfC x9). { 
        specialize(projection_wfc_p G l p q x4 x8 x9); intros.
        apply H26; try easy.
        specialize(typable_implies_wfC H3). easy.
    } 
    easy.
    assert(subsort x2 x6). { 
      apply sstrans with (s2 := x0); try easy.
      specialize(_3_21_ssort_helper2 G p q x x4 H1 H5); intros.
      admit.
    }
    apply sc_sub with (s := x2); try easy.
    apply expr_typ_multi with (e := e); try easy.
  - specialize(_3_19_1 q p l G x8 x); intros.
    specialize(projection_cont_q G x8 p q l x H23 H5); intros.
    destruct H25.
    specialize(H24 x9 x2 x3 H5 H17 H23 H25).
    constructor. exists x9. split; try easy.
    apply tc_sub with (t := x3); try easy.
    assert(wfC x9). { 
          specialize(projection_wfc_q G l p q x x8 x9); intros.
          apply H26; try easy.
          specialize(typable_implies_wfC H10). easy.
    } 
    easy.
  - apply _3_21_3_helper with (p := p) (q := q) (G := G) (l := l); try easy.
    inversion H7. subst. easy.
    simpl in H6. specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H6); intros. 
    destruct H20; try easy.
  
  apply multiC_step with (G2 := x8) (p := q) (q := p) (n := l). easy. apply multiC_refl.
  
  (* T-COND *)
  inversion H0. subst. rename H3 into H100. rename H4 into H101. rename H5 into H102. rename H6 into H3. 
  inversion H3. subst. clear H3.
  inversion H6. subst. clear H6. destruct H4. destruct H3. 
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H4 (eq_refl (p_ite e P Q))); intros.
  destruct H5. destruct H5. destruct H5. destruct H6. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess with (Gl := Gl); try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H4); try easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. rename H3 into H100. rename H4 into H101. rename H5 into H102. rename H6 into H3. 
  inversion H3. subst. clear H3.
  inversion H6. subst. clear H6. destruct H4. destruct H3. 
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H4 (eq_refl (p_ite e P Q))); intros.
  destruct H5. destruct H5. destruct H5. destruct H6. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess with (Gl := Gl); try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H4); try easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(_a22_2 M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(_a22_2 M2' M2 x H4 H0); intros. easy.
  
Admitted.