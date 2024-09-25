From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection type.proj_sub.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.
  



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



Lemma _3_21_3_helper : forall M p q G G' l L1 L2 S T xs y,
    wfgC G ->
    projectionC G p (ltt_send q L1) -> 
    subtypeC (ltt_send q (extendLis l (Datatypes.Some(S, T)))) (ltt_send q L1) ->
    projectionC G q (ltt_recv p L2) -> 
    onth l xs = Some y ->
    ForallT
       (fun (u : string) (P : process) =>
        exists T : ltt, projectionC G u T /\ typ_proc nil nil P T) M ->
    subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
    gttstepC G G' p q l ->
    ~ InT q M ->
    ~ InT p M ->
    ForallT
      (fun (u : string) (P : process) =>
       exists T : ltt, projectionC G' u T /\ typ_proc nil nil P T) M.
Proof.
  intro M. induction M; intros; try easy.
  - unfold InT in *. simpl in H7. simpl in H8.
    specialize(Classical_Prop.not_or_and (s = q) False H7); intros. destruct H9.
    specialize(Classical_Prop.not_or_and (s = p0) False H8); intros. destruct H11.
    clear H10 H12 H7 H8.
    constructor.
    inversion H4. subst. destruct H8 as [T' H8]. destruct H8.
    assert(exists T, projectionC G' s T /\ subtypeC T' T).
    {
      admit.
    } 
    destruct H10. destruct H10.
    exists x. split; try easy. apply tc_sub with (t := T'); try easy.
    admit. (* wfC *)
  - inversion H4. subst.
    specialize(noin_cat_and q (flattenT M1) (flattenT M2) H7); intros.
    specialize(noin_cat_and p (flattenT M1) (flattenT M2) H8); intros.
    specialize(Classical_Prop.not_or_and (In q (flattenT M1)) (In q (flattenT M2)) H9); intros.
    specialize(Classical_Prop.not_or_and (In p (flattenT M1)) (In p (flattenT M2)) H10); intros.
    destruct H13. destruct H14.
    unfold InT in *.
    specialize(IHM1 p q G G' l L1 L2 S T xs y H H0 H1 H2 H3 H11 H5 H6 H13 H14).
    specialize(IHM2 p q G G' l L1 L2 S T xs y H H0 H1 H2 H3 H12 H5 H6 H15 H16).
    constructor; try easy.
Admitted.



Lemma _3_21_helper : forall l xs x1 y,
    onth l xs = Some y ->
    Forall2
        (fun (u : option process) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\
            v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t)) xs x1 ->
    exists s t, onth l x1 = Some(s,t) /\ typ_proc (Some s :: nil) nil y t.
Proof.
  induction l; intros.
  - destruct xs; try easy.
    destruct x1; try easy.
    simpl in *.
    inversion H0. subst. destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. 
    inversion H. subst.
    exists x0. exists x2. split; try easy.
  - destruct xs; try easy.
    destruct x1; try easy. 
    inversion H0. subst. apply IHl with (xs := xs); try easy.
Qed.

Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst. rename H4 into H100. rename H5 into H101. rename H6 into H102. rename H7 into H103.
  rename H8 into H4. clear H1. inversion H3. subst. clear H3.
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
  - specialize(_a_29 G q p (ltt_send p x) (ltt_recv q x4) x2 x3); intros.
    specialize(_3_21_helper l xs x1 y H H13); intros.
    destruct H21. destruct H21. destruct H21. 
    specialize(H20 x0 x5 x1 l).
    assert (wfgC G). 
    {
      unfold wfgC. exists Gl; try easy.
    }
    specialize(H20 H23 H5 H17 H1 H21 H12).
    destruct H20. destruct H20. destruct H20. destruct H20. destruct H20. destruct H24. destruct H25. destruct H26. destruct H27.
    destruct H28.
    
  - specialize(_3_19_h q p l G x x4 x2 x3 x1 (x0, x5) H23 H5 H17 H1 H21 H12); intros.
    destruct H30. rename x10 into G'.
    exists G'.
    assert(multiC G G').
    apply multiC_step with (G2 := G') (p := q) (q := p) (n := l). easy. apply multiC_refl.
    split; try easy.
    specialize(wfgC_after_step G G' q p l H23 H30); intros.
    unfold wfgC in H32. destruct H32. rename x10 into Gl0.
    apply t_sess with (Gl := Gl0); intros; try easy.
    - apply H2; try easy.
      admit. (* participant after gttstep is participant before step *)
    - simpl in *.
      constructor; try easy.
    constructor. constructor. 
    - constructor.
      specialize(_3_19_2 q p l G G' x x4 x2 x3 x0 x5 x1 H23 H5 H17 H1 H21 H12 H30); intros.
      destruct H33. destruct H33. exists x10. split; try easy.
      apply _a24 with (S := x0); try easy.
      - apply tc_sub with (t := x5); try easy.
        assert (wfC x10). 
        {
          admit.
          (* apply H35; try easy. 
          specialize(typable_implies_wfC H3). easy. *)
        }
        easy.
      - apply sc_sub with (s := x2); try easy.
        apply expr_typ_multi with (e := e); intros; try easy.
        apply sstrans with (s2 := x9); try easy.
    - constructor.
      specialize(_3_19_1 q p l G G' x x4 x2 x3 x0 x5 x1 H23 H5 H17 H1 H21 H12 H30); intros.
      destruct H33. destruct H33. exists x10. split; try easy.
      - apply tc_sub with (t := x3); try easy.
        assert (wfC x10).
        {
          admit.
         (*  specialize(projection_wfc_q G l p q x G' x10); intros.
          apply H35; try easy.
          specialize(typable_implies_wfC H10). easy. *)
        }
        easy.
    - specialize(_3_21_3_helper M q p G G' l x x4 x2 x3 x1 (x0, x5)); intros.
      apply H33; try easy.
      simpl in H6. specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H6); intros.
      destruct H34; try easy. unfold InT. 
      inversion H7. subst. easy.

  (* T-COND *)
  inversion H0. subst. rename H3 into H100. rename H4 into H101. rename H5 into H102. rename H6 into H103. rename H7 into H3. 
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
  inversion H0. subst. rename H3 into H100. rename H4 into H101. rename H5 into H102. rename H6 into H103. rename H7 into H3.
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