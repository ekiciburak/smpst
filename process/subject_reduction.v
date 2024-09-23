From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.
  
Lemma step_mon : monotone5 gttstep.
Admitted.

Lemma gttT_mon : monotone2 gttT.
Admitted.

Lemma projection_wfc_p : forall G l p q x4 x8 x9, 
        wfgC G ->
        wfC (ltt_recv q x4) ->
        projectionC G p (ltt_recv q x4) ->
        gttstepC G x8 q p l ->
        projectionC x8 p x9 ->
        wfC x9.
Admitted.

Lemma projection_wfc_q : forall G l p q x x8 x9,
        wfgC G ->
        wfC (ltt_send p x) ->
        projectionC G q (ltt_send p x) ->
        gttstepC G x8 q p l ->
        projectionC x8 q x9 ->
        wfC x9.
Admitted.

Lemma projection_wfc_r : forall G l p0 q s x x0 x6,
        wfgC G ->
        wfC x ->
        q <> s ->
        p0 <> s ->
        projectionC G s x ->
        gttstepC G x6 q p0 l ->
        projectionC x6 s x0 ->
        wfC x0.
Admitted.

Lemma _3_19_h : forall p q l G L1 L2 S T xs y,
  wfgC G ->
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

Lemma _3_19_1 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S,T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' p L /\ subtypeC T L.
Proof.
  intros.
  specialize(_a_29 G p q (ltt_send q LP) (ltt_recv p LQ) S T S' T' xs l H H0 H1 H2 H3 H4); intros.
  destruct H6. rename x into Gl. revert H H0 H1 H2 H3 H4 H5 H6.
  revert p q l G G' LP LQ S T S' T' xs.
  induction Gl using gtth_ind_ref; intros; try easy.
  - destruct H6. destruct H6. destruct H6. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10. destruct H11.
    inversion H6. subst.
    specialize(some_onth_implies_In n x G H15); intros.
    specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : list (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
               onth l lsg = Some (s', Gjk) /\
               projectionC Gjk p Tp /\
               subtypeC T Tp /\ projectionC Gjk q Tq /\ subtypeC T' Tq) /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option sort) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s)) lsg x0)) x); intros.
    destruct H14. specialize(H14 H9). clear H9 H16.
    specialize(H14 (Some G) H13). destruct H14; try easy.
    destruct H9. destruct H9. destruct H9. destruct H14. destruct H16.
    inversion H9. subst. 
    destruct H16. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H18. destruct H19.
    pinversion H5; try easy. subst.
    specialize(eq_trans H30 H14); intros. inversion H21. subst. 
    exists x5. split; try easy.
    apply step_mon.
  - destruct H7. destruct H7. destruct H7. destruct H7. destruct H8. destruct H9. destruct H10. destruct H11. destruct H12.
    inversion H7. subst.
    pinversion H1; try easy. 
    - subst. admit.
    - subst. 
      assert (exists n t, onth n ys0 = Some t). { admit. }
      destruct H14. destruct H14.
      assert (exists g, onth x2 xs = Some g). { admit. }
      
      
      
Admitted.

Lemma _3_19_2 : forall p q l G G' L1 L2 S T xs,
  wfgC G ->
  projectionC G q (ltt_recv p L1) -> 
  subtypeC (ltt_recv p xs) (ltt_recv p L1) ->
  onth l xs = Some (S, T) ->
  gttstepC G G' p q l -> 
  projectionC G' q L2 ->
  subtypeC T L2.
Admitted.

Lemma _3_19_3 : forall p q r l G G' L1 L2,
  wfgC G ->
  r <> p -> r <> q ->
  projectionC G r L1 ->
  gttstepC G G' p q l -> 
  projectionC G' r L2 -> 
  subtypeC L1 L2.
Proof.
  
Admitted.

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
    wfgC G ->
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
    inversion H0. subst. destruct H5. destruct H4.
    specialize(projection_cont_r G x6 q p0 l s x H H4 H1); intros.
    assert (q <> s). { 
      unfold InT in H1. simpl in H1. 
      specialize(Classical_Prop.not_or_and (s = q) False H2); intros. destruct H7.
      easy.
    }
    assert (p0 <> s). {
      unfold InT in H3. simpl in H3.
      specialize(Classical_Prop.not_or_and (s = p0) False H3); intros. destruct H8.
      easy.
    }
    specialize(H6 H7 H8). destruct H6.
    exists x0.
    split; try easy.
    apply tc_sub with (t := x); try easy.
    specialize(_3_19_3 q p0 s l G x6 x x0); intros.
    apply H9; try easy.
    assert (wfC x0). { 
        specialize(projection_wfc_r G l p0 q s x x0 x6); intros.
        apply H9; try easy.
        specialize(typable_implies_wfC H5). easy.
    } easy. 
  - inversion H0. subst. simpl in *.
    unfold InT in *. simpl in *.
    specialize(noin_cat_and q (flattenT M1) (flattenT M2) H2); intros.
    specialize(noin_cat_and p (flattenT M1) (flattenT M2) H3); intros.
    specialize(Classical_Prop.not_or_and (InT q M1) (InT q M2) H4); intros. destruct H8. 
    specialize(Classical_Prop.not_or_and (InT p M1) (InT p M2) H5); intros. destruct H10.
    constructor. apply IHM1 with (p := p) (q := q) (G := G) (l := l); try easy.
    apply IHM2 with (p := p) (q := q) (G := G) (l := l); try easy.
Qed.

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
      specialize(_3_19_2 q p l G G' x4); intros.
      specialize(projection_cont_p G G' p q l x4 H23 H30 H1); intros.
      destruct H34. exists x10. split; try easy.
      specialize(H33 x10 x0 x5 x1 H23 H1 H12 H21 H30 H34).
      apply _a24 with (S := x0); try easy.
      - apply tc_sub with (t := x5); try easy.
        assert (wfC x10). 
        {
          specialize(projection_wfc_p G l p q x4 G' x10); intros.
          apply H35; try easy. 
          specialize(typable_implies_wfC H3). easy.
        }
        easy.
      - apply sc_sub with (s := x2); try easy.
        apply expr_typ_multi with (e := e); intros; try easy.
        apply sstrans with (s2 := x9); try easy.
    - constructor.
      specialize(_3_19_1 q p l G G' x); intros.
      specialize(projection_cont_q G G' p q l x H23 H30 H5); intros.
      destruct H34. exists x10. split; try easy.
      specialize(H33 x10 x2 x3 H23 H5 H17 H30 H34).
      apply tc_sub with (t := x3); try easy.
      assert (wfC x10).
      {
        specialize(projection_wfc_q G l p q x G' x10); intros.
        apply H35; try easy.
        specialize(typable_implies_wfC H10). easy.
      }
      easy.
    - apply _3_21_3_helper with (p := p) (q := q) (G := G) (l := l); try easy.
      inversion H7. subst. easy.
      simpl in H6. specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H6); intros.
      destruct H33; try easy. 

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