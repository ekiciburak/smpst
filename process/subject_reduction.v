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

(* 
Lemma ltt_after_betaL : forall G G' T,
  lttTC G T -> multiS betaL G G' -> lttTC G' T.
Proof.
  intros. revert H. revert T. induction H0; intros; try easy.
  inversion H. subst. pfold. 
  pinversion H0; try easy. subst.
  specialize(subst_injL 0 0 (l_rec G) G y Q H3 H1); intros. subst. easy.
  apply lttT_mon.
  apply IHmultiS.
  inversion H. subst. 
  pinversion H1. subst.
  specialize(subst_injL 0 0 (l_rec G) G y Q H4 H2); intros. subst. pfold. easy.
  apply lttT_mon.
Qed.

Lemma wfL_after_betaL : forall G G',
  wfL G -> multiS betaL G G' -> wfL G'.
Admitted.

Lemma wfC_implies_SList_recv : forall LQ q,
  wfC (ltt_recv q LQ) -> SList LQ.
Proof.
  intro LQ. 
  induction LQ; intros; try easy.
  - unfold wfC in H. destruct H. destruct H. destruct H0.
    pinversion H; try easy. subst. destruct xs; try easy.
    inversion H0. subst. easy.
    subst.
    specialize(guard_break G H1); intros. destruct H4.
    destruct H4. destruct H5.
    specialize(ltt_after_betaL (l_rec G) x (ltt_recv q [])); intros.
    assert (lttTC x (ltt_recv q [])). apply H7; try easy. pfold. easy.
    destruct H6.
    - subst. pinversion H8. apply lttT_mon.
    - destruct H6. destruct H6. destruct H6. 
      pinversion H8. subst. inversion H10. subst. inversion H11.
      apply lttT_mon.
    - subst. pinversion H8; try easy. subst.
    
Admitted. *)

Lemma wfC_recv :  forall [l LQ SL' TL' q],
        wfC (ltt_recv q LQ) -> 
        onth l LQ = Some (SL', TL') -> 
        wfC TL'.
Proof.  
  intros.
  unfold wfC in *.
  destruct H. rename x into T. destruct H. destruct H1.
  pinversion H; try easy. subst.
  assert(exists T, onth l xs = Some(SL', T) /\ lttTC T TL').
  {
    revert H5 H0. clear H2 H1 H. clear q. revert xs TL' SL' LQ.
    induction l; intros.
    - destruct LQ; try easy. destruct xs; try easy.
      inversion H5. subst. clear H5. simpl in H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst.
      simpl in *. exists x0. pclearbot. easy.
    - destruct LQ; try easy. destruct xs; try easy.
      inversion H5. subst. specialize(IHl xs TL' SL' LQ H6). apply IHl; try easy.
  }
  destruct H3. destruct H3. rename x into T. exists T. split; try easy.
  inversion H1. subst.
  
Admitted.

Lemma wfC_send : forall [l LP SL TL p],
        wfC (ltt_send p LP) -> 
        onth l LP = Some (SL, TL) -> 
        wfC TL.
Admitted.




Lemma _3_19_3_helper : forall M p q G G' l L1 L2 S T xs y,
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

Lemma _3_21_helper_1 : forall [l LQ SL' TL' x x1 x0 q],
        onth l LQ = Some (SL', TL') -> 
        onth l x = Some (x0, x1) ->
        subtypeC (ltt_recv q x) (ltt_recv q LQ) ->
        subtypeC x1 TL' /\ subsort SL' x0.
Proof.
  intros.
  specialize(subtype_recv_inv q x LQ H1); intros.
  clear H1. revert H2 H0 H. revert q x0 x1 x TL' SL' LQ.
  induction l; intros.
  - destruct x; try easy. destruct LQ; try easy. simpl in *. subst.
    inversion H2. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
    destruct H. destruct H. destruct H0. destruct H1. inversion H. inversion H0. subst. easy.
  - destruct LQ; try easy. destruct x; try easy. 
    inversion H2. subst.
    specialize(IHl q x0 x1 x TL' SL' LQ). apply IHl; try easy.
Qed.

Lemma _3_21_helper_2 : forall [l LP SL TL LT S p],
       subtypeC (ltt_send p (extendLis l (Some (S, LT)))) (ltt_send p LP) ->
       onth l LP = Some (SL, TL) -> 
       subtypeC LT TL /\ subsort S SL.
Proof.
  intros.
  specialize(subtype_send_inv p (extendLis l (Some (S, LT))) LP H); intros.
  clear H. revert H0 H1. revert LP SL TL LT S p.
  induction l; intros.
  - destruct LP; try easy. inversion H1. subst.
    destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
    destruct H2. destruct H3. inversion H. simpl in H0. subst. inversion H2. subst.
    easy.
  - destruct LP; try easy. inversion H1. subst.
    specialize(IHl LP SL TL LT S p). apply IHl; try easy.
Qed. 


Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H7. subst. clear H7. inversion H10. subst. clear H10. clear H1.
    destruct H6. destruct H1. destruct H7. destruct H6. rename x into T. rename x0 into T'.
    - specialize(_a23_a q xs (p_recv q xs) nil nil T H5 (eq_refl (p_recv q xs))); intros. 
      destruct H8. destruct H8. destruct H10. destruct H11.
    - specialize(_a23_bf p l e Q (p_send p l e Q) nil nil T' H7 (eq_refl (p_send p l e Q))); intros.
      destruct H13. destruct H13. destruct H13. destruct H14. rename x0 into S. rename x1 into LT.
    
    specialize(_3_19_h q p l); intros.
    specialize(subtype_recv T q x H10); intros. destruct H17. subst.
    specialize(subtype_send T' p (extendLis l (Some (S, LT))) H15); intros. destruct H17. subst.
    rename x0 into LQ. rename x1 into LP.
    specialize(H16 G LP LQ S LT).
    specialize(_3_21_helper l xs x y H H11); intros. destruct H17. destruct H17. destruct H17.
    specialize(H16 x (x0, x1)). 
    assert(exists G' : gtt, gttstepC G G' q p l).
    apply H16; try easy. destruct H19. subst. rename x2 into G'. 
    assert(multiC G G').
    specialize(multiC_step G G' G' q p l); intros. apply H20; try easy. constructor.
    exists G'. split; try easy. clear H20.
    clear H16.
    constructor.
    - specialize(wfgC_after_step G G' q p l H2 H19); try easy.
    - intros.
      apply H3; try easy.
      
        
      - specialize(part_after_step G G' q p pt l LP LQ); intros. 
        apply H20; try easy.
      easy.
    specialize(projection_step_label G G' q p l LP LQ); intros.
    assert(exists (LS LS' : sort) (LT LT' : ltt), onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')).
    apply H16; try easy. clear H16. destruct H20. destruct H16. destruct H16. destruct H16. destruct H16.
    rename x2 into SL. rename x3 into SL'. rename x4 into TL. rename x5 into TL'.
    
    specialize(_a_29_s G q p LP LQ SL TL SL' TL' l H2 H6 H16 H1 H20); intros.
    destruct H21. rename x2 into Gl. destruct H21. rename x2 into ctxG. destruct H21. destruct H21.
    rename x2 into SI. rename x3 into Sn.
    destruct H21. destruct H22. destruct H23. destruct H24. destruct H25. destruct H26.
    specialize(_3_21_helper_1 H20 H17 H10); intros.
    specialize(_3_21_helper_2 H15 H16); intros. 
    constructor. constructor.
    - constructor.
      specialize(_3_19_2_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H30; try easy. clear H30. 
      exists TL'. split; try easy.
      
      apply _a24 with (S := x0); try easy.
      - apply tc_sub with (t := x1); try easy.
        specialize(typable_implies_wfC H5); intros.
        specialize(wfC_recv H30 H20); try easy.
      - apply sc_sub with (s := S); try easy.
        apply expr_typ_multi with (e := e); try easy.
        apply sstrans with (s2 := SL'); try easy.
        apply sstrans with (s2 := Sn); try easy. 
        apply sstrans with (s2 := SL); try easy.
    - constructor.
      specialize(_3_19_1_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H30; try easy. clear H30.
      exists TL. split; try easy.
      - apply tc_sub with (t := LT); try easy.
        specialize(typable_implies_wfC H7); intros.
        specialize(wfC_send H30 H16); try easy.
    - specialize(_3_19_3_helper M q p G G' l LP LQ S LT x (x0, x1)); intros.
      inversion H4. subst. inversion H34. subst.
      specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H33); intros. destruct H31.
      apply H30; try easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4.
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H9. destruct H10. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H5); try easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4.
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H9. destruct H10. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H5); try easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(_a22_2 M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(_a22_2 M2' M2 x H4 H0); intros. easy.
Qed.