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

Lemma merge_less_recv : forall p LQ o1 ys1,
    isMerge (ltt_recv p LQ) (o1 :: ys1) -> exists LQ0, isMerge (ltt_recv p LQ0) ys1.
Admitted.

Lemma merge_less_send : forall q LP o2 ys0,
    isMerge (ltt_send q LP) (o2 :: ys0) -> exists LP0, isMerge (ltt_send q LP0) ys0.
Admitted.

Lemma _a_26 : forall T xt xs,
  isMerge T (Some xt :: xs) -> subtypeC T xt.
Admitted.

Lemma _a_26s : forall T lis,
  isMerge T lis -> List.Forall (fun u => u = None \/ (exists T', u = Some T' /\ subtypeC T T')) lis.
Admitted.

Lemma triv_merge : forall T, isMerge T (Some T :: nil).
Admitted.

Lemma triv_merge2 : forall T xs, isMerge T xs -> isMerge T (None :: xs).
Admitted.

Lemma more_merge_sub: forall T T' o0 ys0,
          isMerge T ys0 ->
          isMerge T' (o0 :: ys0) ->
          subtypeC T' T.
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
  - revert H H0 H1 H2 H3 H4 H5 H6 H7.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    revert s s' p q l G G' LP LQ S T S' T' xs0.
    induction xs; intros; try easy.
    - destruct H7. destruct H7. destruct H7. destruct H7. destruct H8. destruct H9. 
      inversion H7. subst. easy.
    - specialize(IHxs s s' p q l).
      inversion H. subst. clear H.
      assert(forall (G G' : gtt) (S : sort) (T : ltt) 
         (S' : sort) (T' : ltt) (xs0 : list (option (sort * ltt))) (LP LQ : list (option (sort * ltt))),
      wfgC G ->
      projectionC G p (ltt_send q LP) ->
      subtypeC (ltt_send q (extendLis l (Some (S, T)))) (ltt_send q LP) ->
      projectionC G q (ltt_recv p LQ) ->
      onth l xs0 = Some (S', T') ->
      subtypeC (ltt_recv p xs0) (ltt_recv p LQ) ->
      gttstepC G G' p q l ->
      (exists (ctxG : list (option gtt)) (SI : list (option sort)) (Sn : sort),
         typ_gtth ctxG (gtth_send s s' xs) G /\
         (ishParts p (gtth_send s s' xs) -> False) /\
         (ishParts q (gtth_send s s' xs) -> False) /\
         Forall
              (fun u : option gtt =>
               u = None \/
               (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                  u = Some g0 /\
                  g0 = gtt_send p q lsg /\
                  (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
                     onth l lsg = Some (s', Gjk) /\
                     projectionC Gjk p Tp /\ subtypeC T Tp /\ projectionC Gjk q Tq /\ subtypeC T' Tq) /\
                  Forall2
                    (fun (u0 : option (sort * gtt)) (v : option sort) =>
                     u0 = None /\ v = None \/
                     (exists (s0 : sort) (g' : gtt), u0 = Some (s0, g') /\ v = Some s0)) lsg SI)) ctxG /\
           onth l SI = Some Sn /\ subsort S Sn /\ subsort Sn S') ->
        exists L : ltt, projectionC G' p L /\ subtypeC T L).
      {
        intros.
        specialize(IHxs G0 G'0 LP0 LQ0 S0 T0 S'0 T'0 xs1). apply IHxs; try easy.
      }
      clear IHxs. rename H into IHxs. clear H11.
      
      destruct H7. destruct H. destruct H. destruct H. destruct H7. destruct H8. destruct H9. destruct H11. destruct H12.
      rename x into ctxG. rename x1 into Sn.
      inversion H. subst. destruct ys; try easy. inversion H20. subst. clear H20.
      
      pinversion H1. subst. assert False. apply H7. constructor. easy.
      pinversion H3. subst. assert False. apply H7. constructor. easy.
      subst. clear H34 H23. rename x0 into SI.
      pinversion H6. subst. easy. subst. clear H18 H20 H22 H31 H32 H33.
      destruct ys0; try easy. destruct ys1; try easy. destruct ys2; try easy.
      
      specialize(SList_f a xs H19); intros. destruct H14.
      
      specialize(IHxs (gtt_send s s' ys) (gtt_send s s' ys2) S T S' T' xs0).
      assert(forall LP LQ : list (option (sort * ltt)),
       wfgC (gtt_send s s' ys) ->
       projectionC (gtt_send s s' ys) p (ltt_send q LP) ->
       subtypeC (ltt_send q (extendLis l (Some (S, T)))) (ltt_send q LP) ->
       projectionC (gtt_send s s' ys) q (ltt_recv p LQ) ->
       subtypeC (ltt_recv p xs0) (ltt_recv p LQ) ->
       exists L : ltt, projectionC (gtt_send s s' ys2) p L /\ subtypeC T L).
      {
        intros. specialize(IHxs LP0 LQ0). apply IHxs; try easy.
        - inversion H41. inversion H42. subst. pfold. constructor; try easy.
          admit. (* removing 1 thing from wfgC *)
        exists ctxG. exists SI. exists Sn.
        - split. constructor; try easy.
        - split; intros. apply H7. inversion H31.
          apply ha_sendp. apply ha_sendq. 
          apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); intros; try easy.
        - split; intros. apply H8. inversion H31.
          apply ha_sendp. apply ha_sendq. 
          apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); intros; try easy.
        - split; try easy.
      }
      clear IHxs. rename H15 into IHxs.
      specialize(merge_less_recv p LQ o1 ys1 H38); intros. destruct H15.
      specialize(merge_less_send q LP o0 ys0 H27); intros. destruct H16.
      rename x into LQ'. rename x0 into LP'.
      specialize(IHxs LP' LQ'); intros.
      assert (exists L : ltt, projectionC (gtt_send s s' ys2) p L /\ subtypeC T L). 
      {
        apply IHxs; try easy. clear IHxs.
        - admit. (* removing 1 thing from wfgC *)
        - pfold. 
          apply proj_cont with (ys := ys0); try easy. inversion H26. subst. easy.
          apply stTrans with (l2 := (ltt_send q LP)); try easy.
          apply more_merge_sub with (o0 := o0) (ys0 := ys0); try easy.
        - pfold.
          apply proj_cont with (ys := ys1); try easy. inversion H37. subst. easy.
          apply stTrans with (l2 := (ltt_recv p LQ)); try easy.
          apply more_merge_sub with (o0 := o1) (ys0 := ys1); try easy.
      }
      destruct H18. rename x into Lys. destruct H18.
      
      inversion H41. subst. clear H41. inversion H37. subst. clear H37.
      inversion H42. subst. clear H42. inversion H26. subst. clear H26.
      clear IHxs.
      
      destruct H10. subst.
      - destruct H17; try easy. destruct H10. subst.
        destruct H37. destruct H36. destruct H39. destruct H22. destruct H17. destruct H26. subst.
        exists Lys. split; try easy.
        pfold. 
        pinversion H18; try easy. subst. (* participant pf, use H33 *)
        admit.
        subst. apply proj_cont with (ys := None :: ys3); try easy. constructor; try easy.
        left. easy.
        apply triv_merge2; try easy.
        apply proj_mon.
        destruct H26. destruct H26. destruct H26. destruct H26; try easy.
        destruct H22. destruct H22. destruct H22. destruct H22. easy.
        destruct H17. destruct H17. destruct H17. destruct H17. easy.
        destruct H10. destruct H10. destruct H10. destruct H10. easy.
        
      - destruct H10. destruct H10. destruct H10. subst.
        destruct H17; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H17.
        inversion H10. subst. clear H10.
        destruct H32; try easy. destruct H10. destruct H10. destruct H10. destruct H17.
        inversion H10. subst. clear H10.
        destruct H37; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H32.
        inversion H10. subst. clear H10.
        destruct H36; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H32.
        inversion H10. subst. clear H10.
        destruct H39; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H32.
        inversion H10. subst. clear H10.
        rename x2 into Gl. rename x3 into G. rename x4 into G'.
        specialize(H22 p q l G G').
        specialize(_a_29_part_helper_recv 0 (Some x5 :: ys1) x5 p LQ (eq_refl (Some x5)) H38); intros.
        destruct H10. subst.
        specialize(_a_29_part_helper_send 0 (Some x6 :: ys0) x6 q LP (eq_refl (Some x6)) H27); intros.
        destruct H10. subst.
        
        rename x into LQs. rename x0 into LPs.
        specialize(H22 LPs LQs S T S' T' xs0).
        assert (exists L : ltt, projectionC G' p L /\ subtypeC T L).
        {
          pclearbot.
          apply H22; try easy.
          - admit. (* wfgC of continuation *)
          - specialize(_a_26 (ltt_send q LP) (ltt_send q LPs) ys0 H27); intros.
            apply stTrans with (l2 := (ltt_send q LP)); try easy.
          - specialize(_a_26 (ltt_recv p LQ) (ltt_recv p LQs) ys1 H38); intros.
            apply stTrans with (l2 := (ltt_recv p LQ)); try easy.
          - destruct H35; try easy.
          - exists ctxG. exists SI. exists Sn. 
          split. easy.
          - split. intros. apply H7; try easy.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              apply ha_sendr with (n := 0) (s := x1) (g := Gl); try easy.
          - split. intros. apply H8.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              apply ha_sendr with (n := 0) (s := x1) (g := Gl); try easy.
          - split; try easy.
        }
        destruct H10. destruct H10. clear H9 H22. 
        destruct x.
        - exists ltt_end. split; try easy.
          pfold. constructor; try easy.
          admit. (* doable, a bit tedious *)
        - 
        
      admit. 
      
      destruct H14. destruct H15. subst. destruct ys; try easy. clear H21.
      inversion H37. subst. clear H37. inversion H41. subst. clear H41. inversion H42. subst. clear H42.
      destruct ys2; try easy. destruct ys1; try easy. clear H33 H20 H21.
      inversion H26. subst. clear H26. destruct ys0; try easy. 
      destruct H10; try easy. destruct H10. destruct H10. destruct H10.
      inversion H10. subst. clear H10.
      destruct H17; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H15.
      inversion H10. subst. clear H10. clear H32.
      destruct H21; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H15. 
      inversion H10. subst. clear H10.
      destruct H31; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H15.
      inversion H10. subst. clear H10.
      destruct H16; try easy. destruct H10. destruct H10. destruct H10. destruct H15. 
      inversion H10. subst. clear H10.
      destruct H18; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H18.
      inversion H10. subst. clear H10.
      rename x2 into Gl. rename x3 into G. rename x5 into G'.
      specialize(H14 p q l G G').
      
      specialize(_a_29_part_helper_recv 0 (Some x6 :: nil) x6 p LQ (eq_refl (Some x6)) H38); intros.
      destruct H10. subst.
      specialize(_a_29_part_helper_send 0 (Some x4 :: nil) x4 q LP (eq_refl (Some x4)) H27); intros.
      destruct H10. subst.
      rename x1 into LP'. rename x0 into LQ'.
      specialize(H14 LP' LQ' S T S' T' xs0).
      assert (exists L : ltt, projectionC G' p L /\ subtypeC T L).
      {
        pclearbot.
        apply H14; try easy.
        - admit. (* wfgC of element in continuation *)
        - specialize(_a_26 (ltt_send q LP) (ltt_send q LP') nil H27); intros.
          apply stTrans with (l2 := (ltt_send q LP)); try easy.
        - specialize(_a_26 (ltt_recv p LQ) (ltt_recv p LQ') nil H38); intros.
          apply stTrans with (l2 := (ltt_recv p LQ)); try easy.
        - destruct H21; try easy.
        - exists ctxG. exists SI. exists Sn. 
        split. easy.
        - split. intros. apply H7; try easy.
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x) (g := Gl); try easy.
        - split. intros. apply H8.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x) (g := Gl); try easy.
        - split; try easy.
      }
      destruct H10. destruct H10. 
      exists x0. split; try easy. 
      pfold.
      destruct x0.
      - apply proj_end; intros.
        apply pmergeCR with (G := G') (r := p); try easy.
        admit. (* participant pf, doable, because we have wfcG *)
      - apply proj_cont with (ys := (Some (ltt_recv s0 l0) :: nil)); try easy.
        constructor; try easy. right. exists x. exists G'. exists (ltt_recv s0 l0).
        split. easy. split. easy. left. easy.
        apply triv_merge; try easy.
      - apply proj_cont with (ys := (Some (ltt_send s0 l0) :: nil)); try easy.
        constructor; try easy. right. exists x. exists G'. exists (ltt_send s0 l0).
        split. easy. split. easy. left. easy.
        apply triv_merge; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
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