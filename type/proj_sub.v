From SST Require Export type.global type.local type.isomorphism type.projection type.merge.
Require Import List String Datatypes ZArith Relations PeanoNat. 
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Lemma step_mon : monotone5 gttstep.
Admitted.

Lemma gttT_mon : monotone2 gttT.
Admitted.

Lemma merge_same : forall ys ys0 ys1 p q l LP LQ S T S' T',
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys0 ->
      isMerge (ltt_send q LP) ys0 ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys1 ->
      isMerge (ltt_recv p LQ) ys1 ->
      onth l LP = Some (S, T) ->
      onth l LQ = Some (S', T') ->
      Forall (fun u => u = None \/ (exists s g LP' LQ', u = Some (s, g) /\
          projectionC g p (ltt_send q LP') /\ onth l LP' = Some (S, T) /\
          projectionC g q (ltt_recv p LQ') /\ onth l LQ' = Some (S', T'))) ys.
Proof.
Admitted.

Lemma merge_constr : forall p LQ ys1 n,
          isMerge (ltt_recv p LQ) ys1 ->
          onth n ys1 = Some ltt_end ->
          False.
Admitted.

Lemma merge_consts : forall q LP ys0 n,
          isMerge (ltt_send q LP) ys0 -> 
          onth n ys0 = Some ltt_end -> 
          False.
Admitted.

Lemma merge_slist : forall T ys, isMerge T ys -> SList ys.
Proof.
  intros T ys. revert T. induction ys; intros; try easy.
  unfold isMerge in H. destruct H. easy.
  unfold isMerge in H. destruct H. easy.
Qed.

Lemma in_some_implies_onth {A} : forall (x : A) xs,
    In (Some x) xs -> exists n, onth n xs = Some x.
Proof.
  intros. revert H. revert x. 
  induction xs; intros; try easy.
  simpl in *. destruct H. exists 0. easy.
  specialize(IHxs x H). destruct IHxs. exists (Nat.succ x0). easy.
Qed.

Lemma ishParts_hxs : forall [p s1 s2 o1 xs0],
    (ishParts p (gtth_send s1 s2 (o1 :: xs0)) -> False) ->
    (ishParts p (gtth_send s1 s2 xs0) -> False).
Admitted.

Lemma ishParts_x : forall [p s1 s2 o1 o2 xs0],
    (ishParts p (gtth_send s1 s2 (Some (o1,o2) :: xs0)) -> False) ->
    (ishParts p o2 -> False).
Admitted.

Lemma proj_inv_lis : forall Gl p q l s s' ys ctxG LP LQ,
    (ishParts p Gl -> False) ->
    (ishParts q Gl -> False) ->
    Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ projectionC Gjk q Tq)))
       ctxG ->
    typ_gtth ctxG Gl (gtt_send s s' ys) ->
    projectionC (gtt_send s s' ys) p (ltt_send q LP) -> 
    projectionC (gtt_send s s' ys) q (ltt_recv p LQ) -> 
    (s = p /\ s' = q /\ exists Gk, onth l ys = Some Gk) \/
    (s <> p /\ s' <> q /\ List.Forall (fun u => u = None \/ 
        (exists s g LP' LQ' T T', u = Some(s, g) /\ projectionC g p (ltt_send q LP') /\ projectionC g q (ltt_recv p LQ') /\ 
          onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
Proof.
  intro Gl. induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H2. subst.
    specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
            u = None \/
            (exists (g : gtt) (lsg : list (option (sort * gtt))),
               u = Some g /\
               g = gtt_send p q lsg /\
               (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
                  onth l lsg = Some (s', Gjk) /\
                  projectionC Gjk p Tp /\
                  projectionC Gjk q Tq))) ctxG); intros. destruct H6.
    specialize(H6 H1). clear H1 H8. specialize(H6 (Some (gtt_send s s' ys)) H5).
    destruct H6; try easy. destruct H1. destruct H1. destruct H1. destruct H6. destruct H8.
    destruct H8. destruct H8. destruct H8. destruct H8. destruct H9.
    subst. inversion H1. subst.
    left. split; try easy. split; try easy. exists (x1, x2). easy.
  - inversion H3. subst. right. 
    pinversion H4; try easy. subst.
    assert False. apply H0. constructor. easy.
    subst. split; try easy. 
    pinversion H5; try easy. subst. split; try easy. 
    rename p0 into p. rename q0 into q. 
    apply Forall_forall; intros; try easy. destruct x.
    - destruct p0. right.
      specialize(in_some_implies_onth (s0, g) ys H6); intros. destruct H7. rename x into n.
      assert(exists t t' g', onth n ys1 = Some t /\ projectionC g q t /\ onth n ys0 = Some t' /\ projectionC g p t' /\ onth n xs = Some (s0, g') /\ typ_gtth ctxG g' g /\
              (forall (p q : string) (l : fin) (s0 s' : string)
                 (ys : list (option (sort * gtt))) (ctxG : list (option gtt)) 
              (LP LQ : list (option (sort * ltt))),
               (ishParts p g' -> False) ->
               (ishParts q g' -> False) ->
               Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
               typ_gtth ctxG g' (gtt_send s0 s' ys) ->
               projectionC (gtt_send s0 s' ys) p (ltt_send q LP) ->
               projectionC (gtt_send s0 s' ys) q (ltt_recv p LQ) ->
               s0 = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
               s0 <> p /\
               s' <> q /\
               Forall
                 (fun u0 : option (sort * gtt) =>
                  u0 = None \/
                  (exists
                     (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
                   (T0 T'0 : sort * ltt),
                     u0 = Some (s1, g0) /\
                     projectionC g0 p (ltt_send q LP') /\
                     projectionC g0 q (ltt_recv p LQ') /\
                     onth l LP' = Some T0 /\ onth l LQ' = Some T'0)) ys)
      ).
      {
        clear H6 H22 H18 H15 H13 H17 H12 H11 H10 H9 H5 H4 H3 H1 H0.
        clear H2. revert H7 H21 H16 H14 H. revert xs p q l s s' ctxG LP LQ ys0 ys1 s0 g n.
        induction ys; intros; try easy. destruct n; try easy. 
        destruct ys1; try easy. destruct xs; try easy. destruct ys0; try easy.
        inversion H. subst. clear H. inversion H21. subst. clear H21.
        inversion H16. subst. clear H16. inversion H14. subst. clear H14.
        
        destruct n.
        - simpl in *. subst.
          destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
          inversion H. subst. clear H.
          clear H11 H9 H6 H3 IHys.
          destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
          inversion H. subst. clear H.
          destruct H8; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
          inversion H. subst. inversion H0. subst. clear H0 H5.
          destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          exists x1. exists x4. exists x3. pclearbot. easy.
        - simpl in *.
          apply IHys; try easy.
      }
      clear H21 H16 H14 H.
      destruct H8. destruct H. destruct H. destruct H. destruct H8.
      destruct H14. destruct H16. destruct H19. destruct H20. 
      rename x0 into gpT. rename x1 into g'. rename x into gqT.
      inversion H20; try easy. subst.
      - specialize(some_onth_implies_In n0 ctxG g H23); intros.
        pose proof H2 as HctxG.
        specialize(Forall_forall (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : list (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
                 onth l lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros. destruct H25.
        specialize(H25 H2 (Some g) H24). clear H26 H2.
        destruct H25; try easy. destruct H2. destruct H2. destruct H2. destruct H25.
        inversion H2. subst. exists s0. exists (gtt_send p q x0).
        pinversion H8; try easy. subst.
        - specialize(merge_constr p LQ ys1 n H22 H); intros. easy.
        - subst. 
          pinversion H16; try easy. subst.
          specialize(merge_consts q LP ys0 n H17 H14); intros. easy.
        - subst.
          specialize(H21 p q l p q x0 ctxG ys3 ys2).
          assert (p = p /\ q = q /\ (exists Gk : sort * gtt, onth l x0 = Some Gk) \/
      p <> p /\
      q <> q /\
      Forall
        (fun u0 : option (sort * gtt) =>
         u0 = None \/
         (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T0 T'0 : sort * ltt),
            u0 = Some (s1, g0) /\
            projectionC g0 p (ltt_send q LP') /\
            projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T0 /\ onth l LQ' = Some T'0)) x0).
        {
          apply H21; try easy.
          pfold. easy. pfold. easy.
        }
        destruct H25; try easy. destruct H25. destruct H27. destruct H30.
        exists ys3. exists ys2. 
        clear H27 H29 H25 H34 H28 H31 H26 HctxG H23 H24 H19 H20 H21 H14 H7 H6 H2 H22 H18 H15 H13 H17 H12.
        clear H11 H10 H9 H5 H4 H3 H1 H0 H.
        clear xs s s' ys ctxG n. clear LP LQ.
        assert(exists T T' : sort * ltt, onth l ys3 = Some T /\ onth l ys2 = Some T').
        {
          clear H16 H8 ys0 ys1. revert H32 H35 H30. clear s0 n0. revert p q x0 ys2 ys3 x.
          induction l; intros; try easy.
          - destruct x0; try easy. destruct ys2; try easy. destruct ys3; try easy.
            inversion H32. inversion H35. subst. clear H32 H35 H4 H10.
            simpl in *. subst. destruct H8; try easy. destruct H. destruct H. destruct H. destruct H.
            destruct H0. inversion H. subst.
            destruct H2; try easy. destruct H0. destruct H0. destruct H0. destruct H0.
            destruct H2. inversion H0. subst.
            exists (x,x3). exists (x,x5). easy.
          - destruct x0; try easy. destruct ys2; try easy. destruct ys3; try easy.
            inversion H32. inversion H35. subst. specialize(IHl p q x0 ys2 ys3 x). apply IHl; try easy.
        }
        destruct H. destruct H. exists x1. exists x2. split. easy. split. pfold. easy. split. pfold. easy.
        easy.
        apply proj_mon.
        apply proj_mon.
      subst. rename p0 into s1. rename q0 into s2. rename ys2 into l0.
      specialize(H21 p q l s1 s2 l0 ctxG).
      specialize(merge_onth_send n q LP ys0 gpT H17 H14); intros. destruct H25. subst.
      specialize(merge_onth_recv n p LQ ys1 gqT H22 H); intros. destruct H25. subst.
      rename x0 into LQ'. rename x into LP'.
      specialize(H21 LP' LQ'). 
      exists s0. exists (gtt_send s1 s2 l0). exists LP'. exists LQ'.
      assert (ishParts p (gtth_send s1 s2 xs0) -> False).
      {
        intros. apply H0.
        - case_eq (eqb p s); intros.
          assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
        - case_eq (eqb p s'); intros.
          assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
        - assert (p <> s). apply eqb_neq; try easy. 
          assert (p <> s'). apply eqb_neq; try easy.
          apply ha_sendr with (n := n) (s := s0) (g := gtth_send s1 s2 xs0); try easy. 
      }
      assert (ishParts q (gtth_send s1 s2 xs0) -> False).
      {
        intros. apply H1.
        - case_eq (eqb q s); intros.
          assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
        - case_eq (eqb q s'); intros.
          assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
        - assert (q <> s). apply eqb_neq; try easy. 
          assert (q <> s'). apply eqb_neq; try easy.
          apply ha_sendr with (n := n) (s := s0) (g := gtth_send s1 s2 xs0); try easy.
      }
      assert (s1 = p /\ s2 = q /\ (exists Gk : sort * gtt, onth l l0 = Some Gk) \/
      s1 <> p /\
      s2 <> q /\
      Forall
        (fun u0 : option (sort * gtt) =>
         u0 = None \/
         (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T0 T'0 : sort * ltt),
            u0 = Some (s1, g0) /\
            projectionC g0 p (ltt_send q LP') /\
            projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T0 /\ onth l LQ' = Some T'0)) l0).
      {
        apply H21; try easy.
      }
      clear H21.
      destruct H27.
      - destruct H21. destruct H27. destruct H28. subst.
        assert False. apply H25. constructor. easy.
      - destruct H21. destruct H27. 
        pinversion H16; try easy. subst.
        pinversion H8; try easy. subst.
        assert(exists T0 T'0, onth l LP' = Some T0 /\ onth l LQ' = Some T'0).
        {
          specialize(merge_slist (ltt_send q LP') ys2 H38); intros.
          assert (exists k s g, onth k l0 = Some (s, g) /\ exists LP' LQ' T0 T'0, projectionC g p (ltt_send q LP') /\
                  projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T0 /\ onth l LQ' = Some T'0 /\
                  onth k ys2 = Some (ltt_send q LP') /\ onth k ys3 = Some (ltt_recv p LQ')).
          {
            
            clear H43 H39 H36 H35 H38 H34 H33 H32 H27 H21 H20 H23 H19 H14 H16 H8 H7 H6 H22 H18 H15 H13 H17 H12 H11 H10 H9 H5 H4 H3 H1 H0.
            revert H28 H37 H29 H42 H2. clear H. clear s s' xs ys LP LQ ys0 ys1 s0 LQ' LP' n.
            revert H24 H25 H26. revert p q l ys2 ys3 ctxG xs0 s1 s2. induction l0; intros; try easy. destruct ys2; try easy. 
            - destruct ys2; try easy. destruct ys3; try easy. destruct xs0; try easy.
              specialize(SList_f o ys2 H29); intros.
              inversion H28. inversion H37. inversion H42. inversion H24. subst. clear H42 H28 H37 H29 H24. destruct H.
              specialize(IHl0 p q l ys2 ys3 ctxG). 
              assert (exists (k : fin) (s : sort) (g : gtt),
         onth k l0 = Some (s, g) /\
         (exists (LP' LQ' : list (option (sort * ltt))) (T0 T'0 : sort * ltt),
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\
            onth l LP' = Some T0 /\
            onth l LQ' = Some T'0 /\
            onth k ys2 = Some (ltt_send q LP') /\ onth k ys3 = Some (ltt_recv p LQ'))).
              apply IHl0 with (xs0 := xs0) (s1 := s1) (s2 := s2); try easy.
              specialize(ishParts_hxs H25); try easy.
              specialize(ishParts_hxs H26); try easy.
              destruct H0. exists (Nat.succ x). easy.
            - destruct H. destruct H0. subst.
              destruct H8; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
              inversion H0. subst.
              destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
              destruct H. destruct H. destruct H3. destruct H5. destruct H6.
              inversion H. subst.
              destruct H14; try easy. destruct H8. destruct H8. destruct H8. destruct H8.
              destruct H9. inversion H8. subst.
              exists 0. exists x0. exists x1. split; try easy.
              exists x4. exists x5. exists x6. exists x7. 
              
              pclearbot. 
              destruct H20; try easy. destruct H9. destruct H9. destruct H9. destruct H9.
              destruct H12. inversion H12. subst.
              assert (ltt_send q x4 = x2). { admit. }
              assert (ltt_recv p x5 = x8). { admit. } 
              subst.
              easy.
              
          }
          destruct H30. destruct H30. destruct H30. destruct H30.
          destruct H31. destruct H31. destruct H31. destruct H31. destruct H31.
          destruct H40. destruct H41. destruct H44. destruct H45.
          specialize(merge_label_recv ys3 LQ' x3 x5 x l p H43 H46 H44); intros.
          specialize(merge_label_send ys2 LP' x2 x4 x l q H38 H45 H41); intros.
          destruct H47. destruct H48.
          exists x7. exists x6. easy.
          
        }
        destruct H29. destruct H29. exists x. exists x0. 
        split. easy. split. pfold. easy. split. pfold. easy. easy.
      apply proj_mon.
      apply proj_mon.
    left. easy.
  apply proj_mon.
  apply proj_mon.
Admitted.

Lemma _3_19_1_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' p T.
Proof.
  intros.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. clear H.
  revert H0 H1 H2 H3 H4 H5. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis (gtth_send s s' xs) p q l s s' ys ctxG LP LQ); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      admit. (* ease up ctxG def *)
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H27 H28 H29 H20 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T)) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' H31 H22 H23 H32 H33 H1 H3); intros.
      clear H32 H31 H22.
      clear H23 H21 H24 H25 H26 H30 H3 H1. 
      revert H0 H38 H18 H8 H7 H6 H H9 H10 H11. clear H37 H33. clear ys0 ys1 LP LQ. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H38. subst. clear H38.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g p T)) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        clear H14 H15 H13 H4 IHxs.
        constructor; try easy.
        destruct H5. destruct H0. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x1. split; try easy.
        destruct H12; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
        inversion H1. subst. clear H1.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
        destruct H1. destruct H3. destruct H12. inversion H0. subst. clear H0.
        destruct H2; try easy. destruct H0. destruct H0. destruct H0.
        inversion H0. subst.
        rename x4 into Gl. rename x0 into G. rename x1 into G'. rename x6 into LQ. rename x5 into LP.
        specialize(H2 p q l G G' LP LQ S S' T T').
        apply H2; try easy. destruct H4; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        clear H2 H H4.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
    }
    
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g p t)) ys2 ys3 /\ isMerge T ys3).
    {
      clear H33 H37 H31 H30 H26 H25 H24 H21 H33 H32 H23 H22 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H17 H18 H12 H38.
      revert s s' xs p q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H38. subst. clear H18 H12 H38.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - assert (exists ys3, Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             (u = None /\ v = None) \/
             (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g p t))
            ys2 ys3 /\ isMerge T ys3).
          {
            apply IHys2 with (xs := xs) (q := q) (l := l) (ys := ys) (ctxG := ctxG); try easy.
          }
          destruct H0. clear IHys2.
          - destruct H6. destruct H5. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. subst.
            destruct H2; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
            inversion H5. subst. 
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T :: x). split.
            constructor; try easy. right. exists x0. exists x1. exists T. easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3.
            inversion H0. subst.
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T :: nil). split.
            constructor; try easy. right. exists x0. exists x2. exists T. easy.
            unfold isMerge. easy.
    }
    destruct H13. destruct H13. pfold.
    apply proj_cont with (ys := x); try easy.
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H17 H18 H22 H23 H32 H33 H21 H24 H25 H26 H30 H31 H38 H37 H12 H14.
    clear s s' xs q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
    revert H13. revert p x.
    induction ys2; intros; try easy.
    - destruct x; try easy.
    - destruct x; try easy.
      inversion H13. subst. clear H13.
      specialize(IHys2 p x H4). constructor; try easy. clear IHys2 H4.
      destruct H2. left. easy. 
      destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
      right. exists x0. exists x1. exists x2. split. easy. split. easy. left. easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Admitted.

Lemma _3_19_2_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' q T'.
Proof.
  intros.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. clear H.
  revert H0 H1 H2 H3 H4 H5. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis (gtth_send s s' xs) p q l s s' ys ctxG LP LQ); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      admit. (* ease up ctxG def *)
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H27 H28 H29 H20 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g q T')) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' H31 H22 H23 H32 H33 H1 H3); intros.
      clear H32 H31 H22.
      clear H23 H21 H24 H25 H26 H30 H3 H1. 
      revert H0 H38 H18 H8 H7 H6 H H9 H10 H11. clear H37 H33. clear ys0 ys1 LP LQ. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H38. subst. clear H38.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g q T')) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        clear H14 H15 H13 H4 IHxs.
        constructor; try easy.
        destruct H5. destruct H0. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x1. split; try easy.
        destruct H12; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
        inversion H1. subst. clear H1.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
        destruct H1. destruct H3. destruct H12. inversion H0. subst. clear H0.
        destruct H2; try easy. destruct H0. destruct H0. destruct H0.
        inversion H0. subst.
        rename x4 into Gl. rename x0 into G. rename x1 into G'. rename x6 into LQ. rename x5 into LP.
        specialize(H2 p q l G G' LP LQ S S' T T').
        apply H2; try easy. destruct H4; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        clear H2 H H4.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
    }
    
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g q t)) ys2 ys3 /\ isMerge T' ys3).
    {
      clear H33 H37 H31 H30 H26 H25 H24 H21 H33 H32 H23 H22 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H17 H18 H12 H38.
      revert s s' xs p q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H38. subst. clear H18 H12 H38.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - assert (exists ys3, Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             (u = None /\ v = None) \/
             (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g q t))
            ys2 ys3 /\ isMerge T' ys3).
          {
            apply IHys2 with (xs := xs) (p := p) (l := l) (ys := ys) (ctxG := ctxG); try easy.
          }
          destruct H0. clear IHys2.
          - destruct H6. destruct H5. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. subst.
            destruct H2; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
            inversion H5. subst. 
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T' :: x). split.
            constructor; try easy. right. exists x0. exists x1. exists T'. easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3.
            inversion H0. subst.
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T' :: nil). split.
            constructor; try easy. right. exists x0. exists x2. exists T'. easy.
            unfold isMerge. easy.
    }
    destruct H13. destruct H13. pfold.
    apply proj_cont with (ys := x); try easy.
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H17 H18 H22 H23 H32 H33 H21 H24 H25 H26 H30 H31 H38 H37 H12 H14.
    clear s s' xs p l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
    revert H13. revert q x.
    induction ys2; intros; try easy.
    - destruct x; try easy.
    - destruct x; try easy.
      inversion H13. subst. clear H13.
      specialize(IHys2 q x H4). constructor; try easy. clear IHys2 H4.
      destruct H2. left. easy. 
      destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
      right. exists x0. exists x1. exists x2. split. easy. split. easy. left. easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Admitted.

Lemma SList_to_In {A} : forall (xs : list (option A)),
    SList xs ->
    exists t, In (Some t) xs.
Proof.
  induction xs; intros; try easy.
  specialize(SList_f a xs H); intros.
  destruct H0.
  specialize(IHxs H0). destruct IHxs. exists x. right. easy.
  destruct H0. destruct H1. subst. exists x. left. easy.
Qed.

Lemma projection_step_label : forall G G' p q l LP LQ,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists LS LS' LT LT', onth l LP = Some(LS, LT) /\ onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(_a_29_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. clear Gl LQ l. clear G G'.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  } 
  clear H3. rename H4 into H3.
  revert H0 H1 H2 H3. clear H.
  revert G G' p q l LP LQ.
  induction Gl using gtth_ind_ref; intros; try easy.
  - destruct H3. destruct H. destruct H3. inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4). clear H8. specialize(H6 (Some G) H5). clear H5 H4.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4.
    subst.
    pinversion H1; try easy. subst.
    pinversion H2; try easy. subst.
    pinversion H0; try easy. subst.
    clear H9 H13 H15 H14 H10 H8 H10 H7 H3 H0 H1 H2 H4 H H16. clear n x.
    revert H12 H17 H19. revert G' p q LP LQ x1 s.
    induction l; intros; try easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H19. subst. clear H19. inversion H12. subst. clear H12. 
      simpl in *. subst.
      destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H. subst.
      destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      inversion H0. subst.
      exists x3. exists x3. exists x2. exists x5. easy.
    - destruct x1; try easy. destruct LP; try easy. destruct LQ; try easy.
      inversion H12. subst. inversion H19. subst.
      specialize(IHl G' p q LP LQ x1 s). apply IHl; try easy.
    apply proj_mon.
    apply step_mon. 
    apply proj_mon.
  - destruct H3. destruct H3. destruct H4. 
    rename p into s. rename q into s0. rename p0 into p. rename q0 into q.
    specialize(_a_29_part x (gtth_send s s0 xs) G p q LP LQ H3 H0 H1 H4); intros.
    inversion H3. subst.
    pinversion H1. subst.
    - assert False. apply H4. constructor. easy.
    pinversion H0; try easy. subst. 
    specialize(SList_to_In xs H12); intros. destruct H7.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt))),
           projectionC G p (ltt_send q LP) ->
           projectionC G q (ltt_recv p LQ) ->
           gttstepC G G' p q l ->
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\
                    g0 = gtt_send p q lsg)) ctxJ) ->
           exists (LS LS' : sort) (LT LT' : ltt),
             onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H). clear H H9.
    specialize(H8 (Some x0) H7). destruct H8; try easy. destruct H. destruct H.
    destruct H. inversion H. subst. clear H. rename x2 into G.
    specialize(in_some_implies_onth (x1, G) xs H7); intros. destruct H. clear H7. rename x0 into n.
    rename x into ctxG.
    pinversion H2; try easy. subst.
    assert(exists g g' t t', onth n ys = Some(x1, g) /\ typ_gtth ctxG G g /\ onth n ys0 = Some t /\ projectionC g q t /\
           onth n ys1 = Some t' /\ projectionC g p t' /\ onth n ys2 = Some (x1, g') /\ gttstepC g g' p q l).
    {
      clear H2 H1 H0 H3 H4 H5 H6 H12 H10 H11 H14 H18 H22 H23 H24 H28 H8 H16 H19 H20 H21 H25 H26 H28 H33.
      clear LP LQ. clear s s0.
      revert H H27 H17 H13. revert H34. 
      revert xs p q ys ctxG ys0 ys1 x1 G. revert l ys2.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H27. subst. inversion H13. subst. inversion H17. subst. inversion H34. subst. clear H27 H13 H17 H34.
        simpl in *. subst.
        destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H. 
        destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H6; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        exists x3. exists x6. exists x5. exists x4. pclearbot. destruct H2; try easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H27. subst. inversion H17. subst. inversion H13. subst. inversion H34. subst. apply IHn with (xs := xs); try easy.
    }
    destruct H7. destruct H7. destruct H7. destruct H7. destruct H7. destruct H9. destruct H15. destruct H29.
    destruct H30. destruct H31. destruct H32. 
    rename x into G0'. rename x2 into LP0. rename x3 into LQ0. rename x0 into G''.
    specialize(H8 G0' G'' p q l).
    specialize(merge_onth_recv n p LQ ys0 LP0 H18 H15); intros. destruct H36 as [LQ' H36].
    specialize(merge_onth_send n q LP ys1 LQ0 H28 H30); intros. destruct H37 as [LP' H37].
    subst.
    specialize(H8 LP' LQ' H31 H29 H35).
    assert (exists (LS LS' : sort) (LT LT' : ltt), onth l LP' = Some (LS, LT) /\ onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split. easy. split; try easy.
      intros. apply H4.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst. apply ha_sendq.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        apply ha_sendr with (n := n) (s := x1) (g := G); try easy.
    }
    destruct H36. destruct H36. destruct H36. destruct H36. destruct H36. 
    
    specialize(merge_label_send ys1 LP LP' (x, x2) n l q H28 H30 H36); intros.
    destruct H38. 
    specialize(merge_label_recv ys0 LQ LQ' (x0, x3) n l p H18 H15 H37); intros.
    destruct H39. destruct x4. destruct x5.
    exists s1. exists s2. exists l0. exists l1. easy.
  apply step_mon.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma projection_step_label_s : forall G p q l LP LQ ST,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some ST -> 
  projectionC G q (ltt_recv p LQ) ->
  exists LS' LT', onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(_a_29_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. clear Gl LQ l. clear G.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  }
  clear H3. clear H.
  revert H4 H2 H1 H0. revert G p q l LP LQ ST.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H. destruct H3.
    inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4 (Some G) H5). clear H4 H8.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst.
    pinversion H0; try easy. subst.
    pinversion H2; try easy. subst.
    clear H10 H14 H9 H11 H0 H7 H5 H2 H3 H H4. clear n x.
    revert H16 H13 H1. revert p q LP LQ ST x1.
    induction l; intros.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H16. inversion H13. subst. clear H16 H13.
      simpl in H1. subst.
      destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
      inversion H. subst. 
      exists x3. exists x5. easy.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H16. inversion H13. subst.
      specialize(IHl p q LP LQ ST x1). apply IHl; try easy.
    apply proj_mon. 
    apply proj_mon.
  - destruct H4. destruct H3. destruct H4. 
    inversion H3. subst.
    specialize(SList_to_In xs H11); intros. destruct H6.
    specialize(in_some_implies_onth x0 xs H6); intros. destruct H7. rename x1 into n.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt)))
             (ST : sort * ltt),
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\ g0 = gtt_send p q lsg)) ctxJ) ->
           projectionC G q (ltt_recv p LQ) ->
           onth l LP = Some ST ->
           projectionC G p (ltt_send q LP) ->
           exists (LS' : sort) (LT' : ltt), onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H (Some x0) H6). clear H9 H. destruct H8; try easy.
    destruct H. destruct H. destruct H. inversion H. subst.
    pinversion H0. subst.
    assert False. apply H4. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    rename x1 into s0. rename x2 into g. rename x into ctxG.
    clear H H6 H11 H2 H0 H3.
    assert(exists g' t t', onth n ys = Some (s0, g') /\ typ_gtth ctxG g g' /\ onth n ys0 = Some t /\ projectionC g' p t 
          /\ onth n ys1 = Some t' /\ projectionC g' q t').
    {
      clear H25 H21 H18 H17 H20 H16 H15 H14 H5 H1 H4 H8. clear ST LP LQ. clear s s'. clear l.
      revert H24 H19 H12 H7. revert xs p q ctxG ys s0 g ys0 ys1.
      induction n; intros.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H24. inversion H19. inversion H12. subst. clear H24 H19 H12.
        simpl in H7. subst.
        destruct H16; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H.
        simpl. exists x1. exists x4. exists x5. pclearbot. easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H24. inversion H19. inversion H12. subst. clear H24 H19 H12.
        specialize(IHn xs p q ctxG ys s0 g ys0 ys1). apply IHn; try easy.
    }
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2. destruct H3. destruct H6.
    clear H24 H19 H12.
    rename x into g'. 
    specialize(merge_onth_recv n p LQ ys1 x1 H25 H6); intros. destruct H10. subst.
    specialize(merge_onth_send n q LP ys0 x0 H20 H2); intros. destruct H10. subst.
    rename x1 into LP'. rename x into LQ'.
    
    specialize(H8 g' p q l LP' LQ' ST).
    specialize(merge_label_sendb ys0 LP LP' ST n l q H20 H2 H1); intros. 
    assert (exists (LS' : sort) (LT' : ltt), onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split; try easy. split; try easy.
      intros. apply H4. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
      
    }
    destruct H11. destruct H11.
    specialize(merge_label_recv ys1 LQ LQ' (x, x0) n l p H25 H6 H11); intros. destruct H12.
    destruct x1. exists s1. exists l0. easy.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma _3_19_1 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' p L /\ subtypeC T L. 
Proof.
  intros.
  specialize(_3_19_1_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t. split; try easy.
  
  clear H10 H8 H6 H5 H4 H3 H2 H1 H0 H. clear s' t' xs T' S' LQ G G' p q.
  revert H9 H7. revert LP S T t s.
  induction l; intros; try easy.
  - destruct LP; try easy. inversion H7. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H. subst. simpl in H9. inversion H9. subst. easy.
  - destruct LP; try easy. inversion H7. subst. specialize(IHl LP S T t s). apply IHl; try easy.
Qed.


Lemma _3_19_2 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' q L /\ subtypeC T' L. 
Proof.
  intros.
  specialize(_3_19_2_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t'. split; try easy.
  
  clear H9 H7 H6 H5 H4 H2 H1 H0 H.
  clear s t S T LP G G' p q.
  revert H3 H8 H10. revert LQ S' T' xs t' s'.
  induction l; intros.
  - destruct LQ; try easy. destruct xs; try easy.
    inversion H8. subst. simpl in *. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H0. inversion H. subst. easy.
  - destruct LQ; try easy. destruct xs; try easy. 
    inversion H8. subst. simpl in *. 
    specialize(IHl LQ S' T' xs t' s'). apply IHl; try easy.
Qed.
  
Lemma _3_19_3_helper : forall G G' p q s l L1 L2 S T S' T',
      wfgC G ->
      projectionC G p (ltt_send q L1) ->
      onth l L1 = Some (S, T) ->
      projectionC G q (ltt_recv p L2) ->
      onth l L2 = Some (S', T') ->
      gttstepC G G' p q l ->
      s <> q ->
      s <> p ->
      projectionC G s T -> 
      exists T', (T = T' /\ T = ltt_end) \/ 
                 (exists r xs, p <> r /\ q <> r /\ T = T' /\ T = ltt_send r xs) \/ 
                 (exists r xs ys, p <> r /\ q <> r /\ T = ltt_recv r xs /\ T' = ltt_recv r ys /\ Forall2R (fun u v => u = None \/ u = v) ys xs /\ (SList xs -> SList ys)).
Proof.
Admitted.

Lemma _3_19_step : forall p q l G L1 L2 S T S' T',
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  onth l L1 = Some(S, T) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l L2 = Some(S', T') ->
  exists G', gttstepC G G' p q l.
Proof.
  intros. 
  specialize(_a_29_s G p q L1 L2 S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. rename x into Gl.
  clear H.
  assert (exists (ctxG : list (option gtt)),
       typ_gtth ctxG Gl G /\
       (ishParts p Gl -> False) /\
       (ishParts q Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
                onth l lsg = Some (s', Gjk) /\
                projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG).
  {
    admit.
  }
  clear H4. rename H into H4.
  revert H4 H3 H2 H1 H0. revert S T S' T' L1 L2 G l p q.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H. destruct H4. destruct H5.
    inversion H. subst.
    specialize(some_onth_implies_In n x G H9); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) x); intros.
    destruct H8. specialize(H8 H6 (Some G) H7). clear H6 H10.
    destruct H8; try easy. destruct H6. destruct H6. destruct H6. destruct H8. inversion H6. subst.
    destruct H10. destruct H8. destruct H8. destruct H8. destruct H8. destruct H10.
    pinversion H2; try easy. subst. pinversion H0; try easy. subst.
    clear H15 H14 H16 H11 H10 H0 H9 H7 H1 H2 H3 H5 H4 H H6.
    exists x2. pfold. apply steq with (s := x0); try easy.
    apply proj_mon.
    apply proj_mon.
  - destruct H4. destruct H4. destruct H5. destruct H6. 
    inversion H4. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    rename x into ctxG.
    
    specialize(proj_inv_lis (gtth_send s s' xs) p q l s s' ys ctxG L1 L2); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      apply H8; try easy.
    }
    destruct H9.
    - destruct H9. destruct H10. subst.
      assert False. apply H5. constructor. easy.
    - destruct H9. destruct H10. clear H8.
      pinversion H2; try easy. subst.
      pinversion H0; try easy. subst.
      assert(List.Forall (fun u => u = None \/ exists s g g', u = Some(s, g) /\ gttstepC g g' p q l) ys).
      {
        apply Forall_forall; intros. destruct x. 
        specialize(in_some_implies_onth p0 ys H8); intros. destruct H12. clear H8. rename x into n.
        destruct p0 as [s0 g].
        right. exists s0. exists g.
        
        assert (exists LP LQ T T' g', onth n ys1 = Some (ltt_send q LP) /\ projectionC g p (ltt_send q LP) /\ onth n ys0 = Some (ltt_recv p LQ) /\ projectionC g q (ltt_recv p LQ) /\ onth l LP = Some T /\ onth l LQ = Some T' /\ 
          onth n xs = Some (s0, g') /\
              (forall (S : sort) (T : ltt) (S' : sort) (T' : ltt) (L1 L2 : list (option (sort * ltt)))
             (G : gtt) (l : fin) (p q : string),
           (exists (ctxG : list (option gtt)),
              typ_gtth ctxG g' G /\
              (ishParts p g' -> False) /\
              (ishParts q g' -> False) /\
              Forall
               (fun u : option gtt =>
                u = None \/
                (exists (g : gtt) (lsg : list (option (sort * gtt))),
                   u = Some g /\
                   g = gtt_send p q lsg /\
                   (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
                      onth l lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG) ->
           onth l L2 = Some (S', T') ->
           projectionC G q (ltt_recv p L2) ->
           onth l L1 = Some (S, T) ->
           projectionC G p (ltt_send q L1) -> exists G' : gtt, gttstepC G G' p q l) /\ typ_gtth ctxG g' g
        ).
        { 
          clear H4 H3 H2 H1 H0 H13 H9 H10 H16 H17 H18 H22 H19 H20 H23 H27.
          revert H12 H26 H21 H11 H14 H H5 H6 H7.
          clear S T S' T' L1 L2. 
          revert xs p q ctxG ys ys0 ys1 s0 g l. revert s s'.
          induction n; intros; try easy.
          - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
            inversion H26. inversion H21. inversion H11. inversion H14. inversion H. clear H26 H21 H11 H14 H.
            subst. clear H33 H29 H22 H17 H8.
            simpl in H12. subst. 
            destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst. clear H.
            destruct H15; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst. clear H.
            destruct H27; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H0. subst. clear H0.
            destruct H20; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
            destruct H. destruct H0. destruct H4. destruct H8. inversion H. subst. clear H.
            destruct H32; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
            pclearbot.
            
            exists x6. exists x7. exists x8. exists x9. exists x5.
            assert (ltt_send q x6 = x1). { admit. }
            assert (ltt_recv p x7 = x4). { admit. }
            subst.
            easy.
          - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
            inversion H26. inversion H21. inversion H11. inversion H14. inversion H. clear H26 H21 H11 H14 H.
            subst. 
            specialize(IHn s s' xs p q ctxG ys ys0 ys1 s0 g l). apply IHn; try easy.
            specialize(ishParts_hxs H5); try easy.
            specialize(ishParts_hxs H6); try easy. 
        }
        clear H26 H21 H11 H14 H.
        destruct H8. destruct H. destruct H. destruct H. destruct H. destruct H.
        destruct H8. destruct H11. destruct H14. destruct H15. destruct H21. destruct H24. destruct H25.
        destruct x1. destruct x2.
        specialize(H25 s1 l0 s2 l1 x x0 g l p q).
        assert (exists G' : gtt, gttstepC g G' p q l).
        {
          apply H25; try easy. exists ctxG.
          split; try easy.
          split. intros. apply H5. apply ha_sendr with (n := n) (s := s0) (g := x3); try easy.
          split. intros. apply H6. apply ha_sendr with (n := n) (s := s0) (g := x3); try easy.
          easy.
        }
        destruct H28. exists x1. easy.
        left. easy.
      }
      clear H27 H
    
    
    
  
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
 
  
Admitted.




