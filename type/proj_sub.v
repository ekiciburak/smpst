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

Lemma in_some_implies_onth {A} : forall (x : A) xs,
    In (Some x) xs -> exists n, onth n xs = Some x.
Proof.
  intros. revert H. revert x. 
  induction xs; intros; try easy.
  simpl in *. destruct H. exists 0. easy.
  specialize(IHxs x H). destruct IHxs. exists (Nat.succ x0). easy.
Qed.

Lemma proj_inv_lis : forall Gl p q l s s' ys ctxG T T' SI LP LQ G',
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
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s)) lsg SI))
       ctxG ->
    typ_gtth ctxG Gl (gtt_send s s' ys) ->
    projectionC (gtt_send s s' ys) p (ltt_send q LP) -> 
    projectionC (gtt_send s s' ys) q (ltt_recv p LQ) -> 
    gttstepC (gtt_send s s' ys) G' p q l ->
    (s = p /\ s' = q /\ exists Gk, onth l ys = Some Gk) \/
    (s <> p /\ s' <> q /\ List.Forall (fun u => u = None \/ 
        (exists s g LP' LQ' T T', u = Some(s, g) /\ projectionC g p (ltt_send q LP') /\ projectionC g q (ltt_recv p LQ') /\ 
          onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
Proof.
  intro Gl. induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H2. subst.
    specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H8); intros.
    specialize(Forall_forall (fun u : option gtt =>
            u = None \/
            (exists (g : gtt) (lsg : list (option (sort * gtt))),
               u = Some g /\
               g = gtt_send p q lsg /\
               (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
                  onth l lsg = Some (s', Gjk) /\
                  projectionC Gjk p Tp /\
                  T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
               Forall2
                 (fun (u0 : option (sort * gtt)) (v : option sort) =>
                  u0 = None /\ v = None \/
                  (exists (s : sort) (g' : gtt),
                     u0 = Some (s, g') /\ v = Some s)) lsg SI)) ctxG); intros. destruct H7.
    specialize(H7 H1). clear H1 H9. specialize(H7 (Some (gtt_send s s' ys)) H6).
    destruct H7; try easy. destruct H1. destruct H1. destruct H1. destruct H7. destruct H9.
    destruct H9. destruct H9. destruct H9. destruct H9. destruct H9. destruct H11. destruct H12. destruct H13. destruct H14. 
    subst. inversion H1. subst.
    left. split; try easy. split; try easy. exists (x1, x2). easy.
  - inversion H3. subst. right. 
    pinversion H4; try easy. subst.
    assert False. apply H0. constructor. easy.
    subst. split; try easy. 
    pinversion H5; try easy. subst. split; try easy. 
    rename p0 into p. rename q0 into q. 
    pinversion H6; try easy. subst.
    apply Forall_forall; intros; try easy. destruct x.
    - right. destruct p0. clear H14 H16 H19.
      specialize(in_some_implies_onth (s0, g) ys H7); intros. destruct H8. rename x into n.
      assert(exists t t' g' g'', onth n ys1 = Some t /\ projectionC g q t /\ onth n ys0 = Some t' /\ projectionC g p t' /\ onth n xs = Some (s0, g') /\ typ_gtth ctxG g' g /\ onth n ys2 = Some (s0, g'') /\ gttstepC g g'' p q l /\ 
              (forall (p q : string) (l : fin) (s0 s' : string)
                 (ys : list (option (sort * gtt))) (ctxG : list (option gtt)) 
                 (T T' : ltt) (SI : list (option sort)) (LP LQ : list (option (sort * ltt)))
                 (G' : gtt),
               (ishParts p g' -> False) ->
               (ishParts q g' -> False) ->
               Forall
                 (fun u0 : option gtt =>
                  u0 = None \/
                  (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                     u0 = Some g0 /\
                     g0 = gtt_send p q lsg /\
                     (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                        onth l lsg = Some (s'0, Gjk) /\
                        projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
                     Forall2
                       (fun (u1 : option (sort * gtt)) (v : option sort) =>
                        u1 = None /\ v = None \/
                        (exists (s1 : sort) (g' : gtt), u1 = Some (s1, g') /\ v = Some s1))
                       lsg SI)) ctxG ->
               typ_gtth ctxG g' (gtt_send s0 s' ys) ->
               projectionC (gtt_send s0 s' ys) p (ltt_send q LP) ->
               projectionC (gtt_send s0 s' ys) q (ltt_recv p LQ) ->
               gttstepC (gtt_send s0 s' ys) G' p q l ->
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
        clear H7 H28 H27 H26 H25 H21 H20 H24 H13 H12 H11 H6 H5 H4 H3 H1 H0 H10.
        clear H23 H18.
        clear H2. revert H8 H34 H33 H15 H17 H22 H. revert xs p q l s s' ctxG T T' SI LP LQ ys2 ys0 ys1 s0 g n.
        induction ys; intros; try easy. destruct n; try easy. 
        destruct ys2; try easy. destruct ys1; try easy. destruct xs; try easy. destruct ys0; try easy.
        inversion H34. subst. clear H34. inversion H. subst. clear H.
        inversion H33. subst. clear H33. inversion H22. subst. clear H22.
        inversion H17. subst. clear H17. inversion H15. subst. clear H15.
        
        destruct n.
        - simpl in *. subst.
          destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
          inversion H. subst. clear H.
          clear H16 H13 H11 H6 H4 H5 IHys.
          destruct H1; try easy. destruct H. destruct H. destruct H. destruct H0. 
          inversion H. subst. clear H.
          destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H4. 
          inversion H. subst. clear H.
          destruct H10; try easy. destruct H. destruct H. destruct H. destruct H. destruct H4.
          inversion H. subst. clear H.
          destruct H12; try easy. destruct H. destruct H. destruct H. destruct H. destruct H4.
          inversion H4. subst. clear H4.
          destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          exists x4. exists x5. exists x3. exists x1. pclearbot. easy.
        - simpl in *.
          apply IHys; try easy.
      }
      clear H34 H33 H22 H17 H15 H. clear H11 H12 H13.
      destruct H9. destruct H. destruct H. destruct H. destruct H. destruct H9. destruct H11.
      destruct H12. destruct H13. destruct H14. destruct H15. destruct H16.
      rename x0 into gpT. rename x1 into g'. rename x2 into g''. rename x into gqT.
      destruct g; try easy. pinversion H16; try easy. apply step_mon.
      specialize(H17 p q l s1 s2 l0 ctxG T T' SI).
      specialize(merge_onth_send n q LP ys0 gpT H18 H11); intros. destruct H19. subst.
      specialize(merge_onth_recv n p LQ ys1 gqT H23 H); intros. destruct H19. subst.
      rename x0 into LQ'. rename x into LP'.
      specialize(H17 LP' LQ' g''). 
      exists s0. exists (gtt_send s1 s2 l0). exists LP'. exists LQ'.
      assert (ishParts p g' -> False).
      {
        intros. apply H0.
        - case_eq (eqb p s); intros.
          assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
        - case_eq (eqb p s'); intros.
          assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
        - assert (p <> s). apply eqb_neq; try easy. 
          assert (p <> s'). apply eqb_neq; try easy.
          apply ha_sendr with (n := n) (s := s0) (g := g'); try easy. 
      }
      assert (ishParts q g' -> False).
      {
        intros. apply H1.
        - case_eq (eqb q s); intros.
          assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
        - case_eq (eqb q s'); intros.
          assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
        - assert (q <> s). apply eqb_neq; try easy. 
          assert (q <> s'). apply eqb_neq; try easy.
          apply ha_sendr with (n := n) (s := s0) (g := g'); try easy.
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
        apply H17; try easy.
      }
      
      destruct H29.
      - destruct H29. destruct H30. destruct H31. subst. clear H17 H2.
        pinversion H9; try easy. subst. pinversion H12; try easy. subst.
        destruct x.
        assert(exists T0 T'0, onth l LP' = Some T0 /\ onth l LQ' = Some T'0).
        {
          clear H0 H1 H3 H4 H5 H6 H10 H19 H24 H20 H21 H22 H25 H26 H27 H28 H7.
          clear H8 H9 H12 H11 H13 H14 H15 H16 H18 H23 H30 H H29 H35 H32.
          clear xs s s' ys ctxG T T' s0 LP LQ ys2 ys0 ys1 s0 g' g''. clear SI n.
          revert H31 H34 H37.
          revert p q l LQ' LP' s1 g. induction l0; intros; try easy.
          destruct l; try easy.
          destruct LQ'; try easy. destruct LP'; try easy. 
          inversion H34. subst. inversion H37. subst. clear H34 H37.
          destruct l. simpl in *. subst.
          destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
          inversion H. subst. clear H.
          destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
          inversion H. subst. clear H.
          exists (x2, x4). exists (x2, x1). split; try easy.
          specialize(IHl0 p q l LQ' LP' s1 g). apply IHl0; try easy.
        }
        destruct H2. destruct H2. exists x. exists x0.
        split. easy. split. pfold. easy. split. pfold. easy. easy.
        apply proj_mon. apply proj_mon. 
      - destruct H29. destruct H30. 
        inversion H14. subst.
        - clear H31 H17 H18 H23 H16 H15 H13 H14 H11 H12 H H9 H8 H7 H28 H27 H26 H25 H22 H21 H20 H24 H19.
          clear H10 H6 H5 H4 H3 H1 H0.
          assert False.
          clear LQ' LP' g'' n s0 ys0 ys1 ys2. clear LP LQ ys s s'. clear xs.
          revert H32 H30 H29 H2. revert p q l T T' SI s1 s2 l0 n0.
          induction ctxG; intros; try easy. destruct n0; try easy.
          inversion H2. subst. clear H2. 
          destruct n0. simpl in H32.
          - subst. destruct H1; try easy. destruct H. destruct H. destruct H.
            destruct H0. inversion H. subst. inversion H4. subst. easy.
          - specialize(IHctxG p q l T T' SI s1 s2 l0 n0). apply IHctxG; try easy.
            easy.
        - subst.
          assert (exists k s4 g2 LP' LQ' T0 T'0, onth k l0 = Some(s4, g2) /\ projectionC g2 p (ltt_send q LP') /\ projectionC g2 q (ltt_recv p LQ') /\ onth l LP' = Some T0 /\ onth l LQ' = Some T'0).
          {
            clear H30 H29 H17 H18 H23 H16 H15 H13 H14 H11 H12 H9 H8 H7 H28 H27 H26 H25 H22 H21 H.
            clear H20 H24 H19 H10 H6 H5 H4 H3 H2 H1 H0. revert H38 H36 H31.
            revert xs p q l s s' ys ctxG T T' SI LP LQ ys2 ys0 ys1 s0 s1 s2 l0 n g'' LQ' LP'.
            induction xs0; try easy.
            intros.
            destruct l0; try easy. inversion H38. subst. inversion H31. subst. clear H31 H38.
            specialize(SList_f a xs0 H36); intros. destruct H.
            assert (exists (k : fin) (s4 : sort) (g2 : gtt) (LP' LQ'0 : list (option (sort * ltt))) 
        (T0 T'0 : sort * ltt),
          onth k l0 = Some (s4, g2) /\
          projectionC g2 p (ltt_send q LP') /\
          projectionC g2 q (ltt_recv p LQ'0) /\ onth l LP' = Some T0 /\ onth l LQ'0 = Some T'0).
            {
              apply IHxs0 with (p := p) (q := q) (l0 := l0) (ctxG := ctxG); try easy.
            }
            destruct H0. exists (Nat.succ x). easy.
            
            destruct H. destruct H0. subst. destruct l0; try easy.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H1; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
            destruct H0. destruct H0. destruct H1. destruct H5. destruct H6. inversion H0. subst.
            exists 0. exists x. exists x3. exists x4. exists x5. exists x6. exists x7. easy.
          }
          destruct H32. destruct H32. destruct H32. destruct H32. destruct H32. 
          destruct H32. destruct H32. destruct H32. destruct H33. destruct H34. 
          destruct H35. rename x2 into LP0'. rename x3 into LQ0'. clear H31.
          
          pinversion H9; try easy. subst.
          pinversion H12; try easy. subst. 
          clear H38 H36 H30 H29 H17 H18 H23 H16 H15 H13 H14 H11 H8 H7 H28 H27.
          clear H26 H25 H22 H21 H20 H24 H19 H10 H6 H5 H4 H3 H2 H1 H0 H.
          assert (exists t t', onth x ys3 = Some t /\ projectionC x1 q t /\ onth x ys4 = Some t' /\ projectionC x1 p t').
          {
              clear H48 H45 H44 H43 H42 H41 H34 H33 H47 H52 H12 H9 .
              clear xs s s' ys T T' SI LP LQ ys2 ys0 ys1. clear xs0 g''. clear n. clear ctxG.
              revert H32 H35 H37 H46 H51. 
              revert p q l s0 s1 s2 LQ' LP' x x0 x1 LP0' LQ0' x4 x5 ys3 ys4.
              induction l0; intros; try easy.
              - destruct x; try easy.
              - destruct ys3; try easy. destruct ys4; try easy.
              inversion H46. subst. inversion H51. subst. clear H46 H51.
              destruct x.
              - simpl in H32. subst. destruct H2; try easy. destruct H. destruct H. destruct H.
                destruct H. destruct H0. inversion H. subst.
                destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
                inversion H0. subst.
                exists x3. exists x6. pclearbot. easy.
              - simpl. apply IHl0 with (l := l) (x0 := x0) (x4 := x4) (x5 := x5) (LP0' := LP0') (LQ0' := LQ0'); try easy.
          }
          destruct H. destruct H. destruct H. destruct H0. destruct H1.
          specialize(proj_inj H2 H33); intros. subst.
          specialize(proj_inj H0 H34); intros. subst.
          rename ys3 into Mp. rename ys4 into Mq. rename x into k.
          specialize(merge_label_send Mq LP' LP0' x4 k l q H52 H1 H35); intros.
          destruct H3. 
          specialize(merge_label_recv Mp LQ' LQ0' x5 k l p H47 H H37); intros.
          destruct H4.
          exists x. exists x2. pclearbot. split. easy. split. pfold. easy. split. pfold. easy. easy.
        apply proj_mon.
        apply proj_mon.
    - left. easy.
    apply step_mon. apply proj_mon. apply proj_mon.
Qed.

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
    pinversion H4; try easy. subst. specialize(eq_trans H25 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis (gtth_send s s' xs) p q l s s' ys ctxG T T' SI LP LQ (gtt_send s s' ys2)); intros.
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
      apply H12; try easy. pfold. easy. pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H27 H28 H29 H20 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T)) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' H34 H22 H23 H32 H33 H1 H3); intros.
      clear H34 H33 H22.
      clear H23 H30 H21 H24 H25 H26 H31 H32 H38 H3 H1. 
      revert H0 H39 H18 H8 H7 H6 H H9 H10 H11. clear ys0 ys1 LP LQ. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H39. subst. clear H39.
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
      clear H34 H38 H31 H30 H26 H25 H24 H21 H33 H32 H23 H22 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H17 H18 H12 H39.
      revert s s' xs p q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H39. subst. clear H18 H12 H39.
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
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H17 H18 H22 H23 H32 H33 H21 H24 H25 H26 H30 H31 H38 H39 H34 H12 H14.
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
Qed.

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
    pinversion H4; try easy. subst. specialize(eq_trans H25 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis (gtth_send s s' xs) p q l s s' ys ctxG T T' SI LP LQ (gtt_send s s' ys2)); intros.
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
      apply H12; try easy. pfold. easy. pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H27 H28 H29 H20 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g q T')) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' H34 H22 H23 H32 H33 H1 H3); intros.
      clear H34 H33 H22.
      clear H23 H30 H21 H24 H25 H26 H31 H32 H38 H3 H1. 
      revert H0 H39 H18 H8 H7 H6 H H9 H10 H11. clear ys0 ys1 LP LQ. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H39. subst. clear H39.
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
      clear H34 H38 H31 H30 H26 H25 H24 H21 H33 H32 H23 H22 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H17 H18 H12 H39.
      revert s s' xs p q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H39. subst. clear H18 H12 H39.
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
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H17 H18 H22 H23 H32 H33 H21 H24 H25 H26 H30 H31 H38 H39 H34 H12 H14.
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
Qed.

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
    clear H9 H16 H15 H14 H11 H8 H10 H7 H3 H0 H1 H2 H4 H H17. clear n x.
    revert H12 H18 H20. revert G' p q LP LQ x1 s.
    induction l; intros; try easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H20. subst. clear H20. inversion H12. subst. clear H12. 
      simpl in *. subst.
      destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H. subst.
      destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      inversion H0. subst.
      exists x3. exists x3. exists x2. exists x5. easy.
    - destruct x1; try easy. destruct LP; try easy. destruct LQ; try easy.
      inversion H12. subst. inversion H20. subst.
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
      clear H2 H1 H0 H3 H4 H5 H6 H12 H10 H11 H14 H18 H22 H23 H24 H28 H8 H16 H19 H20 H21 H25 H26 H29 H34.
      clear LP LQ. clear s s0.
      revert H H27 H17 H13. revert H35. 
      revert xs p q ys ctxG ys0 ys1 x1 G. revert l ys2.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H27. subst. inversion H13. subst. inversion H17. subst. inversion H35. subst. clear H27 H13 H17 H35.
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
        inversion H27. subst. inversion H17. subst. inversion H13. subst. inversion H35. subst. apply IHn with (xs := xs); try easy.
    }
    destruct H7. destruct H7. destruct H7. destruct H7. destruct H7. destruct H9. destruct H15. destruct H30.
    destruct H31. destruct H32. destruct H33. 
    rename x into G0'. rename x2 into LP0. rename x3 into LQ0. rename x0 into G''.
    specialize(H8 G0' G'' p q l).
    specialize(merge_onth_recv n p LQ ys0 LP0 H18 H15); intros. destruct H37 as [LQ' H37].
    specialize(merge_onth_send n q LP ys1 LQ0 H28 H31); intros. destruct H38 as [LP' H38].
    subst.
    specialize(H8 LP' LQ' H32 H30 H36).
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
    destruct H37. destruct H37. destruct H37. destruct H37. destruct H37. 
    
    specialize(merge_label_send ys1 LP LP' (x, x2) n l q H28 H31 H37); intros.
    destruct H39. 
    specialize(merge_label_recv ys0 LQ LQ' (x0, x3) n l p H18 H15 H38); intros.
    destruct H40. destruct x4. destruct x5.
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
  
Admitted.




