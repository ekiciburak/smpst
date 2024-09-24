From SST Require Export type.global type.local type.isomorphism type.projection.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Lemma step_mon : monotone5 gttstep.
Admitted.

Lemma gttT_mon : monotone2 gttT.
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

Lemma triv_merge : forall T T', isMerge T (Some T' :: nil) -> T = T'.
Admitted.

Lemma triv_merge2 : forall T xs, isMerge T xs -> isMerge T (None :: xs).
Admitted.

Lemma merge_onth_recv : forall n p LQ ys1 gqT,
      isMerge (ltt_recv p LQ) ys1 ->
      onth n ys1 = Some gqT -> 
      exists LQ', gqT = ltt_recv p LQ'.
Admitted.

Lemma merge_onth_send : forall n q LP ys0 gpT,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some gpT ->
      exists LP', gpT = (ltt_send q LP').
Admitted.


Lemma more_merge_sub: forall T T' o0 ys0,
          isMerge T ys0 ->
          isMerge T' (o0 :: ys0) ->
          subtypeC T' T.
Admitted.

Lemma merge_label_recv : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          exists T', onth l LQ' = Some T'.
Admitted.

Lemma merge_label_send : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          exists T', onth l LP' = Some T'. 
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
    subst. clear H14. split; try easy. 
    pinversion H5; try easy. subst. split; try easy. 
    rename p0 into p. rename q0 into q. clear H20.
    pinversion H6; try easy. subst.
    apply Forall_forall; intros; try easy. destruct x.
    - right. destruct p0. clear H14 H16 H17.
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
        clear H7 H28 H27 H26 H25 H22 H21 H20 H24 H19 H13 H12 H11 H6 H5 H4 H3 H1 H0 H10.
        clear H2. revert H8 H34 H33 H23 H18 H15 H. revert xs p q l s s' ctxG T T' SI LP LQ ys2 ys0 ys1 s0 g n.
        induction ys; intros; try easy. destruct n; try easy. 
        destruct ys2; try easy. destruct ys1; try easy. destruct xs; try easy. destruct ys0; try easy.
        inversion H34. subst. clear H34. inversion H. subst. clear H.
        inversion H33. subst. clear H33. inversion H23. subst. clear H23.
        inversion H18. subst. clear H18. inversion H15. subst. clear H15.
        
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
      clear H34 H33 H23 H18 H15 H. clear H11 H12 H13.
      destruct H9. destruct H. destruct H. destruct H. destruct H. destruct H9. destruct H11.
      destruct H12. destruct H13. destruct H14. destruct H15. destruct H16.
      rename x0 into gpT. rename x1 into g'. rename x2 into g''. rename x into gqT.
      destruct g; try easy. pinversion H16; try easy. apply step_mon.
      specialize(H17 p q l s1 s2 l0 ctxG T T' SI).
      specialize(merge_onth_send n q LP ys0 gpT H19 H11); intros. destruct H18. subst.
      specialize(merge_onth_recv n p LQ ys1 gqT H24 H); intros. destruct H18. subst.
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
          clear H8 H9 H12 H11 H13 H14 H15 H16 H18 H23 H17 H34 H30 H.
          clear xs s s' ys ctxG T T' s0 LP LQ ys2 ys0 ys1 s0 g' g''. clear SI n.
          revert H31 H32 H36.
          revert p q l LQ' LP' s1 g. induction l0; intros; try easy.
          destruct l; try easy.
          destruct LQ'; try easy. destruct LP'; try easy. 
          inversion H32. subst. inversion H36. subst. clear H32 H36.
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
          clear H44 H50.
          clear H38 H36 H30 H29 H17 H18 H23 H16 H15 H13 H14 H11 H8 H7 H28 H27.
          clear H26 H25 H22 H21 H20 H24 H19 H10 H6 H5 H4 H3 H2 H1 H0 H.
          assert (exists t t', onth x ys3 = Some t /\ projectionC x1 q t /\ onth x ys4 = Some t' /\ projectionC x1 p t').
          {
              clear H49 H46 H45 H43 H42 H41 H34 H33 H48 H54 H12 H9 .
              clear xs s s' ys T T' SI LP LQ ys2 ys0 ys1. clear xs0 g''. clear n. clear ctxG.
              revert H32 H35 H37 H47 H53. 
              revert p q l s0 s1 s2 LQ' LP' x x0 x1 LP0' LQ0' x4 x5 ys3 ys4.
              induction l0; intros; try easy.
              - destruct x; try easy.
              - destruct ys3; try easy. destruct ys4; try easy.
              inversion H47. subst. inversion H53. subst. clear H47 H53.
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
          specialize(merge_label_send Mq LP' LP0' x4 k l q H54 H1 H35); intros.
          destruct H3. 
          specialize(merge_label_recv Mp LQ' LQ0' x5 k l p H48 H H37); intros.
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
    clear H20 H31 H15 H16 H19 H28 H29 H30 H21 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T)) ys2).
    {
      clear H5 H4 H2 H0 H17.
      
    }
    
    
    
    revert H H0 H1 H2 H3 H4 H5. revert s s' p q l G G' LP LQ S S' T T'.
    - induction xs; intros; try easy.
      destruct H5. destruct H5. destruct H5. destruct H5. inversion H5; try easy.
    - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10. inversion H5. subst.
      specialize(IHxs s s' p q l); intros. rename x1 into Sn. rename x0 into SI. rename x into ctxG.
      
      pinversion H0; try easy.
      - subst. assert False. apply H6. constructor. easy.
      pinversion H2; try easy.
      subst. clear H20 H31. 
      pinversion H4; try easy. subst.
      clear H28 H29 H30. 
      
      destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy. destruct ys2; try easy.
      specialize(IHxs (gtt_send s s' ys) (gtt_send s s' ys2) LP LQ S S' T T').
      
      specialize(SList_f a xs H17); intros. clear H17.
      destruct H12.
      - assert (projectionC (gtt_send s s' ys2) p T).
        {
          apply IHxs; try easy.
          inversion H; try easy.
        }
      - destruct H12. destruct H13. subst.
        inversion H18. subst. clear H18. inversion H38. subst. clear H38.
        inversion H39. subst. clear H39. inversion H. subst. clear H.
        inversion H34. subst. clear H34. inversion H23. subst. clear H23.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy. destruct ys2; try easy.
        clear H39 H38 H32 H33 H18 H29 IHxs.
        destruct H17; try easy. destruct H. destruct H. destruct H. destruct H. destruct H12.
        inversion H. subst. clear H.
        destruct H30; try easy. destruct H. destruct H. destruct H. destruct H. destruct H12.
        inversion H. subst. clear H.
        destruct H34; try easy. destruct H. destruct H. destruct H. destruct H. destruct H12.
        inversion H. subst. clear H.
        destruct H14; try easy. destruct H. destruct H. destruct H. destruct H12.
        inversion H. subst. clear H.
        destruct H36; try easy. destruct H. destruct H. destruct H. destruct H. destruct H23. 
        inversion H. subst. clear H.
        destruct H28; try easy. destruct H. destruct H. destruct H.
        inversion H. subst. clear H.
        specialize(H23 p q l).
        rename x2 into G. rename x4 into G'. rename x3 into Gl.
        specialize(triv_merge (ltt_send q LP) x5 H24); intros. subst.
        specialize(triv_merge (ltt_recv p LQ) x6 H35); intros. subst.
        specialize(H23 G G' LP LQ S S' T T').
        assert (projectionC G' p T).
        {
          pclearbot.
          apply H23; try easy.
          destruct H17; try easy.
          exists ctxG. exists SI. exists Sn. 
          split. easy.
          split; intros.
          - apply H6. 
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              apply ha_sendr with (n := 0) (s := x) (g := Gl); try easy.
          split; intros.
          - apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              apply ha_sendr with (n := 0) (s := x) (g := Gl); try easy.
          split; try easy.
        }
        clear H23 H8.
        destruct T.
        - pinversion H; try easy. subst.
          pfold. constructor; try easy. intros. apply H8.
          - admit. (* isParts in continuation *)
          apply proj_mon.
        - pfold.
          apply proj_cont with (ys := (Some (ltt_recv s0 l0) :: nil)); try easy.
          constructor; try easy. right. exists x. exists G'. exists (ltt_recv s0 l0). 
          split. easy. split. easy. left. easy.
        - pfold. 
          apply proj_cont with (ys := (Some (ltt_send s0 l0) :: nil)); try easy. 
          constructor; try easy. right. exists x. exists G'. exists (ltt_send s0 l0).
          split. easy. split. easy. left. easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.

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
        assert (exists L, projectionC (gtt_send s s' (Some (x1, G') :: ys2)) p L). { admit. }
        destruct H9. exists x0. rename x0 into L. split; try easy.
        pinversion H9; try easy. subst. admit. (* doable, a bit tedious *)
        - subst.
        
        
        destruct x.
        - exists ltt_end. split; try easy.
          pfold. constructor; try easy.
          admit. (* doable, a bit tedious *)
        - 
        
      admit. admit.
       
     


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
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
  
  
  revert H H0 H1 H2 H3 H4 H5 H6 H7.
    
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
        assert (exists L, projectionC (gtt_send s s' (Some (x1, G') :: ys2)) p L). { admit. }
        destruct H9. exists x0. rename x0 into L. split; try easy.
        pinversion H9; try easy. subst. admit. (* doable, a bit tedious *)
        - subst.
        
        
        destruct x.
        - exists ltt_end. split; try easy.
          pfold. constructor; try easy.
          admit. (* doable, a bit tedious *)
        - 
        
      admit. admit.
       
      
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
      