From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.merge.
Require Import List String Coq.Arith.PeanoNat Relations.
Import ListNotations. 

Inductive isgParts : part -> global -> Prop := 
  | pa_sendp : forall p q l, isgParts p (g_send p q l)
  | pa_sendq : forall p q l, isgParts q (g_send p q l)
  | pa_mu    : forall p g,   isgParts p g -> isgParts p (g_rec g)
  | pa_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> isgParts r g -> isgParts r (g_send p q lis).
  
Definition isgPartsC (pt : part) (G : gtt) : Prop := 
    exists G', gttTC G' G /\ isgParts pt G'.

Inductive ishParts : part -> gtth -> Prop := 
  | ha_sendp : forall p q l, ishParts p (gtth_send p q l)
  | ha_sendq : forall p q l, ishParts q (gtth_send p q l)
  | ha_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> ishParts r g -> ishParts r (gtth_send p q lis).


Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, 
               (isgPartsC r g -> False) -> 
               projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ R g r t)) xs ys ->
               isMerge t ys ->
               projection R (gtt_send p q xs) r t.

Definition projectionC g r t := paco3 projection bot3 g r t.

Lemma proj_mon: monotone3 projection.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor. easy.
       - try easy.
Admitted.
(* 
Lemma wfg_to_wfl : forall G p T,
  wfgC G -> 
  projectionC G p T ->
  wfC T.
Admitted. *)

Lemma lttT_mon : monotone2 lttT.
Admitted.
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

Lemma pmergeCR: forall G r,
          wfgC G ->
          projectionC G r ltt_end ->
          (isgPartsC r G -> False).
Proof. intros.
Admitted.

Variant gttstep (R: gtt -> gtt -> part -> part -> nat -> Prop): gtt -> gtt -> part -> part -> nat -> Prop :=
  | steq : forall p q xs s gc n,
                  p <> q ->
                  Datatypes.Some (s, gc) = onth n xs ->
                  gttstep R (gtt_send p q xs) gc p q n
  | stneq: forall p q r s xs ys n,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) xs ->
                  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g' p q n)) xs ys ->
                  gttstep R (gtt_send r s xs) (gtt_send r s ys) p q n.

Definition gttstepC g1 g2 p q n := paco5 gttstep bot5 g1 g2 p q n. 

Lemma proj_inj_p [G p T T' ctxG q Gl] :  
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg))
       ctxG ->
  (ishParts p Gl -> False) ->
  typ_gtth ctxG Gl G ->
  projectionC G p T -> projectionC G p T' -> T = T'.
Admitted.

Lemma proj_inj_q [G p T T' ctxG q Gl] :  
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg))
       ctxG ->
  (ishParts q Gl -> False) -> 
  typ_gtth ctxG Gl G ->
  projectionC G q T -> projectionC G q T' -> T = T'.
Admitted.


Lemma _a_29_10 : forall G p q PT S T n,
    projectionC G p PT ->
    subtypeC (ltt_send q (extendLis n (Some (S, T)))) PT ->
    exists (xs : list (option (sort * ltt))) (Sk : sort) (Tk : ltt), projectionC G p (ltt_send q xs) /\ 
    onth n xs = Some(Sk, Tk) /\ subsort S Sk /\ subtypeC T Tk.
Proof.
  intros.
  specialize(subtype_send PT q (extendLis n (Some (S, T))) H0); intros.
  destruct H1. subst.
  specialize(subtype_send_inv q (extendLis n (Some (S,T))) x H0); intros.
  exists x.
  assert (exists Sk Tk, onth n x = Some (Sk, Tk) /\ subsort S Sk /\ subtypeC T Tk).
  {
    clear H0. clear H. revert G p q S T x H1.
    induction n; intros; try easy.
    - destruct x; try easy.
      simpl in *. inversion H1. subst. destruct H3; try easy.
      destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2.
      inversion H. subst.
      exists x1. exists x3. try easy.
    - destruct x; try easy. apply IHn; try easy.
      inversion H1; try easy.
  }
  destruct H2. destruct H2. destruct H2. destruct H3.
  exists x0. exists x1. try easy.
Qed.

Lemma _a_29_11_helper : forall G p q x, 
    wfgC G -> 
    projectionC G p (ltt_send q x) -> 
    exists G' ctxJ,
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg)) ctxJ.
Proof.
  intros.
  unfold wfgC in H. destruct H as [G' H1].
  destruct H1. destruct H1. destruct H2. 
  revert H H1 H2 H3 H0. revert G p q x.
  induction G' using global_ind_ref; intros; try easy.
  
Admitted.

Lemma _a_29_11 : forall G p q x,
    wfgC G ->
    projectionC G p (ltt_send q x) ->
    exists G' ctxJ, 
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t g', u = Some(s, g') /\ v = Some(s, t) /\
          projectionC g' p t
        )) lsg x 
      )) ctxJ.
Proof.
    intros.
Admitted.

Lemma some_onth_implies_In {A} : forall n (ctxG : list (option A)) G,
    onth n ctxG = Some G -> In (Some G) ctxG.
Proof.
  induction n; intros; try easy.
  - destruct ctxG; try easy. simpl in *.
    left. easy.
  - destruct ctxG; try easy. simpl in *.
    right. apply IHn; try easy.
Qed.

Lemma _a_29_1314 : forall G G' p q QT xs ctxG x,
    Forall
        (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x))
        ctxG -> 
  typ_gtth ctxG G' G ->
  (ishParts p G' -> False) ->
  projectionC G q QT ->
  subtypeC (ltt_recv p xs) QT -> 
  exists ys, projectionC G q (ltt_recv p ys) /\ List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t'))) ys x.
Proof.
  
Admitted.


Lemma _a_29_part : forall ctxG G' G p q x ys,
    typ_gtth ctxG G' G -> 
    projectionC G p (ltt_send q x) ->
    projectionC G q (ltt_recv p ys) ->
    (ishParts p G' -> False) -> 
    (ishParts q G' -> False).
Proof.
    intros ctxG G'. revert ctxG.
    induction G' using gtth_ind_ref; intros; try easy.
    rename p into r. rename q into s. rename p0 into p. rename q0 into q.
    inversion H0. subst.
    inversion H4; try easy. 
    - subst.
      pinversion H2; try easy. subst.
      apply proj_mon.
    - subst. 
      pinversion H2; try easy. subst.
      apply H3. constructor.
      apply proj_mon.
    - subst.
      specialize(some_onth_implies_In n xs (s0, g) H13); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (x ys : seq.seq (option (sort * ltt))),
           typ_gtth ctxG g G ->
           projectionC G p (ltt_send q x) ->
           projectionC G q (ltt_recv p ys) ->
           (ishParts p g -> False) -> ishParts q g -> False))) xs); intros.
    destruct H6. specialize(H6 H). clear H H7.
    specialize(H6 (Some (s0, g)) H5).
    destruct H6; try easy.
    destruct H. destruct H. destruct H.
    inversion H. subst. clear H.
    case_eq (eqb p s); intros; try easy.
    - assert (p = s). apply eqb_eq; easy. subst. apply H3. constructor.
    case_eq (eqb p r); intros; try easy.
    - assert (p = r). apply eqb_eq; easy. subst. apply H3. constructor.
    assert (p <> s). apply eqb_neq; try easy.
    assert (p <> r). apply eqb_neq; try easy.
    assert (ishParts p x1 -> False). 
    {
      intros. apply H3.
      apply ha_sendr with (n := n) (s := x0) (g := x1); try easy.
    }
    assert (exists g', typ_gtth ctxG x1 g' /\ onth n ys0 = Some (x0, g')).
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H6 H H7 H9 H15 H16. clear p q r s.
      clear x ys.
      revert H11 H13. revert xs ctxG ys0 x0 x1.
      induction n; intros; try easy.
      - destruct xs; try easy. 
        destruct ys0; try easy.
        inversion H11. simpl in *. subst.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst.
        exists x3; try easy.
      - destruct xs; try easy.
        destruct ys0; try easy.
        apply IHn with (xs := xs) (ys0 := ys0) (x0 := x0); try easy.
        inversion H11. easy.
    }
    destruct H17. 
    specialize(H6 ctxG x2 p q).
    pinversion H2; try easy. subst.
    pinversion H1; try easy. subst. destruct H17.
    assert (exists t t', projectionC x2 p t /\ projectionC x2 q t' /\ onth n ys2 = Some t /\ onth n ys1 = Some t').
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H13 H6 H H7 H9 H15 H16 H17 H21 H22 H23 H24. clear H27 H25 H28 H32 H11.
      clear r s x1 x ys xs ctxG.
      revert H18 H26 H31. revert p q x0 x2 ys0 ys1 ys2.
      induction n; intros; try easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H26. subst. inversion H31. subst. clear H26 H31.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. inversion H0. subst.
        pclearbot. exists x4. exists x3. easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H26. subst. inversion H31. subst. clear H26 H31.
        apply IHn with (x0 := x0) (ys0 := ys0) (ys1 := ys1) (ys2 := ys2); try easy.
    }
    destruct H19. destruct H19. destruct H19. destruct H20. destruct H29.
    specialize(_a_29_part_helper_recv n ys1 x4 p ys H30 H27); intros. destruct H33. subst.
    specialize(_a_29_part_helper_send n ys2 x3 q x H29 H32); intros. destruct H33. subst.
    specialize(H6 x4 x5). apply H6; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _a_29_16 : forall G' ctxG G p q ys x, 
    projectionC G q (ltt_recv p ys) -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG ->
    (ishParts p G' -> False) ->
    (ishParts q G' -> False) -> 
    typ_gtth ctxG G' G -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x /\
              Forall2
                (fun u v => (u = None /\ v = None) \/ 
                 (exists s t g', u = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys
              )) ctxG.
Proof.
  
  
Admitted.


Lemma _a_29_helper : forall n x Sk Tk lsg p,
    onth n x = Some (Sk, Tk) ->
    Forall2 
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
    exists Glsg, onth n lsg = Some (Sk, Glsg) /\ projectionC Glsg p Tk.
Proof.
  induction n; intros; try easy.
  - destruct x; try easy.
    destruct lsg; try easy.
    simpl in *. subst.
    inversion H0. subst. destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H1. subst.
    exists x2. split; try easy.
  - destruct x; try easy. destruct lsg; try easy.
    inversion H0. subst.
    simpl in *. apply IHn with (x := x); try easy.
Qed.

Lemma _a_29_helper2 : forall lsg SI x p,
      Forall2
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
      Forall2
        (fun (u : option sort) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (t : ltt), u = Some s /\ v = Some (s, t))) SI x ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option sort) =>
         u = None /\ v = None \/
         (exists (s : sort) (g' : gtt), u = Some (s, g') /\ v = Some s)) lsg SI.
Proof.
  induction lsg; intros; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
    inversion H0. subst. clear H0. inversion H. subst. clear H.
    constructor.
    - destruct H4. left. destruct H. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
      destruct H. destruct H0. easy.
    - destruct H. destruct H. destruct H. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst. right.
      exists x2. exists x4. split; try easy.
  - apply IHlsg with (x := x) (p := p); try easy.
Qed.

Lemma _a_29_helper3 : forall n lsg x0 Sk ys q,
    onth n lsg = Some(Sk, x0) -> 
    Forall2
          (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
           u0 = None /\ v = None \/
           (exists (s : sort) (t : ltt) (g' : gtt),
              u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys ->
    exists Tq, onth n ys = Some(Sk, Tq) /\ projectionC x0 q Tq.
Proof.
  induction n; intros; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst. destruct H4; try easy. 
    destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H. subst.
    exists x1. split; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst.
    apply IHn with (lsg := lsg); try easy.
Qed.

Lemma _a_29_helper4 : forall n xs ys S' Sk T' x1,
    onth n xs = Some (S', T') ->
    onth n ys = Some (Sk, x1) ->
    Forall2R
        (fun u v : option (sort * ltt) =>
         u = None \/
         (exists (s s' : sort) (t t' : ltt),
            u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys xs -> 
    subtypeC T' x1.
Proof.
  induction n; intros.
  - destruct xs; try easy. destruct ys; try easy.
    inversion H1. subst. simpl in *. subst.
    destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2.
    inversion H0. inversion H. subst. easy.
  - destruct xs; try easy. destruct ys; try easy.
    inversion H1. subst. specialize(IHn xs ys S' Sk). apply IHn; try easy.
Qed.

Lemma _a_29 : forall G p q PT QT S T S' T' xs n, 
    wfgC G -> 
    projectionC G p PT -> 
    subtypeC (ltt_send q (extendLis n (Some (S, T)))) PT ->
    projectionC G q QT -> 
    onth n xs = Some (S', T') ->
    subtypeC (ltt_recv p xs) QT -> 
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ (* 1 *)
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ (* 2 *)
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ subtypeC T Tp /\ projectionC Gjk q Tq /\ subtypeC T' Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ (* 3 5 6 *)
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. (* 5 6 *)
Proof.
  intros.
  specialize(_a_29_10 G p q PT S T n H0 H1); intros.
  destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7.
  rename x0 into Sk. rename x1 into Tk.
  assert (PT = (ltt_send q x)).
  {
(*    specialize(proj_inj H0 H5); intros. *)
    admit.
  } 
  subst. clear H5. (* _a_29_10 *)
  
  specialize(_a_29_11 G p q x H H0); intros.
  destruct H5. destruct H5. destruct H5. destruct H9.
  
  rename x1 into ctxG. rename x0 into G'.
  exists G'. exists ctxG.
  assert (exists (SI : seq.seq (option sort)),
    List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t, u = Some s /\ v = Some (s, t))) SI x).
  {
    clear H H1 H0 H2 H3 H4 H8 H5 H6 H7 H9 H10. 
    clear G p q QT S' T' T xs G' ctxG S n Sk Tk.
    induction x; intros; try easy.
    - exists []. easy.
    - destruct IHx; try easy. destruct a.
      - destruct p. exists (Some s :: x0). constructor; try easy.
        right. exists s. exists l. easy.
      - exists (None :: x0). constructor; try easy.
        left. easy.
  }
  destruct H11 as [SI H11]. exists SI.
  exists Sk. split. easy.
  split. easy.
  assert (onth n SI = Some Sk /\ subsort S Sk).
  {
    clear H1 H0 H10 H3.
    revert H11 H6 H7. revert n x SI. induction n; intros; try easy.
    - destruct SI; try easy. destruct x; try easy.
      destruct x; try easy. inversion H11. subst.
      simpl in H6. subst.
      destruct H10; try easy. destruct H0. destruct H0. destruct H0. inversion H1. subst. easy.
    - destruct SI; try easy. destruct x; try easy.
      destruct x; try easy.
      inversion H11. subst. simpl.
      apply IHn with (x := x); try easy. 
  }
  specialize(_a_29_1314 G G' p q QT xs ctxG x H10 H5 H9 H2 H4); intros; try easy.
  destruct H13. destruct H13. rename x0 into ys.
  
  assert (ltt_recv p ys = QT).
  {
    admit.
(*     specialize(proj_inj H13 H2); intros. *)
  } 
 
  subst. clear H13.
  clear H7.
  
  specialize(_a_29_part ctxG G' G p q x ys H5 H0 H2 H9); intros.
  split. easy.
  assert (subsort Sk S').
  {
    clear H7 H12 H10 H9 H5 H8 H2 H0 H1 H.
    specialize(subtype_recv_inv p xs ys H4); intros. clear H4.
    revert H11 H14 H H3 H6. clear G p q S T G' ctxG.
    revert S' T' xs x ys Sk Tk SI.
    induction n; intros; try easy.
    - destruct xs; try easy.
      destruct x; try easy. 
      destruct SI; try easy. destruct ys; try easy.
      simpl in *.
      subst.
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
      inversion H. subst. clear H.
      destruct H4; try easy. destruct H. destruct H. destruct H. inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. inversion H1. subst.
      destruct H6; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H2. destruct H3. 
      inversion H. inversion H2. subst. easy.
    - destruct xs; try easy.
      destruct x; try easy.
      destruct SI; try easy. destruct ys; try easy.
      simpl in *. 
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
      inversion H. subst. clear H.
      specialize(IHn S' T' xs x ys Sk Tk SI). apply IHn; try easy.
  }
  split; try easy.
  
  specialize(subtype_recv_inv p xs ys H4); intros.
  specialize(subtype_send_inv q (extendLis n (Some (S, T))) x H1); intros.
  
  specialize(_a_29_16 G' ctxG G p q ys x H2 H10 H9 H7 H5); intros.
  
  specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x /\
            Forall2
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys)) ctxG); intros.
  destruct H18. specialize(H18 H17). clear H17 H19 H10.
  
  apply Forall_forall; intros.
  specialize(H18 x0 H10). destruct H18. left. easy.
  destruct H17. destruct H17. destruct H17. destruct H18. destruct H19.
  right. exists (gtt_send p q x2). exists x2. subst.
  split. easy. split. easy. 
  rename x2 into lsg.
  specialize(_a_29_helper n x Sk Tk lsg p H6 H19); intros. 
  destruct H17. destruct H17.
  specialize(_a_29_helper2 lsg SI x p H19 H11); intros. 
  split; try easy. clear H21 H19.
  exists Sk. exists x0. exists Tk.
  specialize(_a_29_helper3 n lsg x0 Sk ys q H17 H20); intros.
  destruct H19. destruct H19. exists x1. split. easy.
  split. easy. split. easy. split. easy.
  specialize(_a_29_helper4 n xs ys S' Sk T' x1); intros. apply H22; try easy.
Admitted.


Lemma _a_29_s : forall G p q PT QT S T S' T' n, 
    wfgC G -> 
    projectionC G p (ltt_send q PT) -> 
    onth n PT = Some(S, T) ->
    projectionC G q (ltt_recv p QT) -> 
    onth n QT = Some (S', T') ->
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ (* 1 *)
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ (* 2 *)
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ (* 3 5 6 *)
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. (* 5 6 *)
Proof.
Admitted.


Lemma wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> wfgC G'.
Proof.
Admitted.







