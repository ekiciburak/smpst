From mathcomp Require Import all_ssreflect.
From SST Require Import src.coseq src.expressions type.global tree.local.
From Paco Require Import paco pacotac.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.



Inductive isgParts (R: part -> gtt -> Prop): part -> gtt -> Prop :=
  | pa_send1: forall p q l, isgParts R p (gtt_send p q l)
  | pa_send2: forall p q l, isgParts R q (gtt_send p q l)
  | pa_send3: forall a p q u l, a <> p -> a <> q ->
                                isgParts R a u ->
                                List.In u (ounzip2 l) ->
                                isgParts R a (gtt_send p q l).

Definition isgPartsC a g := paco2 isgParts bot2 a g.

Fixpoint isgPartsL (a: part)  (l: list (option(sort*gtt))): Prop :=
  match l with
    | nil                       => False
    | (Datatypes.Some(s,x))::xs => isgPartsC a x \/ isgPartsL a xs
    |( Datatypes.None)::xs      => isgPartsL a xs
  end.
  
Lemma isp_mon: monotone2 isgParts.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - constructor.
       - apply pa_send3 with (u := u); easy.
Qed.

Lemma ispartch: forall xs p q r,
  (isgPartsC r (gtt_send p q xs) -> False) ->
  isgPartsL r xs -> False.
Proof. intro xs.
       induction xs; intros.
       - simpl in H0. easy.
       - simpl in H0. destruct a. destruct p0.
         apply (IHxs p q r).
         intro Ha.
         apply H. pfold.
         case_eq (eqb p r); intros.
         + rewrite eqb_eq in H1. subst.
           constructor.
         + case_eq (eqb q r); intros.
           ++ rewrite eqb_eq in H2. subst.
              constructor.
           ++ destruct H0 as [H0 | H0].
              * apply pa_send3 with (u := g).
                apply eqb_neq in H1. easy.
                apply eqb_neq in H2. easy.
                pinversion H0.
                apply isp_mon.
                simpl. left. easy.
                pinversion Ha.
                subst. constructor. subst. constructor.
                subst.
                apply pa_send3 with (u := u). easy. easy.
                easy. simpl. right. easy.
                apply isp_mon.
                destruct H0 as [H0 | H0].
                contradict H.
                pfold.
                case_eq (eqb p r); intros.
                rewrite eqb_eq in H. subst.
                constructor.
                case_eq (eqb q r); intros.
                rewrite eqb_eq in H1. subst.
                constructor.
                apply pa_send3 with (u := g).
                apply eqb_neq in H. easy.
                apply eqb_neq in H1. easy.
                unfold isgPartsC in H0.
                pinversion H0.
                apply isp_mon. simpl. left. easy. easy.
         apply (IHxs p q r).
         intro Ha.
         apply H.
         pfold.
         case_eq (eqb p r); intros.
         ++ rewrite eqb_eq in H1. subst.
            constructor.
         ++ case_eq (eqb q r); intros.
            * rewrite eqb_eq in H2. subst.
              constructor.
            * pinversion Ha. subst.
              constructor. constructor.
              subst. 
              apply pa_send3 with (u := u). easy. easy.
              easy. simpl. easy. apply isp_mon.
              easy.
Qed.

Fixpoint wfbisim (R: gtt -> gtt -> Prop) (l1: list (option(sort*gtt))) (l2: list (option(sort*gtt))): Prop :=
  match (l1, l2) with
    | ((Datatypes.Some(s1,g1)::xs), (Datatypes.Some(s2,g2)::ys)) => s1 = s2 /\ R g1 g2 /\ wfbisim R xs ys
    | (Datatypes.None::xs, Datatypes.None::ys)                   => wfbisim R xs ys
    | (nil, nil)                                                 => True
    | _                                                          => False
  end.

Inductive gttb (R: gtt -> gtt -> Prop): gtt -> gtt -> Prop :=
  | gendb : gttb R gtt_end gtt_end
  | gsendb: forall p q xs ys, wfbisim R xs ys -> gttb R (gtt_send p q xs) (gtt_send p q ys).

Definition gttbC g1 g2 := paco2 gttb bot2 g1 g2.

Fixpoint wfbisimL (R: ltt -> ltt -> Prop) (l1: list (option(sort*ltt))) (l2: list (option(sort*ltt))): Prop :=
  match (l1, l2) with
    | ((Datatypes.Some(s1,t1)::xs), (Datatypes.Some(s2,t2)::ys)) => s1 = s2 /\ R t1 t2 /\ wfbisimL R xs ys
    | (Datatypes.None::xs, Datatypes.None::ys)                   => wfbisimL R xs ys
    | (nil, nil)                                                 => True
    | _                                                          => False
  end.

Inductive lttb (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | lendb : lttb R ltt_end ltt_end
  | lsendb: forall p xs ys, wfbisimL R xs ys -> lttb R (ltt_send p xs) (ltt_send p ys)
  | lrecvb: forall p xs ys, wfbisimL R xs ys -> lttb R (ltt_recv p xs) (ltt_recv p ys).

Definition lttbC t1 t2 := paco2 lttb bot2 t1 t2.

(* inductive membership check *)
Inductive coseqIn: part -> coseq part -> Prop :=
  | CoInSplit1 x xs y ys: force xs = cocons y ys -> x = y  -> coseqIn x xs
  | CoInSplit2 x xs y ys: force xs = cocons y ys -> x <> y -> coseqIn x ys -> coseqIn x xs.

(* Inductive gt2gtt (R: global -> gtt -> Prop): global -> gtt -> Prop :=
  | gt2gtt_end: gt2gtt R g_end gtt_end
  | gt2gtt_snd: forall p q l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                gt2gtt R (g_send p q (zip (zip l s) xs)) (gtt_send p q (zip l (zip s ys)))
  | gt2gtt_mu : forall g t,
                gt2gtt R (subst_global ((g_rec g) .: g_var) g) t ->
                gt2gtt R (g_rec g) t.

Definition gt2lttC g t := paco2 gt2gtt bot2 g t. *)
(* 
Fixpoint findpath (l: list (label*(sort*gtt))) (lbl: label): option (sort*gtt) :=
  match l with
    | []             => Datatypes.None
    | (l1,(s,g))::xs => if Nat.eqb l1 lbl then Datatypes.Some (s, g) else findpath xs lbl
  end.

Fixpoint findpathL (l: list (label*(sort*ltt))) (lbl: label): option (sort*ltt) :=
  match l with
    | []             => Datatypes.None
    | (l1,(s,g))::xs => if Nat.eqb l1 lbl then Datatypes.Some (s, g) else findpathL xs lbl
  end. *)

(* Fixpoint findpathGI (l: list (option(sort*gtt))) (lbl: nat): option (sort*gtt) :=
  match lbl with
    | O => 
      match l with
        | []                      => Datatypes.None
        | Datatypes.None::xs      => Datatypes.None
        | Datatypes.Some(s,g)::xs => Datatypes.Some(s,g) 
      end
    | S k =>
      match l with
        | []                      => Datatypes.None
        | Datatypes.None::xs      => findpathGI xs k
        | Datatypes.Some(s,g)::xs => findpathGI xs k
      end
  end. *)

Fixpoint wfStep (r: part) (s: part) (R: gtt -> gtt -> part -> part -> nat -> Prop) (l1: list (option(sort*gtt))) (l2: list (option(sort*gtt))) (n: nat): Prop :=
  match (l1,l2) with
    | ((Datatypes.Some(s1,g)::xs), (Datatypes.Some(s2,t)::ys)) => s1 = s2 /\ R g t r s n /\ wfStep r s R xs ys n
    | (Datatypes.None::xs, Datatypes.None::ys)                 => wfStep r s R xs ys n
    | (nil, nil)                                               => True
    | _                                                        => False
  end. 
  

(* Definition wfStep (r: part) (s: part) (R: gtt -> gtt -> part -> part -> nat -> Prop) (l1: list (option(sort*gtt))) (l2: list (option(sort*gtt))) :=
  wfStepH r s R l1 l2 0. *)

Fixpoint dNone (l: list (option(sort*gtt))): list (sort*gtt) :=
  match l with
    | x::xs =>
      match x with
        | Datatypes.Some (s,g) => (s,g) :: dNone xs
        | Datatypes.None       => dNone xs
      end
    | nil   => nil
  end.



(* Lemma monoRStep: forall xs ys R1 R2 r s,
  (forall (a a0 : gtt) (a1 a2 : string), R1 a a0 a1 a2 -> R2 a a0 a1 a2) ->
  wfStep r s R1 xs ys ->
  wfStep r s R2 xs ys.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + subst. simpl. easy.
         + subst. simpl in H0. easy.
       - case_eq ys; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. simpl.
           destruct a. destruct p, o. destruct p.
           split. easy. split. apply H. easy. 
           apply IHxs with (R1 := R1); easy. easy.
           destruct o. easy.
           apply IHxs with (R1 := R1); easy.
Qed.

Definition bstep: mon (gtt -> gtt -> part -> part -> Prop).
Proof. unshelve econstructor.
       - intros R g1 g2 p q.
         exact (gttstep R g1 g2 p q).
       - cbv. intros R1 R2 Rmon g1 g2 p q HR1.
         induction HR1.
         + apply steq with (s := s); easy.
         + apply stneq; try easy.
           apply monoRStep with (R1 := R1); easy.
Defined.

Notation "g1 ⟶ g2 p q" := (gfp bstep g1 g2 p q) (at level 70).
Notation "g1 ⟶[ R ] g2 p q" := (`R g1 g2 p q) (at level 79).
Notation "g1 [⟶] g2 p q" := (bstep `_ g1 g2 p q) (at level 79). *)

Fixpoint allSameH {A: Type} (a: A) (l: list A): Prop :=
  match l with
    | nil   => True
    | x::xs => x = a /\ allSameH a xs
  end.

Fixpoint dropN  {A: Type}  (l: list (option A)): (list A) :=
  match l with
    | nil => nil
    | x::xs => 
      match x with
        | Datatypes.None   => dropN xs
        | Datatypes.Some u => u :: dropN xs
      end
  end.

Definition allSame {A: Type} (l: list (option A)): Prop := 
  let ll := dropN l in
  match ll with
    | nil   => True
    | x::xs => allSameH x xs 
  end.

Definition asame {A: Type} (l: list (option A)): Prop := 
  (exists a, (In a l) /\ (forall b, a <> b -> (In b l -> False))) \/ l = nil.

Fixpoint omap {A B: Type} (f: A -> B) (l: list (option A)): list B :=
  match l with
    | nil => nil
    | x::xs =>
      match x with
        | Datatypes.Some u => f u :: omap f xs
        | Datatypes.None   => omap f xs
      end
  end.

Definition injection3 (R: gtt -> part -> ltt -> Prop) := forall a b c d, R a b c -> R a b d -> c = d.


Lemma wps: forall l1 l2 l3 p R, 
  injection3 R ->
  wfProj p R l1 l2 ->
  wfProj p R l1 l3 -> l2 = l3.
Proof. intro l1.
       induction l1; intros.
       - case_eq l2; case_eq l3; intros.
         + easy.
         + subst. simpl in H0. easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - case_eq l2; case_eq l3; intros.
         + easy.
         + subst. simpl in H. destruct a. destruct p0. easy.
           easy.
         + subst.  simpl in H0. destruct a. destruct p0. easy.
           easy.
         + subst. simpl in H1, H0.
           destruct a. destruct o, o0.
           destruct p0, p1, p2.
           simpl.
           pose proof H as HH.
           specialize(H g p l2 l3).
           rewrite H; try easy.
           destruct H0 as (H0a,(H0b,H0c)).
           destruct H1 as (H1a,(H1b,H1c)).
           subst. f_equal. 
           apply IHl1 with (p := p) (R := R); easy. 
           destruct p0. easy.
           destruct p0. easy.
           destruct p0. easy.
           destruct o, o0.
           easy. easy. easy.
           f_equal.
           apply IHl1 with (p := p) (R := R); easy. 
Qed.

Lemma wfproj_mon: forall xs ys p r r',
  wfProj p r xs ys ->
  (forall (x0 : gtt) (x1 : string) (x2 : ltt), r x0 x1 x2 -> r' x0 x1 x2) ->
  wfProj p r' xs ys.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + easy.
         + subst. easy.
       - case_eq ys; intros.
         + subst. easy.
         + subst. simpl in H. simpl.
           destruct a. destruct p0, o. destruct p0.
           split. easy. split. apply H0. easy.
           apply IHxs with (r := r); easy.
           easy.
           destruct o. easy.
           apply IHxs with (r := r); easy.
Qed.



Axiom injup: injection3 (paco3 projection bot3).
(* Axiom injupP: injection3 (projection (gfp bproj)). *)

Lemma projL_same: forall l1 l2 l3 p,
 wfProj p (upaco3 projection bot3) l1 l2 ->
 wfProj p (upaco3 projection bot3) l1 l3 -> l2 = l3.
Proof. intro l1.
       induction l1; intros.
       - case_eq l2; case_eq l3; intros.
         + subst. easy.
         + subst. simpl in H0. easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - case_eq l2; case_eq l3; intros.
         + easy.
         + subst. simpl in H. destruct a. destruct p0. easy.
           easy.
         + subst. simpl in H0. destruct a. destruct p0. easy.
           easy.
         + subst.
           simpl in H. simpl in H0.
           destruct a. destruct p0, o, o0. destruct p0, p1.
           f_equal. 
           destruct H as (Ha,(Hb,Hc)).
           destruct H0 as (H0a,(H0b,H0c)). 
           f_equal. subst. f_equal.
           specialize(injup); intro HH.
           unfold injection3 in HH.
           unfold upaco3 in H0b. 
           unfold upaco3 in Hb. 
           destruct H0b as [H0b | H0b].
           destruct Hb as [Hb | Hb].
           specialize(HH g p l3 l2 Hb H0b); easy.
           easy. easy.

           apply IHl1 with (p := p).
           easy. easy.
           easy. easy. easy.
           destruct o, o0. easy. easy. easy.
           f_equal. 
           apply IHl1 with (p := p). easy. easy.
Qed.

Lemma projI_same: forall g l1 l2 p,
 projectionC g p l1 ->
 projectionC g p l2 -> l1 = l2.
Proof. intros.
       unfold projectionC in *.
       specialize(injup); intro HH.
       unfold injection3 in HH.
       specialize(HH g p l1 l2 H H0); easy.
Qed.

Lemma pmergeC: forall G r,
         (isgPartsC r G -> False) ->
         projectionC G r ltt_end.
Proof. intros.
       pfold. constructor. easy.
Qed.


Lemma asameE: forall {A: Type} (xs: list (option A)) x, allSame (x::xs) -> allSame xs.
Proof. intros A xs.
       induction xs; intros.
       - simpl. easy.
       - unfold allSame in *. simpl. simpl in H. destruct a.
         destruct x. simpl in H. destruct H. subst. easy. easy.
         apply IHxs with (x := x). simpl.
         easy.
Qed.

Lemma endH: forall xs ys r s l,
  allSame ys ->
  wfProj r (upaco3 projection bot3) xs ys ->
  In (Datatypes.Some (s, l)) ys ->
  (isgPartsL r xs -> False) -> 
  l = ltt_end.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + subst. simpl in H1. easy.
         + subst. simpl in H0. easy.
           case_eq ys; intros.
           ++ subst. simpl in H1. easy.
           ++ subst. simpl in H0.
              simpl in H1.
              destruct H1 as [H1 | H1].
              rewrite H1 in H0. destruct a.
              destruct p. 
              destruct H0 as (H0a,(H0b,H0c)).
              unfold upaco3 in H0b.
              destruct H0b as [H0b | H0b].
              pinversion H0b.
              subst. easy.
              subst. contradict H2. simpl. left.
              pfold. constructor.
              subst.  contradict H2. simpl. left.
              pfold. constructor.
              subst. destruct t.
              simpl. simpl in H0b.
              simpl in H.
              specialize(@pmergeC  (gtt_send p q xs0) r); intro HH.
              assert((isgPartsC r (gtt_send p q xs0) -> False)).
              { intro Ha.
                apply H2. simpl. left. easy. }
              specialize(HH H1).
              pinversion HH.
              subst.
              specialize(injup); intro Ha.
              unfold injection3 in Ha.
              specialize(Ha (gtt_send p q xs0) r l ltt_end).
              apply Ha.
              pfold. easy. pfold. easy.
             
              subst. destruct t. simpl. easy.
              apply proj_mon. apply proj_mon.
              subst. apply IHxs with (ys := l0) (r := r) (s := s); try easy.
              easy.
           destruct a. destruct p, o. destruct p.
           apply (IHxs l0 r s).
           apply asameE in H. easy.
           easy. easy. 
           intro Ha.
           apply H2. simpl. right. easy.
           easy.
           destruct o. easy.
           apply (IHxs l0 r s).
           apply asameE in H. easy.
           easy. easy. 
           intro Ha.
           apply H2. simpl. easy.
Qed.

Lemma projI2_same: forall g p t1 t2,
  projection (upaco3 projection bot3) g p t1 ->
  projection (upaco3 projection bot3) g p t2 ->
  t1 = t2.
Proof. intros.
       specialize(injup); intro Ha.
       unfold injection3 in Ha.
       specialize(Ha g p t1 t2).
       apply Ha. pfold. easy. pfold. easy.
Qed.


(* Lemma pmergeC: forall p q r xs,
         wfgC (gtt_send p q xs) ->
         (isgPartsC r (gtt_send p q xs) -> False) ->
         projectionC (gtt_send p q xs) r ltt_end.
Proof. intros.
       pfold. constructor. easy.
Qed. *)

Lemma InSH: forall {A: Type} l (a b: A), In (Datatypes.Some a) l -> allSameH b (dropN l) -> In (Datatypes.Some b) l.
Proof. intros A l.
       induction l; intros.
       - easy.
       - simpl. simpl in H0.
         destruct a. simpl in H0.
         simpl in H. destruct H0. subst. left. easy.
         right. simpl in H. destruct H. easy.
         apply IHl with (a := a0). easy. easy.
Qed.

Lemma InSame: forall {A: Type} (ys: list (option A)) a b,
  allSame ys ->
  In (Datatypes.Some a) ys ->
  In (Datatypes.Some b) ys -> a = b.
Proof. intros A ys.
       induction ys; intros.
       - easy.
       - simpl in H0. simpl in H1.
         destruct H0 as [H0 | H0].
         + subst. destruct H1 as [H1 | H1]. inversion H1. subst. easy.
         + unfold allSame in H. simpl in H.
           apply IHys.
           case_eq ys; intros.
           subst. easy. subst. simpl in H. destruct o. unfold allSame. simpl.
           simpl in H. destruct H. subst. easy.
           simpl in H1. destruct H1 as [H1 | H1]. easy.
           unfold allSame. simpl. destruct (dropN l). easy. simpl in H.
           destruct H. subst. easy.
           case_eq ys; intros.
           subst. easy. subst. simpl in H. simpl.
           destruct o. simpl in H. destruct H. subst. left. easy.
           simpl in H1. destruct H1 as [H1 | H1]. easy.
           clear IHys. revert a0 H.
           right.
           induction l; intros.
           subst. simpl in H1. easy.
           simpl in H1. destruct H1 as [H1 | H1].
           subst. simpl in H. destruct H. subst. left. simpl. easy.
           right. simpl.
           apply IHl. easy. simpl in H. destruct a. simpl in H. destruct H. subst. easy. easy. easy.

           destruct H1 as [H1 | H1]. subst.
           case_eq ys; intros. subst. easy.
           subst. simpl in H. simpl in H0.
           unfold allSame in H. simpl in H.
           destruct H0 as [H0 | H0].
           subst. simpl in H. destruct H. easy.
           destruct o. simpl in H. destruct H. subst.
           apply IHys. unfold allSame. simpl. easy.
           simpl. right. easy.
           simpl. left. easy.
           apply IHys. unfold allSame. simpl. 
           destruct (dropN l). easy. simpl in H. destruct H. subst. easy.
           simpl. right. easy. simpl. right.
           apply InSH with (a := a0); easy.
           apply IHys. apply asameE in H. easy. easy. easy.
Qed.

Inductive gctx: Type :=
  | ghole: gctx
  | gsend: part -> part -> list (option (sort*gctx)) -> gctx.

(* Fixpoint Nth {A: Type} (l: list A) (n: nat): option A :=
  match (l, n) with
    | (x::xs, O)   => Datatypes.Some x
    | (x::xs, S k) => Nth xs k
    | (nil, S k)   => Datatypes.None
    | (nil, O)     => Datatypes.None
  end. *)

Fixpoint ounzip3 (l: list (option(sort*gctx))): list gctx :=
  match l with
    | []                      => []
    | Datatypes.None::xs      => ounzip3 xs
    | Datatypes.Some(s,g)::xs => g :: ounzip3 xs
  end.

Inductive graft: gctx -> list gtt -> gtt -> Prop :=
  | gr_hole_sing: forall g, graft ghole [g] g
  | gr_cont_hole: forall p q s S xs ys g gs,
                  List.Forall (fun u => graft (fst u) gs (snd u)) (zip xs ys) -> 
                  graft (gsend p q (Datatypes.Some(s,ghole)::(ozip S xs))) (g::gs) (gtt_send p q (Datatypes.Some(s,g)::(ozip S ys)))
  | gr_cont_cont: forall p q s S xs ys a b S2 l nl gs1 gs2,
                  List.Forall (fun u => graft (fst u) gs1 (snd u)) (zip l nl) -> 
                  List.Forall (fun u => graft (fst u) gs2 (snd u)) (zip xs ys) -> 
                  graft (gsend p q (Datatypes.Some(s,gsend a b (ozip S2 l))::(ozip S xs))) (gs1++gs2) (gtt_send p q (Datatypes.Some(s,gtt_send a b (ozip S2 nl))::(ozip S ys))).

Fixpoint isPartgctx (p: part) (c: gctx): bool :=
  match c with
    | ghole       => false
    | gsend a b l => 
      let fix next p l :=
        match l with
          | nil   => false
          | (Datatypes.Some (s,x))::xs => isPartgctx p x || next p xs
          | (Datatypes.None)::xs       => next p xs
        end
      in eqb a p || eqb b p || next p l
  end.
(* 
Lemma _319_1: forall p q S T G G' L1 L2,
  wfC L1 ->
  wfC L2 ->
  wfC T ->
  wfgC G ->
  wfgC G' ->
  projectionC G p L1 ->
  subtypeC (ltt_send q [Datatypes.Some(S,T)]) L1 ->
  gttstepC G G' p q 0 ->
  projectionC G' p L2 ->
  subtypeC T L2.
Proof. intros p q S T G G' L1 L2 Hwk1 Hwl2 Hwt Hwg Hwg' Hpg Hsl1 Hsg Hpg'.
       pinversion Hsl1. subst. (* L1 = send *)
       - pinversion Hpg. subst. (* G = send *)
         + pinversion Hsg. subst. (* G' = gc *)
           ++ pinversion Hpg'. subst. (* L2 = end *)
              * case_eq xs; intros. subst. pinversion Hwg. easy.
                admit. subst.
                case_eq ys; intros. subst. simpl in H5. easy.
                subst. simpl in H11. simpl in H5. simpl in H2.
                destruct o. destruct o0. destruct p0, p1.
                inversion H11. subst.
                specialize(@pmergeC g p H); intro Ha.
                pinversion Ha. subst. 
                destruct H5 as (H5a,(H5b,H5c)). 
                unfold upaco3 in H5b. destruct H5b as [H5b | H5b ].
                punfold H5b.
                specialize(@projI2_same g p l1 ltt_end H5b Ha); intro Hb.
                subst. 
                destruct H2 as (H2a,(H2b,H2c)).
                unfold upaco2 in H2b.
                destruct H2b as [H2b | H2b].
                punfold H2b. pfold. easy.
                admit. easy. admit. easy.
                destruct t. simpl. simpl in H0. subst.
                destruct H5 as (H5a,(H5b,H5c)). 
                unfold upaco3 in H5b. destruct H5b as [H5b | H5b ].
                punfold H5b.
                specialize(@projI2_same (gtt_send p0 q0 xs) p l1 ltt_end H5b Ha); intro Hb.
                subst. 
                destruct H2 as (H2a,(H2b,H2c)).
                unfold upaco2 in H2b.
                destruct H2b as [H2b | H2b].
                punfold H2b. pfold. easy.
                admit. easy. admit. easy. admit. easy. easy.
              * subst. (* L2 = receive *)
                case_eq xs; intros. subst. pinversion Hwg. easy.
                admit. subst.
                case_eq ys; intros. subst. simpl in H5. easy.
                subst. simpl in H11. simpl in H5. simpl in H2.
                destruct o. destruct o0. destruct p1, p2.
                inversion H11. subst.
                destruct H5 as (H5a,(H5b,H5c)). 
                unfold upaco3 in H5b. destruct H5b as [H5b | H5b ].
                pinversion H5b. subst. 
                contradiction H1. pfold. constructor.
                subst. 
                specialize(projL_same xs0 ys ys0 p H14 H0); intro Ha.
                subst.
                destruct H2 as (H2a,(H2b,H2c)).
                unfold upaco2 in H2b.
                destruct H2b as [H2b | H2b].
                punfold H2b. pfold. easy.
                admit. easy. subst. easy.
                destruct t. simpl in H16. subst. easy. admit. easy. easy.
                destruct o0. easy. easy.
              * subst. (* L2 = send *)
                case_eq xs; intros. subst. pinversion Hwg. easy.
                admit. subst.
                case_eq ys; intros. subst. simpl in H5. easy.
                subst. simpl in H11. simpl in H5. simpl in H2.
                destruct o. destruct o0. destruct p0, p1.
                inversion H11. subst.
                destruct H5 as (H5a,(H5b,H5c)). 
                unfold upaco3 in H5b. destruct H5b as [H5b | H5b ].
                pinversion H5b. subst.
                contradiction H1. pfold. constructor.
                subst. 
                specialize(projL_same xs0 ys ys0 p H14 H0); intro Ha.
                subst. easy. 
                subst.
                specialize(projL_same xs0 ys ys0 p H14 H0); intro Ha.
                subst.
                destruct H2 as (H2a,(H2b,H2c)).
                unfold upaco2 in H2b.
                destruct H2b as [H2b | H2b].
                punfold H2b. pfold. easy.
                admit. easy. subst. easy. admit. easy. easy.
                destruct o0. easy. easy.
              * subst. (* L2 = t.2 *)
                destruct t. simpl. simpl in Hpg'.
                case_eq xs; intros. subst. pinversion Hwg. easy.
                admit. subst.
                case_eq ys; intros. subst. simpl in H5. easy.
                subst. simpl in H11. simpl in H5. simpl in H2.
                destruct o. destruct o0. destruct p1, p2.
                inversion H11. subst.
                destruct H5 as (H5a,(H5b,H5c)). 
                unfold upaco3 in H5b. destruct H5b as [H5b | H5b ].
                pinversion H5b. subst.
                specialize(@ispartch xs0 p0 q0 p H5); intro Hb.
                specialize(@endH xs0 ys0 p s0 l H6 H9 H12 Hb); intro Ha.
                subst. 
                destruct H2 as (H2a,(H2b,H2c)).
                unfold upaco2 in H2b.
                destruct H2b as [H2b | H2b].
                punfold H2b. pfold. easy.
                admit. easy. subst. easy. subst. easy.
                destruct t. simpl in H20. subst.
                specialize(projL_same xs0 ys ys0 p H21 H9); intro Ha.
                subst. 
                specialize(InSame ys0 (s0, l) (s, l2) H18 H12 H22); intro Ha.
                inversion Ha. subst.
                destruct H2 as (H2a,(H2b,H2c)).
                unfold upaco2 in H2b.
                destruct H2b as [H2b | H2b]. pfold. punfold H2b. admit.
                easy.
                admit.
                subst. easy. easy.
                destruct o0. easy. easy.
                admit.
           ++ subst. (* G' = send *)
              easy. admit.
         + destruct t. simpl in H. subst.
(*            case_eq ys; intros. subst. pinversion Hwk1. subst. easy.
           admit. subst.  *)
           pinversion Hsg. subst. easy. subst.
           pinversion Hpg'. subst.

          (*  case_eq xs; intros.
           subst. pinversion Hwg. easy. admit.
           subst. 
           case_eq ys0; intros.
           subst. simpl in H8. easy.
           subst. simpl in H8. destruct H8 as [H8 | H8].
           subst. 
           case_eq ys1; intros. 
           subst. pinversion Hwg'. easy. admit.
           subst. simpl in H5. simpl in H21.
           destruct o. destruct p1.
           destruct o0. destruct p1.
           destruct H5 as (H5a,(H5b,H5c)). subst.
           destruct H21 as (H6a,(H6b,H6c)). subst.
           unfold upaco3 in H5b.
           destruct H5b as [H5b | H5b ]. pinversion H5b.
           subst. 
           unfold upaco5 in H6b.
           destruct H6b as [H6b | H6b ].
           pinversion H6b. subst.
           assert (In (Datatypes.Some (s, g0)) xs) by admit.
           assert(isgPartsC p g0 -> False).
           { intro Ha. apply H.
             pfold. apply pa_send3 with (u := g0). easy. easy. 
             pinversion Ha. admit. simpl. left. easy. }
           simpl in H15.
           rewrite Forall_forall in H15.
           specialize(H15 g0). simpl in H15.
           case_eq xs; intros.
           subst. simpl in H24. easy.
           subst. simpl in H24. destruct o. destruct p1.
           inversion H24. subst.
           inversion H5b. subst. *)
           
           admit.
           subst. easy. subst. easy.
           subst. destruct t. simpl.
           admit(**).
           admit. admit. admit. admit.
Admitted. *)
