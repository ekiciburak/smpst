From mathcomp Require Import all_ssreflect.
From SST Require Import aux.coseq aux.expressions type.global tree.local.
From Paco Require Import paco pacotac.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

(* coinduction by Pous *)
(* From Coinduction Require Import all. Import CoindNotations.
Set Implicit Arguments. *)

(* global session trees *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (label*(sort*gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.

CoFixpoint gparts (t: gtt): coseq part :=
  match t with
<<<<<<< HEAD
    | gtt_send p q [Datatypes.Some(s,g')] => Delay (cocons p (Delay (cocons q (gparts g'))))
=======
    | gtt_send p q [(l,(s,g'))] => Delay (cocons p (Delay (cocons q (gparts g'))))
>>>>>>> refs/remotes/origin/apiros3_branch
    | _                         => Delay conil
  end.

Fixpoint ounzip2 (l: list (option(sort*gtt))): list gtt :=
  match l with
    | []                      => []
    | Datatypes.None::xs      => ounzip2 xs
    | Datatypes.Some(s,g)::xs => g :: ounzip2 xs
  end.

(* Inductive Forall (A : Type) (P : A -> Prop) : seq.seq A -> Prop :=
  | Forall_nil : Forall P []
  | Forall_cons : forall (x : A) (l : seq.seq A), P x -> Forall P l -> Forall P (x :: l). *)

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
                admit.
                simpl. left. easy.
                pinversion Ha.
                subst. constructor. subst. constructor.
                subst.
                apply pa_send3 with (u := u). easy. easy.
                easy. simpl. right. easy.
                admit.
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
                admit. simpl. left. easy. easy.
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
              easy. simpl. easy. admit.
              easy.
Admitted.

(* CoFixpoint isgParts (a: part) (t: gtt): Prop :=
 match t with
    | gtt_send p q l => 
      let fix next l :=
        match l with
          | x::xs =>
            match x with
              | Datatypes.Some(s,g') => isgParts a g'
              | Datatypes.None       => next xs
            end
          | nil  => False
        end
      in a = p \/ a = q \/ next l
    | _              => False
  end. *)
  
(*
Local Open Scope list_scope.
CoFixpoint gparts (t: gtt): list (coseq part) :=
  match t with
    | gtt_send p q l => 
      let fix next l :=
        match l with
          | x::xs =>
            match x with
              | Datatypes.Some(s,g') => [(Delay (cocons p (Delay conil)))] ++ [(Delay (cocons q (Delay conil)))] ++ (gparts g') ++ next xs
              | Datatypes.None       => next xs
            end
          | nil  => nil
        end
      in next l
    | _                                     => [Delay conil]
  end.
 *)
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

Inductive gt2gtt (R: global -> gtt -> Prop): global -> gtt -> Prop :=
  | gt2gtt_end: gt2gtt R g_end gtt_end
  | gt2gtt_snd: forall p q l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                gt2gtt R (g_send p q (zip (zip l s) xs)) (gtt_send p q (zip l (zip s ys)))
  | gt2gtt_mu : forall g t,
                gt2gtt R (subst_global ((g_rec g) .: g_var) g) t ->
                gt2gtt R (g_rec g) t.

Definition gt2lttC g t := paco2 gt2gtt bot2 g t.

Fixpoint findpath (l: list (label*(sort*gtt))) (lbl: label): option (sort*gtt) :=
  match l with
    | []             => Datatypes.None
    | (l1,(s,g))::xs => if Nat.eqb l1 lbl then Datatypes.Some (s, g) else findpath xs lbl
  end.

Fixpoint findpathL (l: list (label*(sort*ltt))) (lbl: label): option (sort*ltt) :=
  match l with
    | []             => Datatypes.None
    | (l1,(s,g))::xs => if Nat.eqb l1 lbl then Datatypes.Some (s, g) else findpathL xs lbl
  end.

<<<<<<< HEAD
Fixpoint findpathGI (l: list (option(sort*gtt))) (lbl: nat): option (sort*gtt) :=
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
  end.

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

Variant gttstep (R: gtt -> gtt -> part -> part -> nat -> Prop): gtt -> gtt -> part -> part -> nat -> Prop :=
  | steq : forall p q xs s gc n,
                  p <> q ->
                  NoDup (dNone xs) ->
                  Datatypes.Some (s, gc) = findpathGI xs n ->
                  gttstep R (gtt_send p q xs) gc p q n
  | stneq: forall p q r s xs ys n,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  List.Forall (fun u => isgPartsC p u) (ounzip2 xs) ->
                  List.Forall (fun u => isgPartsC q u) (ounzip2 xs) ->
                  wfStep p q R xs ys n ->
                  gttstep R (gtt_send r s xs) (gtt_send r s ys) p q n.
=======
Inductive gttstep (R: gtt -> gtt -> part -> part -> Prop): gtt -> gtt -> part -> part -> Prop :=
  | steq : forall p q l xs s gc,
(*                eqb p q = false -> *)
                  Datatypes.Some (s, gc) = findpath xs l -> gttstep R (gtt_send p q xs) gc p q
  | stneq: forall p q r s L S xs ys,
(*                eqb p q = false ->
                  eqb r s = false -> *)
                  eqb r p = false ->
                  eqb r q = false ->
                  eqb s p = false ->
                  eqb s q = false ->
                  List.Forall (fun u => coseqIn p (gparts u)) xs ->
                  List.Forall (fun u => coseqIn q (gparts u)) xs ->
                  List.Forall (fun u => R (fst u) (snd u) p q) (zip xs ys) ->
                  gttstep R (gtt_send r s (zip L (zip S xs))) (gtt_send p q (zip L (zip S ys))) p q.
>>>>>>> refs/remotes/origin/apiros3_branch

Definition gttstepC g1 g2 p q n := paco5 gttstep bot5 g1 g2 p q n.

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

<<<<<<< HEAD
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
  match l with
    | nil   => True
    | x::xs => let ll := dropN l in allSameH x xs 
  end.

Definition asame {A: Type} (l: list (option A)): Prop := 
  (exists a, (In a l) /\ (forall b, a <> b -> (In b l -> False))) \/ l = nil.

Fixpoint wfProj (r: part) (R: gtt -> part -> ltt -> Prop) (l1: list (option(sort*gtt))) (l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | ((Datatypes.Some(s1,g)::xs), (Datatypes.Some(s2,t)::ys)) => s1 = s2 /\ R g r t /\ wfProj r R xs ys
    | (Datatypes.None::xs, Datatypes.None::ys)                 => wfProj r R xs ys
    | (nil, nil)                                               => True
    | _                                                        => False
  end.

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

Fixpoint wfListH (l: list (option(sort*gtt))): Prop :=
  match l with
    | [] => True
    | x::xs => 
      match x with
        | Datatypes.None      => wfListH xs
        | Datatypes.Some(s,g) => wfgC g /\ wfListH xs
      end
  end.

Definition wfList (l: list (option(sort*gtt))): Prop :=
 l <> nil /\ wfListH l.

Fixpoint wfListHL (l: list (option(sort*ltt))): Prop :=
  match l with
    | [] => True
    | x::xs => 
      match x with
        | Datatypes.None      => wfListHL xs
        | Datatypes.Some(s,g) => wfC g /\ wfListHL xs
      end
  end.

Definition wfListL (l: list (option(sort*ltt))): Prop :=
  l <> nil /\ wfListHL l.

Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, (isgPartsC r g -> False) -> projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
(*                wfList xs ->
               wfListL ys -> *)
               wfProj r R xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
(*                wfList xs ->
               wfListL ys -> *)
               wfProj r R xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
(*                wfList xs ->
               wfListL ys -> *)
               allSame ys ->
               wfProj r R xs ys ->
               List.In (Datatypes.Some t) ys ->
               projection R (gtt_send p q xs) r (snd t).

Definition projectionC g r t := paco3 projection bot3 g r t.

Lemma monoRProj: forall xs ys R1 R2 r,
  (forall (a : gtt) (a0 : string) (a1 : ltt), R1 a a0 a1 -> R2 a a0 a1) ->
  wfProj r R1 xs ys ->
  wfProj r R2 xs ys.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + subst. easy.
         + subst. simpl in H0. easy.
       - case_eq ys; intros.
         + subst. simpl in H0. easy.
         + subst. simpl. simpl in H0.
           destruct a, o. destruct p, p0.
           split. easy. split. apply H. easy.
           apply IHxs with (R1 := R1); easy. easy. easy.
           apply IHxs with (R1 := R1); easy.
Qed.

(* Definition bproj: mon (gtt -> part -> ltt -> Prop).
Proof. unshelve econstructor.
       - intros R g p t.
         exact (projection R g p t).
       - cbv. intros R1 R2 leqR g p t HR1.
         induction HR1. 
         + constructor. easy.
         + constructor.
           easy. apply monoRProj with (R1 := R1); easy.
           constructor.
           easy. apply monoRProj with (R1 := R1); easy.
           apply proj_cont with (ys := ys); try easy.
           apply monoRProj with (R1 := R1); easy.
Defined.

Notation "g ↓ p t" := (gfp bproj g p t) (at level 70).
Notation "g ↓[ R ] p t" := (`R g p t) (at level 79).
(*Notation "x ↓ y" := (`_ g p t) (at level 79). *)
Notation "g [↓] p t" := (bproj `_ g p t) (at level 79).

Lemma wpsBot: forall l1 l2 l3 p, 
  wfProj p bot3 l1 l2 ->
  wfProj p bot3 l1 l3 -> l2 = l3.
Proof. intros. 
       apply wps with (l1 := l1) (p := p) (R := bot3); try easy.
Qed. *)

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
       - simpl. simpl in H.
         destruct H. subst. easy.
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
             
              subst. destruct t. simpl. simpl in H11.
              subst.               
              specialize(injup); intro Ha.
              unfold injection3 in Ha.
              specialize(Ha (gtt_send p q xs0) r l ltt_end).
              apply Ha.
              pfold. easy. pfold. easy.
              admit. admit.
           easy.
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
Admitted.

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

Lemma InSame: forall {A: Type} (ys: list (option A)) a b,
  allSame ys ->
  In a ys ->
  In b ys -> a = b.
Proof. intros A ys.
       induction ys; intros.
       - easy.
       - simpl in H0. simpl in H1.
         destruct H0 as [H0 | H0].
         + subst. destruct H1 as [H1 | H1]. easy.
         + simpl in H.
           apply IHys.
           case_eq ys; intros.
           subst. easy. subst. simpl in H. simpl. destruct H. subst. easy.
           case_eq ys; intros.
           subst. easy. subst. simpl in H. simpl. left. easy.
           easy.
           destruct H1 as [H1 | H1]. subst.
           case_eq ys; intros. subst. easy.
           subst. simpl in H. simpl in H0.
           destruct H.
           destruct H0 as [H0 | H0].
           subst. easy.
           subst. apply IHys. simpl. easy. simpl. right. easy. simpl. left. easy.
           apply IHys. simpl in H. case_eq ys; intros. easy. subst. simpl. simpl in H.
           destruct H. subst. easy. easy. easy.
Qed.

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
                specialize(InSame ys0 (Datatypes.Some (s0, l)) (Datatypes.Some (s, l2)) H18 H12 H22); intro Ha.
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
Admitted.
           
(*
Lemma proj_inj: forall xs p q t1 t2 r,
 projection (gfp bproj) (gtt_send p q xs) r t1 ->
 projection (gfp bproj) (gtt_send p q xs) r t2 ->
 t1 = t2.
Proof. intros.
       inversion H. subst.
       inversion H0. subst. 
       easy.
       subst. contradiction H1. admit.
       subst. contradiction H1. admit.
       subst. destruct t. simpl in *.
       case_eq xs; case_eq ys; intros.
       - subst. simpl in H12. easy.
       - subst. easy.
       - subst. easy.
       - subst. simpl in H11.
         simpl in H12.
         destruct H12.
         rewrite H2 in H11. destruct o0. destruct p0.
         simpl in H8. subst.
         case_eq l0; intros.
         + subst. case_eq l1; intros.
           ++ subst. inversion H0. easy.
              subst. contradiction H1. admit.
              subst. contradiction H1. admit.
              subst.
              
Admitted. *)
                 

(*  Lemma projI_same: forall g l1 l2 p,
 wfgC g -> 
 wfC l1 ->
 wfC l2 -> 
 projectionC g p l1 ->
 projectionC g p l2 -> l1 = l2.
Proof. intros.
       case_eq g; intros.
       - subst.
         pinversion H2. subst.
         pinversion H3. subst.
         easy.
         admit.
         admit.
       - subst.
         pinversion H2. subst.
         pinversion H3. subst.
         easy.
         subst.
         contradiction H4. admit.
         subst.
         contradiction H4. admit.
         subst.
         admit.
         admit.
         subst.
         pinversion H3. subst.
         contradiction H4. admit.
         subst. 
         specialize(wps l ys ys0 p (upaco3 projection bot3) injup H10 H12); intro Hwps.
         subst. easy.
         subst. 
         specialize(wps l ys ys0 p (upaco3 projection bot3) injup H10 H12); intro Hwps.
         subst. easy.
         subst.
         easy.
         admit.
         subst.
         pinversion H3. subst.
         contradiction H4. admit.
         subst.
         specialize(wps l ys ys0 p (upaco3 projection bot3) injup H10 H12); intro Hwps.
         subst. easy.
         subst.
         specialize(wps l ys ys0 p (upaco3 projection bot3) injup H10 H12); intro Hwps.
         subst. easy.
         subst. easy.
         admit.
         subst. 
         pinversion H3. subst. 
         case_eq l; intros. subst. pinversion H. easy.
         admit. subst.
         admit. (*helper*)
         subst. easy.
         subst. easy.
         subst.
         specialize(wps l ys ys0 p (upaco3 projection bot3) injup H13 H19); intro Hwps.
         subst. 
         admit. (*a fact*)
         admit.
         admit.
Admitted.
 *)

(*  *)




(*
=======
>>>>>>> refs/remotes/origin/apiros3_branch
Definition dropDups {A: Type} (l1 l2: list A) := 
  (forall x, In x l1 <-> In x l2) /\ NoDup l2.

Inductive dropM {A : Type} : A -> list A -> list A -> Prop :=
  | drop0: forall a, dropM a [] []
  | drop1: forall x l1 xs, In x l1 -> ~In x xs -> (forall a, In a (x::xs) <-> In a l1) -> dropM x l1 xs.

Inductive mergeH {A B C: Type}: list (A*(B*C)) -> list (A*(B*C)) -> list (A*(B*C)) -> Prop :=
  | merge0: mergeH [] [] []
  | merge1: forall l1 s1 c1 xs L1 L2 L3,
            In (l1,(s1,c1)) L1 ->
            (forall s2 c2, (In (l1,(s2,c2)) L2) -> False) ->
            dropM (l1,(s1,c1)) L1 L3 ->
            mergeH L3 L2 xs ->
            mergeH L1 L2 ((l1,(s1,c1))::xs)
  | merge2: forall l2 s2 c2 xs L1 L2 L3,
            In (l2,(s2,c2)) L2 ->
            (forall s1 c1, (In (l2,(s1,c1)) L1) -> False) ->
            dropM (l2,(s2,c2)) L2 L3 ->
            mergeH L1 L3 xs ->
            mergeH L1 L2 ((l2,(s2,c2))::xs)
  | merge3: forall x xs L1 L2 L3 L4,
            In x L1 ->
            In x L2 ->
            dropM x L1 L3 ->
            dropM x L2 L4 ->
            mergeH L3 L4 xs ->
            mergeH L1 L2 (x::xs).

Definition merge {A B C: Type} (l1 l2 l3: list (A*(B*C))) :=
  mergeH l1 l2 l3 /\ dropDups (l1 ++ l2) l3.
(* 
Inductive merge_branch: ltt -> ltt -> ltt -> Prop :=
  | mbc: forall p l1 l2 l3, merge l1 l2 l3 ->
                            merge_branch (ltt_recv p l1) (ltt_recv p l2) (ltt_recv p l3)
  | mbe: forall L1 L2, L1 = L2 -> merge_branch L1 L2 L1.

Inductive mergeList {A: Type}: list ltt -> ltt -> Prop :=
  | ml1  : forall t, mergeList [t] t
  | mlce : forall x y xs t, merge_branch x y t -> xs = [] -> mergeList (x::y::xs) t
  | mlcne: forall x y xs t T T2, merge_branch x y t -> mergeList xs T -> merge_branch t T T2 -> mergeList (x::y::xs) T2.

Inductive projection (R: part -> gtt -> ltt -> Prop): part -> gtt -> ltt -> Prop :=
  | proj_end : forall g r, (coseqIn r (gparts g) -> False) -> projection R r g (ltt_end)
  | proj_in  : forall p r l s xs ys,
               List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
               projection R r (gtt_send p r (zip l (zip s xs))) (ltt_recv p (zip l (zip s ys)))
  | proj_out : forall p r l s xs ys,
               List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
               projection R r (gtt_send r p (zip l (zip s xs))) (ltt_send p (zip l (zip s ys))).
(*   | proj_cont: forall p q r l s xs ys T,
               r <> p ->
               r <> q ->
               List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
               @mergeList ltt ys T ->
               projection R r (gtt_send p q (zip (zip l s) xs)) T. *)

Definition projectionC r g t := paco3 projection bot3 r g t.

Definition t1 := [(3,(sint,ltt_end)); (5,(snat,ltt_end))].

Definition t2 := [(4,(sint,ltt_end)); (5,(snat,ltt_end))].

Definition t3 := [(3,(sint,ltt_end)); (5,(snat,ltt_end)); (4,(sint,ltt_end))].

Example _39_d: merge_branch (ltt_recv "q" t1) (ltt_recv "q" t2) (ltt_recv "q" t3).
Proof. constructor.
       unfold merge.
       split.
       unfold t1, t2, t3.
       specialize (merge1 3 sint ltt_end
                   ([(5, (snat, ltt_end)); (4,(sint, ltt_end))])
                   [(3, (sint, ltt_end)); (5,(snat, ltt_end))] [(4, (sint, ltt_end)); (5, (snat, ltt_end))]
                   [(5, (snat, ltt_end))] 
                   ); intros HS.
       apply HS;  clear HS.
       simpl. left. easy.

       intros. simpl in H.
       destruct H as [H | H]. easy.
       destruct H as [H | H]. easy. easy.

       (*dropM case*)
       constructor. simpl. left. easy.
       simpl. unfold not.  intro H. destruct H; easy.
       easy.

       specialize (merge3 (5,(snat,ltt_end)) [(4,(sint, ltt_end))]
                  [(5, (snat, ltt_end))] [(4,(sint, ltt_end)); (5, (snat, ltt_end))]
                  [] [(4, (sint, ltt_end))]
                  ); intro HS.
       apply HS; clear HS.
       simpl. left. easy.
       simpl. right. left. easy.
       constructor. simpl.
       left. easy.
       simpl. easy.
       easy.

       constructor.
       simpl. right. left. easy.
       simpl. intro H.
       destruct H; easy.
       intros (u,(v,y)).

       simpl. split. intro Hc.
       simpl in Hc. 
       destruct Hc as [Hc |Hc].
       inversion Hc. subst. right. left. easy.
       destruct Hc as [Hc |Hc].
       inversion Hc. subst. left. easy. easy.
       intro Hc.
       simpl in Hc. 
       destruct Hc as [Hc |Hc].
       inversion Hc. subst. right. left. easy.
       destruct Hc as [Hc |Hc].
       inversion Hc. subst. left. easy. easy.

       specialize (merge2 4 sint ltt_end
                   nil
                   [] [(4, (sint, ltt_end))] []
                  ); intros HS.
       apply HS;  clear HS.
       simpl. left. easy.
       intros. simpl in H. easy.

       (*dropM case*)
       constructor.
       simpl. left. easy. 
       intro H. simpl in H. easy.
       easy.
       (*merge0*)
       constructor.

       unfold dropDups.
       split.
       intros (l1,(s1,c1)).
       split.
       intro Hx.
       simpl in Hx.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       left. easy.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       right. left. easy.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       right. right. left. easy.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       right. left. easy. easy.

       intro Hx.
       simpl in Hx.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       left. easy.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       right. left. easy.
       destruct Hx as [Hx | Hx]. 
       inversion Hx. subst. unfold t3. simpl.
       right. right. left. easy. easy.

       unfold t3.
       apply NoDup_cons_iff.
       split. simpl. intro Hx.
       destruct Hx as [Hx | Hx]. easy.
       destruct Hx as [Hx | Hx]. easy. easy.
       apply NoDup_cons_iff.
       split. simpl. intro Hx.
       destruct Hx as [Hx | Hx]. easy. easy.
       apply NoDup_cons_iff.
       split. simpl. easy.
       apply NoDup_nil.
Qed.

Definition t4 := [(0,(snat,ltt_end))].

Definition t5 := [(0,(sint,ltt_end))].

Example _39_f: forall l, merge_branch (ltt_recv "q" t4) (ltt_recv "q" t5) (ltt_recv "q" l) -> False.
Proof. intro l.
       induction l; intros.
       - inversion H. subst.
         unfold merge in H1.
         destruct H1 as (Ha, Hb).
         inversion Hb. easy.
       - inversion H.
         subst.
         unfold merge in H1.
         destruct H1 as (Ha, Hb).
         inversion Ha.
         + subst.
           specialize(H3 sint ltt_end). apply H3.
           inversion H2. subst.
           unfold t5. inversion H0; subst. simpl. 
           left. easy.
         + simpl in H0. easy.
         + subst. 
           inversion H2. unfold t5 in *.
           inversion H0. subst. 
           specialize(H3 snat ltt_end). apply H3.
           unfold t4. simpl. left. easy.
           simpl in H0. easy.
         + subst.
           inversion H2.
           inversion H3.
           rewrite <- H0 in H1.
           easy.
           simpl in H1. easy.
           simpl in H0. easy.
         + subst. easy.
Qed.

Definition t6 := [(3,(snat,ltt_end))].

Definition t7 := [(3,(snat,ltt_recv "q" [(3,(snat,ltt_end))]))].

Example _39_e: forall l, merge_branch (ltt_recv "q" t6) (ltt_recv "q" t7) (ltt_recv "q" l) -> False.
Proof. intro l.
       induction l; intros.
       - inversion H.
         subst. inversion H1.
         inversion H0.
       - inversion H.
         subst.
         inversion H1.
         inversion H0.
         + subst.
           inversion H5. inversion H3.
           subst.
           specialize (H6 snat (ltt_recv "q" [(3,(snat,ltt_end))])).
           apply H6. simpl. left. easy.
           simpl in H3. easy.
         + subst.
           inversion H5. inversion H3.
           subst.
           specialize (H6 snat ltt_end).
           apply H6. simpl. left. easy.
           simpl in H3. easy.
         + subst.
           inversion H5. inversion H6.
           rewrite <- H3 in H4.
           easy.
           simpl in H4. easy.
           simpl in H3. easy.
         + subst. easy.
Qed.

Example _39_c: forall l, merge_branch (ltt_send "q" [(3,(snat,ltt_end))]) (ltt_send "q" [(4,(snat,ltt_end))]) l -> False.
Proof. intros.
       inversion H.
       subst. easy.
Qed.

Example _39_a: merge_branch (ltt_send "q" [(0,(snat,ltt_end))]) (ltt_send "q" [(0,(snat,ltt_end))]) (ltt_send "q" [(0,(snat,ltt_end))]).
Proof. constructor.
       easy.
Qed.

Example _39_b: forall l, merge_branch (ltt_send "p" [(0,(snat,ltt_end))]) (ltt_send "q" [(0,(snat,ltt_end))]) l -> False.
Proof. intros l H.
       inversion H.
       easy.
Qed.

Check findpath.

Lemma shelp: forall p q l s T L G,
  projectionC p G L ->
  subtypeC (ltt_send q [(l,(s,T))]) L -> 
  exists lk sk Tk xs, Datatypes.Some (sk,Tk) = lkp lk xs -> 
  l = lk /\ subsort s sk /\ subtypeC T Tk /\ L = (ltt_send q xs).
Proof. intros.
       punfold H0.
       inversion H0.
       subst.
       specialize(helperR [(l, (s, T))] ys l s T subsort (upaco2 subtype bot2)); intro HH.
       apply HH in H5.
       destruct H5 as (s',(t',(Ha,(Hb,Hc)))).
       exists l. exists s'. exists t'. exists ys.
       
       intros.
       split. easy. split. easy. split. unfold upaco2.
       unfold upaco2 in Hb.
       destruct Hb. easy. easy.
       rewrite H1 in Hc.
       easy.
       simpl in H3. easy.
       simpl. left. easy.
       apply st_mon.
Qed.

Lemma _37: forall {A B C: Type} (t1 t2 t3 t4 t5 t6: list (A * (B * C))), 
           mergeH t1 t2 t5 ->
           mergeH t3 t5 t6 ->
           mergeH t2 t3 t4 ->
           mergeH t1 t4 t6.
Proof. intros A B C t1.
       induction t1; intros.
       - inversion H.
         subst.
         inversion H1. subst.
         inversion H0. subst.
         easy.
         + subst. simpl in H2. easy.
         + subst. simpl in H2. easy.
         + subst. simpl in H2. easy.
         + subst. simpl in H2. easy.
         + subst. inversion H1.
           subst. simpl in H12. easy.
Admitted.
       

 *)
(* Parameter (l: list (label*sort*ltt)).
Check dropDups l l. *)

(* TODO: add merging *)

(*
Lemma _319: forall q p l S1 S2 T1 T2 T' T'' T''' G G', 
                   projectionC p G T' ->
                   projectionC q G T'' ->
                   gttstepC G G' p q ->
                   projectionC p G' T''' ->
                   subtypeC (ltt_send q [(l,S1,T1)]) T' ->
                   subtypeC (ltt_recv p [(l,S2,T2)]) T'' ->
                   subtypeC T1 T'''.
Proof. intros.
       punfold H3.
       inversion H3.
Admitted. *)