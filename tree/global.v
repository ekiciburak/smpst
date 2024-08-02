From mathcomp Require Import all_ssreflect.
From SST Require Import aux.coseq aux.expressions type.global tree.local.
From Paco Require Import paco.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

(* global session trees *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (option(sort*gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.

CoFixpoint gparts (t: gtt): coseq part :=
  match t with
    | gtt_send p q [(Datatypes.Some(s,g'))] => Delay (cocons p (Delay (cocons q (gparts g'))))
    | _                                     => Delay conil
  end.

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

Fixpoint gLparts (p: part) (l: list (option(sort*gtt))): Prop :=
  match l with
    | Datatypes.Some(s,g) :: xs => coseqIn p (gparts g) \/ gLparts p xs
    | Datatypes.None :: xs      => gLparts p xs
    | nil                       => False
  end.

Inductive wfg (R: gtt -> Prop): gtt -> Prop :=
  | wfg_end : wfg R gtt_end
  | wfg_send: forall p q lis,
              SList lis ->
              Forall (fun u => u = Datatypes.None \/ (exists s g, u = Datatypes.Some (s,g) /\ R g)) lis ->
              wfg R (gtt_send p q lis).

Definition wfgC (g: gtt) := paco1 wfg bot1 g.

(*
Inductive gt2gtt (R: global -> gtt -> Prop): global -> gtt -> Prop :=
  | gt2gtt_end: gt2gtt R g_end gtt_end
  | gt2gtt_snd: forall p q l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                gt2gtt R (g_send p q (zip (zip l s) xs)) (gtt_send p q (ozip s ys))
  | gt2gtt_mu : forall g t,
                gt2gtt R (subst_global ((g_rec g) .: g_var) g) t ->
                gt2gtt R (g_rec g) t.

Definition gt2lttC g t := paco2 gt2gtt bot2 g t. *)

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

Fixpoint wfStep (r: part) (s: part) (R: gtt -> gtt -> part -> part -> Prop) (l1: list (option(sort*gtt))) (l2: list (option(sort*gtt))): Prop :=
  match (l1,l2) with
    | ((Datatypes.Some(s1,g)::xs), (Datatypes.Some(s2,t)::ys)) => s1 = s2 /\ R g t r s /\ wfStep r s R xs ys
    | (Datatypes.None::xs, Datatypes.None::ys)                 => wfStep r s R xs ys
    | (nil, nil)                                               => True
    | _                                                        => False
  end.

Fixpoint ounzip2 (l: list (option(sort*gtt))): list gtt :=
  match l with
    | []                      => []
    | Datatypes.None::xs      => ounzip2 xs
    | Datatypes.Some(s,g)::xs => g :: ounzip2 xs
  end.

Inductive gttstep (R: gtt -> gtt -> part -> part -> Prop): gtt -> gtt -> part -> part -> Prop :=
  | steq : forall p q l xs s gc,
                  p <> q ->
                  Datatypes.Some (s, gc) = findpathGI xs l ->
                  gttstep R (gtt_send p q xs) gc p q
  | stneq: forall p q r s xs ys,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  List.Forall (fun u => coseqIn p (gparts u)) (ounzip2 xs) ->
                  List.Forall (fun u => coseqIn q (gparts u)) (ounzip2 xs)  ->
                  wfStep r s R xs ys ->
                  gttstep R (gtt_send r s xs) (gtt_send r s ys) p q.

Definition gttstepC g1 g2 p q := paco4 gttstep bot4 g1 g2 p q.

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

(* Lemma asd: forall {A: Type} (l: list (option A)) (a: A),
(*   l <> nil -> *)
  allSame (Datatypes.Some a :: l) -> List.In (Datatypes.Some a) l.
Proof. intros A l.
       induction l; intros.
       - simpl in H. easy.
       - simpl in H. destruct l. simpl.
         left. easy.
         simpl.
         left. easy.
Qed.
 *)
(*
Lemma asd: forall {A: Type} (s: A), @allSame A [Datatypes.Some s; Datatypes.None; Datatypes.None; Datatypes.None ; Datatypes.None; Datatypes.Some s].
Proof. intros. simpl. *)

(* Lemma allsameI: forall (l: list (option(sort*ltt))) s t,
(*   SList l -> *)
  allSameH (s, t) l -> In (Datatypes.Some (s, t)) l.
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - simpl. simpl in H.
         destruct a, l. subst. 
         left. easy.
         destruct H. subst. left. easy. 
         simpl in H. easy.
         right. apply IHl. easy.
         easy.
Qed. *)

(* Lemma allsameI: forall (l: list (option(sort*ltt))) s t, 
  SList l ->
  allSameH (s, t) l -> allSame l.
Proof. intro l.
       induction l; intros.
       - simpl in *. easy.
       - simpl. destruct l, a. easy.
         simpl in *. easy.
         simpl. 
         simpl in H0. destruct l, o. simpl.
         destruct H0. destruct H1. subst. easy.
         easy.
         split. destruct H0. destruct H1.
         inversion H1. inversion H0. easy.
         destruct H0. subst. easy.
         destruct H0. subst. easy.
         apply IHl with (s := s) (t := t). easy.
         simpl in H0. destruct o. simpl. easy.
         simpl. easy. 
Qed. *)

Fixpoint wfProj (r: part) (R: gtt -> part -> ltt -> Prop) (l1: list (option(sort*gtt))) (l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | ((Datatypes.Some(s1,g)::xs), (Datatypes.Some(s2,t)::ys)) => s1 = s2 /\ R g r t /\ wfProj r R xs ys
    | (Datatypes.None::xs, Datatypes.None::ys)                 => wfProj r R xs ys
    | (nil, nil)                                               => True
    | _                                                        => False
  end.



Check injective2.

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

Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, (coseqIn r (gparts g) -> False) -> projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
               wfProj r R xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
               wfProj r R xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
               allSame ys ->
               wfProj r R xs ys ->
               List.In (Datatypes.Some t) ys ->
               projection R (gtt_send p q xs) r (snd t).

Definition projectionC g r t := paco3 projection bot3 g r t.

(*
Lemma fmerge: forall g p (t: ltt) (s: sort),
 (coseqIn p (gparts g) -> False) ->
 upaco3 projection bot3 g p t -> 
 t = ltt_end.
Proof. intros.
       unfold upaco3 in H0.
       destruct H0.
       pinversion H0.
       subst. easy.
       subst. contradict H. admit.
       subst. contradict H. admit.
       subst. destruct t0.
       simpl.
 *)

Fixpoint wfListH (l: list (option(sort*gtt))): Prop :=
  match l with
    | [] => True
    | x::xs => 
      match x with
        | Datatypes.None => wfListH xs
        | Datatypes.Some(s,g) => wfgC g /\ wfListH xs
      end
  end.

Definition wfList (l: list (option(sort*gtt))): Prop :=
 l <> nil /\ wfListH l.

(* this lemma *)
Lemma contra: forall g t p,
  (coseqIn p (gparts g) -> False) ->
  upaco3 projection bot3 g p t -> 
  t = ltt_end.
Proof. intros.
       unfold upaco3 in H0.
       destruct H0; [ | easy].
       pinversion H0.
       subst.
       easy.
       subst.
       contradict H. admit.
       subst.
       contradict H. admit.
       destruct t0. simpl in H9. simpl.
       subst.
Admitted.
       
(* Lemma mListe: forall xs ys s t p,
  SList xs ->
  wfList xs ->
  allSame ys ->
  (gLparts p xs -> False) ->
  wfProj p (upaco3 projection bot3) xs ys ->
  In (Datatypes.Some (s, t)) ys ->
  t = ltt_end.
Proof. intro xs.
       induction xs; intros.
       - case_eq ys; intros.
         + subst. simpl in H1. easy.
         + subst. simpl in H0. easy.
       - case_eq ys; intros.
         + subst. simpl in H2. easy.
         + subst. simpl in H2.
           destruct a, o. destruct p0, p1.
           simpl in H.
           simpl in H0.
           case_eq xs; intros.
           ++ subst. simpl in H2.
              simpl in H3.
              case_eq l; intros.
              * subst.
                simpl in H4. destruct H4.
                inversion H4. subst.
                case_eq l0; intros.
                ** subst. simpl in H4.
                   destruct H4.
                   inversion H4. subst. easy. easy.
                   subst.
                   simpl in H4.
                   destruct H4.
                   inversion H4. subst.
                   destruct H3 as (H3a,(H3b, H3c)).
                   unfold upaco3 in H3b.
                   destruct H3b as [H3b | H3b].
                   pinversion H3b. subst.
                   contradict H2. left. admit.
                   subst. destruct t. simpl in H3. simpl.
                   
                   inversion H3b. subst.
                   contradict H2. left. admit.
                   subst. destruct t. simpl in H14. simpl.
                   inversion H3b. subst.
                   contradict H2. left. admit.
                   subst.
(*            destruct H2. *)
(*            simpl in H. *)
           
           apply IHxs with (ys := l) (s := s) (p := p).
           unfold wfList in H0.
           
           simpl in H0.
           easy.
           intros Hn. apply H0. now right.
           easy.
           simpl in H. destruct l. simpl.  easy.
           simpl in H. destruct l. simpl. easy.
           simpl in H. simpl.
           destruct H. destruct H2. subst. easy.
           easy.
           simpl in H. admit.
           
           apply IHxs with (ys := l) (s := s) (p := p).
           destruct l. easy. simpl in H. simpl.
           destruct H. subst. easy.
           easy. easy. 
           
           destruct p0. easy.
           easy. simpl in H. 
           
           apply IHxs with (ys := l) (s := s) (p := p).
           destruct l. easy. simpl in H. simpl.
           destruct H. subst. easy.
           easy. simpl in H1.
           destruct H1. easy. easy.
Admitted. *)
           


Lemma wpsBot: forall l1 l2 l3 p, 
  wfProj p bot3 l1 l2 ->
  wfProj p bot3 l1 l3 -> l2 = l3.
Proof. intros. 
       apply wps with (l1 := l1) (p := p) (R := bot3); try easy.
Qed.


Axiom injup: injection3 (upaco3 projection bot3).


 Lemma projI_same: forall g l1 l2 p,
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
           specialize(injup g p l3 l2 Hb H0b); easy.

           apply IHl1 with (p := p).
           easy. easy.
           easy. easy. easy.
           destruct o, o0. easy. easy. easy.
           f_equal. 
           apply IHl1 with (p := p). easy. easy.
Qed.

Lemma _319_1: forall p q S T G G' L1 L2,
  wfC L1 ->
  wfC L2 ->
  wfC T ->
  wfgC G ->
  wfgC G' ->
  projectionC G p L1 ->
  subtypeC (ltt_send q [Datatypes.Some(S,T)]) L1 ->
  gttstepC G G' p q ->
  projectionC G' p L2 ->
  subtypeC T L2.
Proof. intros p q S T G G' L1 L2 Hwk1 Hwl2 Hwt Hwg Hwg' Hpg Hsl1 Hsg Hpg'.
       pinversion Hsl1. subst.
       pinversion Hpg. subst.
       pinversion Hsg. subst.
       case_eq xs; intros; subst.
       - pinversion Hwg.
         subst. simpl in H1. easy.
         admit.
       - case_eq ys; intros; subst.
         simpl in H5. destruct o. destruct p0. easy.
         simpl in H2. easy.
       simpl in H2.
       destruct o0. destruct p0.
       destruct o.
       simpl in H5. destruct p0.
       case_eq l; intros.
       - subst. simpl in H9. inversion H9. subst. clear H9.
         pinversion Hpg'. subst.
         case_eq T; intros.
         subst. pfold. constructor.
         subst. 
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst.
         contradict H.
         case_eq xs; intros; subst.
         pinversion Hwg'. simpl in H1. easy.
         admit. admit.

         subst.
         admit. (*merge case*)
         admit.
         easy.
         admit.
         easy.
         
         subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst.
         contradict H. admit.
         
         subst.
         admit. (*merge case*)
         admit.
         easy.
         admit.
         easy.

         case_eq T; intros. subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst.
         contradict H. admit.
         
         subst.
         admit. (*merge case*)
         admit.
         easy.
         admit.
         easy.
         
         subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst.
         pfold. constructor.
         admit. (* issue solved here *)
         
         subst. easy.
         admit.
         easy.
         admit.
         easy.
         
         subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst.
         easy.
         subst. easy.
         admit.
         subst. easy.
         admit. easy.
         
         subst.
         case_eq T; intros. subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst.
         contradict H1. admit.
         
         subst. easy.
         admit.
         easy.
         admit.
         easy.
         
         subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst. easy.

         subst. easy.
         admit.
         easy.
         admit.
         easy.
         
         subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst. 
         pfold. constructor.
         admit. (* issue solved here *)
         
         subst.
         easy.
         admit.
         easy. 
         admit. 
         easy.
         
         
         subst.
         destruct H5 as (H5a,(H5b,H5c)).
         destruct H5b as [H5b | H5b].
         pinversion H5b. subst. 
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         pinversion Hwg'.
         unfold SList in H12.
         admit. (*helper*)
         admit.
         admit.
         easy.
         subst.
         destruct H2 as (H2a,(H2b,H2c)).
         destruct H2b as [H2b | H2b].
         pinversion H2b. subst.
         easy. admit.
         easy. subst. easy. subst.
         admit.
         admit.
         easy.
         admit.
         subst.
         subst.
         
         admit.
         
         subst. 
         simpl in H5. easy.
         easy. subst. easy.
         admit. subst.
         
         pinversion Hsg.
         subst. easy. subst.
         pinversion Hpg'. subst.
(*          rewrite Forall_forall in H15.
         rewrite Forall_forall in H19. *)
Admitted.


(*
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

Inductive merge_branch: ltt -> ltt -> ltt -> Prop :=
  | mbc: forall p l1 l2 l3, merge l1 l2 l3 ->
                            merge_branch (ltt_recv p l1) (ltt_recv p l2) (ltt_recv p l3)
  | mbe: forall L1 L2, L1 = L2 -> merge_branch L1 L2 L1.

Inductive mergeList {A: Type}: list ltt -> ltt -> Prop :=
  | ml1  : forall t, mergeList [t] t
  | mlce : forall x y xs t, merge_branch x y t -> xs = [] -> mergeList (x::y::xs) t
  | mlcne: forall x y xs t T T2, merge_branch x y t -> mergeList xs T -> merge_branch t T T2 -> mergeList (x::y::xs) T2.
*)

(*
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
