From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From SST Require Import type.local.
Require Import List String Datatypes ZArith Relations PeanoNat.
Local Open Scope list_scope.
Import ListNotations.
Require Import Morphisms.
Require Import Lia.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat. 
From mathcomp Require Import ssreflect.seq.
From Paco Require Import paco.

(* 
Class nlist (A: Type): Type :=
{ under: list A;
  uprop: under <> nil
}.
*)

Inductive nlist (A : Type) : Type :=
  | nnil : A -> nlist A
  | ncons: A -> nlist A -> nlist A.

Arguments nnil {_} _.
Arguments ncons {_} _.

Fixpoint nlength {A: Type} (l: nlist A): nat :=
  match l with
    | nnil x => S O
    | ncons x xs => S (nlength xs)
  end.

Fixpoint nzip {A B: Type} (l1: nlist A) (l2: nlist B): nlist (A*B) :=
  match (l1, l2) with
    | (ncons x xs, ncons y ys) => ncons (x,y) (nzip xs ys) 
    | (nnil x, nnil y)         => nnil (x,y)
    | (nnil x, ncons y ys)     => nnil (x,y)
    | (ncons x xs, nnil y)     => nnil (x,y)
  end. 

Inductive SSortedNList : list fin -> Prop :=
  | sort1 : forall a, SSortedNList [a]
  | sort2 : forall (z1 z2 : fin), forall l, le z1 z2 -> SSortedNList (z2 :: l) -> SSortedNList (z1 :: z2 :: l).

Inductive nForall {A : Type} (P : A -> Prop) : nlist A -> Prop :=
  | nForall_nil:  forall (x : A), P x -> nForall P (nnil x)
  | nForall_cons : forall (x : A) (l : nlist A), P x -> nForall P l -> nForall P (ncons x l).

Fixpoint nIn {A: Type} (a : A) (l : nlist A): Prop :=
  match l with
    | nnil a1     => a = a1
    | ncons a1 xs => a = a1 \/ nIn a xs
  end.

(* local session trees *)
(* CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: part -> list label -> list sort -> list ltt -> ltt
  | ltt_send: part -> list label -> list sort -> list ltt -> ltt. *)

CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: part -> list (label*(sort*ltt)) -> ltt
  | ltt_send: part -> list (label*(sort*ltt)) -> ltt. 

Definition ltt_id (s: ltt): ltt :=
  match s with
    | ltt_end      => ltt_end
    | ltt_recv p l => ltt_recv p l 
    | ltt_send p l => ltt_send p l
  end.

Lemma ltt_eq: forall s, s = ltt_id s.
Proof. intro s; destruct s; easy. Defined.

Definition nonE {A: Type} (l: list A): Prop :=
  match l with
    | [] => False
    | x::xs => True
  end.

Definition wfL (l: list fin) := SSortedNList l.

Inductive wf (R: ltt -> Prop): ltt -> Prop :=
  | wf_end : wf R ltt_end
  | wf_recv: forall p l s t,
             wfL l ->
             length l = length s ->
             length s = length t ->
             Forall R t -> 
             wf R (ltt_recv p (zip l (zip s t)))
  | wf_send: forall p l s t,
             wfL l ->
             length l = length s ->
             length s = length t ->
             Forall R t ->
             wf R (ltt_send p (zip l (zip s t))).

Lemma mon_wf: monotone1 wf.
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - constructor.
       - constructor. easy. easy. easy.
         rewrite Forall_forall.
         intros.
         apply LE.
         rewrite Forall_forall in H2.
         apply H2. easy.
       - constructor. easy. easy. easy.
         rewrite Forall_forall.
         intros.
         apply LE.
         rewrite Forall_forall in H2.
         apply H2. easy.
Qed.

Definition wfC (t: ltt) := paco1 wf bot1 t.

Class wfltt: Type :=
{
   utype: ltt;
   sprop: wfC utype
}.

Fixpoint lkp (x: label) (l: list (label*(sort*ltt))): option(sort*ltt) :=
  match l with
    | []            => Datatypes.None
    | (u,(v,t))::xs => if Nat.eqb x u then Datatypes.Some(v,t) else lkp x xs
  end.

Fixpoint wfrec (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (label*(sort*ltt))): Prop :=
  match l1, l2 with
    | [], _ => True  
    | ((l,(s,t))::xs), ((l',(s',t'))::ys) => if Nat.eqb l l' then R1 s s' /\ R2 t t' /\ wfrec R1 R2 xs ys
                                                             else wfrec R1 R2 xs l2 
    | _, [] => False
  end.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (label*(sort*ltt))): Prop :=
  match l1, l2 with 
    | _, [] => True  
    | ((l,(s,t))::xs), ((l',(s',t'))::ys) => if Nat.eqb l l' then R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
                                                             else wfsend R1 R2 l1 ys 
    | [], _ => False
  end.

Fixpoint unzipF {A B C: Type} (l: list(A*(B*C))): list A :=
  match l with
    | []            => []
    | (u,(v,t))::xs => u::unzipF xs 
  end.

Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p xs ys,
                    Nat.le (length ys) (length xs) ->
                    wfrec subsort R xs ys ->
                    subtype R (ltt_recv p xs) (ltt_recv p ys)
  | sub_out : forall p xs ys,
                     Nat.le (length xs) (length ys) ->
                     wfsend subsort R xs ys ->
                     subtype R (ltt_send p xs) (ltt_send p ys).

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.

Lemma destZip: forall {A B C: Type} (l: list (A * (B * C))),
               exists L S xs, l = (zip L (zip S xs)).
Proof. induction l; intros.
       - exists nil. exists nil. exists nil. easy.
       - destruct IHl as (L,(S,(xs,Hxs))).
         destruct a as (a1,(a2,a3)).
         simpl.
         exists (a1::L). exists (a2::S). exists(a3::xs).
         simpl. rewrite Hxs. easy.
Qed.

Lemma ndestZip: forall {A B C: Type} (l: nlist (A * (B * C))),
               exists L S xs, l = (nzip L (nzip S xs)).
Proof. induction l; intros.
       destruct a as (a1,(a2,a3)).
       - exists (nnil a1). exists (nnil a2). exists (nnil a3). easy.
       - destruct IHl as (L,(S,(xs,Hxs))).
         destruct a as (a1,(a2,a3)).
         simpl.
         exists (ncons a1 L). exists (ncons a2 S). exists(ncons a3 xs).
         simpl. rewrite Hxs. easy.
Qed.

Lemma unzipIn: forall (l1:  list (label*(sort*ltt))) l s t, In (l, (s, t)) l1 -> In l (unzipF l1).
Proof. intro l1.
       induction l1; intros.
       - simpl in *. easy.
       - simpl in *.
         destruct H, a, p.
         inversion H. subst. simpl. left. easy.
         simpl. right.
         eapply IHl1. exact H.
Qed.

Lemma inDiff: forall {A: Type} (l: list A) a b, In a l -> ~In b l -> a <> b.
Proof. intros A l.
       induction l; intros.
       - simpl in H. easy.
       - simpl in *.
         intro Ha.
         destruct H. subst.
         apply H0. left. easy.
         subst.
         apply H0. right. easy. 
Qed.

Lemma inLkp: forall (l1:  list (label*(sort*ltt))) l s t,
  NoDup (unzipF l1) ->
  In (l,(s,t)) l1 <-> lkp l l1 = Datatypes.Some(s, t).
Proof. intro l1.
       induction l1; intros.
       split.
       simpl. easy.
       simpl. easy.
       split.
       intro Ha.
       simpl.
       destruct a, p.
       simpl in Ha.
       destruct Ha. inversion H0. subst.
       rewrite Nat.eqb_refl. easy.
       simpl in H.
       pose proof H0 as H00.
       apply unzipIn in H0.
       inversion H. subst.
       specialize(inDiff _ _ _ H0 H3); intros.
       assert(Nat.eqb l n = false).
       { rewrite Nat.eqb_neq. easy. }
       rewrite H2.
       apply IHl1. easy. easy.
       intro Ha.
       simpl in Ha.
       destruct a, p. simpl.
       case_eq(Nat.eqb l n); intros.
       rewrite H0 in Ha.
       rewrite Nat.eqb_eq in H0. subst.
       inversion Ha. subst. left. easy.
       rewrite H0 in Ha.
       eapply IHl1 in Ha.
       right. easy.
       simpl in H.
       inversion H. subst. easy.
Qed.

Lemma ninLkp: forall (l1:  list (label*(sort*ltt))) l,
  NoDup (unzipF l1) ->
  (forall s t, (~ In (l,(s,t)) l1)) <-> lkp l l1 = Datatypes.None.
Proof. intro l1.
       induction l1; intros.
       - split. intro Ha.
         simpl. easy.
       - intro Ha.
         simpl. easy.
       - split. intro Ha.
         simpl. destruct a, p.
         simpl in Ha.
         case_eq(Nat.eqb l n); intros.
         rewrite Nat.eqb_eq in H0. subst.
         specialize(Ha s l0).
         destruct Ha. left. easy.
         apply IHl1.
         simpl in H. inversion H. subst. easy.
         intros.
         rewrite Nat.eqb_neq in H0.
         intro Hb.
         apply H0.
         specialize(Ha s0 t).
         destruct Ha. right. easy.
         
         intro Ha.
         intros. simpl in Ha.
         destruct a, p.
         case_eq(Nat.eqb l n); intros.
         rewrite Nat.eqb_eq in H0. subst.
         rewrite Nat.eqb_refl in Ha.
         easy.
         rewrite H0 in Ha.
         simpl.
         intro Hb.
         rewrite Nat.eqb_neq in H0.
         apply H0.
         destruct Hb.
         inversion H1. easy.
         apply IHl1 in H1. easy.
         simpl in H. inversion H. easy.
         easy.
Qed.

Lemma lkp_eq: forall l1 l2, 
  NoDup (unzipF l1) ->
  NoDup (unzipF l2) ->
  (forall l, lkp l l1 = lkp l l2) <-> (forall x, In x l1 <-> In x l2).
Proof. intros.
       split. intros Ha (l,(s,t)).
       case_eq(lkp l l1); case_eq(lkp l l2); intros.
       - specialize(Ha l).
         rewrite inLkp.
         rewrite inLkp.
         split.
         intro Hb. rewrite <- Ha. easy.
         intro Hb. rewrite Ha. easy.
         easy. easy.
         specialize(Ha l).
         rewrite H1 in Ha.
         rewrite H2 in Ha.
         easy.
         specialize(Ha l).
         rewrite H1 in Ha.
         rewrite H2 in Ha.
         easy.
         specialize(Ha l).
         rewrite <- ninLkp in H1.
         rewrite <- ninLkp in H2.
         specialize(H1 s t).
         specialize(H2 s t).
         split; intro; easy.
         easy. easy.
         
       intros.
       case_eq(lkp l l1); case_eq(lkp l l2); intros.
       destruct p, p0.
       rewrite <- inLkp in H2.
       rewrite <- inLkp in H3.
       pose proof H1 as H10.
       specialize(H1 (l, (s, l0))).
       specialize(H10 (l, (s0, l3))).
       apply H10 in H3.
       rewrite inLkp in H3.
       rewrite inLkp in H2.
       rewrite H3 in H2.
       inversion H2. subst. easy.
       easy. easy. easy. easy.
       
       destruct p.
       rewrite <- inLkp in H3.
       rewrite <- ninLkp in H2.
       specialize(H2 s l0). 
       apply H1 in H3. easy.
       easy. easy.
       destruct p.
       rewrite <- inLkp in H2.
       rewrite <- ninLkp in H3.
       specialize(H3 s l0). 
       apply H1 in H2. easy.
       easy. easy.
       easy.
Qed.

Lemma refl_recv: forall (l1:  list (label*(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfrec R1 R2 l1 l1.
Proof. intros.
       induction l1.
       - easy.
       - destruct a. destruct p. 
         simpl.
         assert ((n =? n)%nat = true). 
         {
          induction n. easy. simpl. easy.
         }
         replace (n =? n)%nat with true. easy. 
Qed.

Lemma refl_send: forall (l1:  list (label*(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfsend R1 R2 l1 l1.
Proof. intros.
       induction l1.
       - easy.
       - destruct a. destruct p.
         simpl.
         assert ((n =? n)%nat = true). 
         {
          induction n. easy. simpl. easy.
         }
         replace (n =? n)%nat with true.
         easy.
Qed.

Lemma stRefl: forall l, subtypeC l l.
Proof. pcofix CIH.
       intros.
       pfold.
       case_eq l; intros.
       constructor.
       constructor. lia.
       subst.
       apply refl_recv.
       constructor.
       repeat intro.
       right. apply CIH.

       constructor. lia.
       apply refl_send.
       constructor.
       repeat intro.
       right. apply CIH.
Qed.

Theorem le_Sn_le : forall n m, Nat.le (S n) m -> Nat.le n m.
Proof.
  intros n m H. unfold Nat.le in *. 
  specialize(Nat.le_succ_l n m); intros. destruct H0. clear H1. specialize(H0 H); intros.
  apply Nat.lt_le_incl; try easy.
Qed.


Lemma trans_recv: forall (l1 l2 l3:  list (label*(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Transitive R1 -> Transitive R2 ->
   Nat.le (length l1) (length l2) ->
   Nat.le (length l2) (length l3) ->
   wfrec R1 R2 l1 l2 -> wfrec R1 R2 l2 l3 -> wfrec R1 R2 l1 l3.
Proof. intros l1.
       induction l1; intros.
       - simpl in *.  easy.
       - destruct a as (l,(s,t)). 
         destruct l2; try easy. destruct p; try easy. destruct p; try easy.
         destruct l3; try easy. destruct p; try easy. destruct p; try easy.
         simpl in *.
         case_eq (Nat.eqb l n); intros; try easy.
         - replace (l =? n )%nat with true in H3.
           case_eq (Nat.eqb n n0)%nat; intros; try easy.
           - replace (n =? n0)%nat with true in H4.
             specialize(Nat.eqb_eq l n); intros. destruct H7. clear H8. specialize(H7 H5); intros.
             specialize(Nat.eqb_eq n n0); intros. destruct H8. clear H9. specialize(H8 H6); intros.
             specialize(Nat.eqb_eq l n0); intros. destruct H9. clear H9.
             specialize(eq_trans H7 H8); intros. specialize(H10 H9); intros.
             replace (l =? n0)%nat with true.
             destruct H3. destruct H11. destruct H4. destruct H13.
             pose proof H as T1. pose proof H0 as T2.
             specialize(H s s0 s1 H3 H4); intros.
             specialize(H0 t l0 l4 H11 H13); intros.
             split; try easy. split; try easy. apply IHl1 with (l2 := l2); try easy.
             specialize(le_S_n (length l1) (length l2) H1); intros. easy.
             specialize(le_S_n (length l2) (length l3) H2); intros. easy.
           - replace (n =? n0)%nat with false in H4.
             specialize(Nat.eqb_eq l n); intros. destruct H7. clear H8. specialize(H7 H5); intros.
             specialize(Nat.eqb_neq n n0); intros. destruct H8. clear H9. specialize(H8 H6); intros.
             case_eq (Nat.eqb l n0); intros; try easy.
             - specialize(Nat.eqb_eq l n0); intros. destruct H10. clear H11. specialize(H10 H9).
               specialize(eq_trans (esym H7) H10); intros. easy.
             apply IHl1 with (l2 := l2); intros; try easy.
             specialize(le_S_n (length l1) (length l2) H1); intros. easy.
             specialize(le_Sn_le (length l2) ((length l3).+1) H2); intros. easy.
         - replace (l =? n)%nat with false in H3.
           - case_eq (Nat.eqb n n0); intros.
             replace (n =? n0)%nat with true in H4.
             specialize(Nat.eqb_neq l n); intros. destruct H7. clear H8. specialize(H7 H5); intros.
             specialize(Nat.eqb_eq n n0); intros. destruct H8. clear H9. specialize(H8 H6); intros.
             case_eq (Nat.eqb l n0); intros.
             - specialize(Nat.eqb_eq l n0); intros. destruct H10. clear H11. specialize(H10 H9).
               specialize(esym (eq_trans H8 (esym H10))); intros. easy.
             apply IHl1 with (l2 := ((n, (s0, l0)) :: l2)); try easy.
             apply le_Sn_le; try easy.
             simpl. replace (n =? n0)%nat with true; try easy.
           - replace (n =? n0)%nat with false in H4.
             case_eq (Nat.eqb l n0); intros.
             - 
                       
Admitted.


Lemma trans_send: forall (l1 l2 l3:  list (label*(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Transitive R1 -> Transitive R2 ->
   NoDup(unzipF l1) -> NoDup(unzipF l2) -> NoDup(unzipF l3) ->
   Nat.le (length l1) (length l2) ->
   Nat.le (length l2) (length l3) ->
   wfsend R1 R2 l1 l2 -> wfsend R1 R2 l2 l3 -> wfsend R1 R2 l1 l3.
Proof. intro l1.
       induction l1; intros.
       - simpl in H6. 
Admitted.

Lemma unzipL: forall {A B C: Type} (l1: list A) (l2: list B) (l3: list C),
  length l1 = length l2 ->
  length l2 = length l3 ->
  unzipF (zip l1 (zip l2 l3)) = l1.
Proof. intros A B C l1.
       induction l1; intros.
       - simpl. case_eq l2; case_eq l3; intros.
         + simpl. easy.
         + simpl. easy.
         + simpl. easy.
         + simpl. easy.
       - case_eq l2; case_eq l3; intros.
         + simpl. subst. easy.
         + simpl. subst. easy.
         + simpl. subst. easy.
         + simpl. f_equal.
           apply IHl1.
           subst. inversion H. easy.
           subst. inversion H0. easy.
Qed.

Lemma reflstH: forall t1 R,
  Reflexive R ->
  wfC t1 ->
  subtype R t1 t1.
Proof. intros.
       case_eq t1; intros.
       constructor.
       constructor.
       lia.
       apply refl_recv.
       constructor. easy.
       subst.
       punfold H0. inversion H0.
       subst. simpl.
       unfold wfL in H3.
(*        rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       constructor.
       lia.
       apply refl_send.
       constructor. easy.
       subst.
       punfold H0. inversion H0.
       subst. simpl.
       unfold wfL in H3.
       rewrite unzipL. easy. easy. easy.
       apply mon_wf.
Qed. *)
Admitted.

Lemma transtH: forall t1 t2 t3 R,
  Transitive R ->
  wfC t1 ->
  wfC t2 ->
  wfC t3 ->
  subtype R t1 t2 ->
  subtype R t2 t3 ->
  subtype R t1 t3.
Proof. intros.
       case_eq t1; case_eq t2; case_eq t3; intros; try (subst; simpl in *; easy).
       subst.
       inversion H3. subst.
       inversion H4. subst.
       constructor.
       lia.
       apply trans_recv with (l2 := l0).
       repeat intro.
       apply sstrans with (s2 := y). easy. easy.
       easy. 
       punfold H2.
       inversion H2. subst.
       unfold wfL in H7.
(*        rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       punfold H1.
       inversion H1. subst.
       unfold wfL in H7.
       rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       punfold H0.
       inversion H0. subst.
       unfold wfL in H7.
       rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       lia.
       lia.
       easy. easy.

       subst.
       inversion H3. subst.
       inversion H4. subst.
       constructor.
       lia.
       apply trans_send with (l2 := l0).
       repeat intro.
       apply sstrans with (s2 := y). easy. easy.
       easy. 

       punfold H0.
       inversion H0. subst.
       unfold wfL in H7.
       rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       punfold H1.
       inversion H1. subst.
       unfold wfL in H7.
       rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       punfold H2.
       inversion H2. subst.
       unfold wfL in H7.
       rewrite unzipL. easy. easy. easy.
       apply mon_wf.
       lia.
       lia.
       easy. easy.
Qed. *)
Admitted.

Lemma st_mon: monotone2 subtype.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - apply sub_in; try easy.
         revert xs H H0.
         induction ys; intros. (* easy.
         destruct a as (l,(s,t)).
         specialize(helperL ((l,(s,t)) :: ys) xs l s t subsort r); intro HH.
         pose proof H0 as HN.
         apply HH in H0.
         destruct H0 as (s',(t',(Ha,(Hb,Hc)))).
         simpl.
         rewrite Hc.
         split. easy. split. apply LE. easy.
         apply IHys. simpl in H. lia.
         simpl in HN. rewrite Hc in HN.
         easy.
         lia.
         simpl. left. easy.
       - apply sub_out; try easy.
         revert ys H H0.
         induction xs; intros. easy.
         destruct a as (l,(s,t)).
         specialize(helperR ((l,(s,t)) :: xs) ys l s t subsort r); intro HH.
         pose proof H0 as HN.
         apply HH in H0.
         destruct H0 as (s',(t',(Ha,(Hb,Hc)))).
         simpl.
         rewrite Hc.
         split. easy. split. apply LE. easy.
         apply IHxs. simpl in H. lia.
         simpl in HN. rewrite Hc in HN.
         easy.
         lia.
         simpl. left. easy.
Qed.
 *)
Admitted.



#[export]
Declare Instance stTrans: Transitive (subtypeC).

(* #[export]
Declare Instance stRefl: Reflexive (subtypeC). *)