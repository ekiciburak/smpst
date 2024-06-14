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
  | gtt_send   : part -> part -> list (label*sort*gtt) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end      => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.

CoFixpoint gparts (t: gtt): coseq part :=
  match t with
    | gtt_send p q [(l,s,g')] => Delay (cocons p (Delay (cocons q (gparts g'))))
    | _                       => Delay conil
  end.

(* inductive membership check *)
Inductive coseqIn: part -> coseq part -> Prop :=
  | CoInSplit1 x xs y ys: force xs = cocons y ys -> x = y  -> coseqIn x xs
  | CoInSplit2 x xs y ys: force xs = cocons y ys -> x <> y -> coseqIn x ys -> coseqIn x xs.

Inductive gt2gtt (R: global -> gtt -> Prop): global -> gtt -> Prop :=
  | gt2gtt_end: gt2gtt R g_end gtt_end
  | gt2gtt_snd: forall p q l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                gt2gtt R (g_send p q (zip (zip l s) xs)) (gtt_send p q (zip (zip l s) ys))
  | gt2gtt_mu : forall g t,
                gt2gtt R (subst_global ((g_rec g) .: g_var) g) t ->
                gt2gtt R (g_rec g) t.

Definition gt2lttC g t := paco2 gt2gtt bot2 g t.

Fixpoint findpath (l: list (label*sort*gtt)) (lbl: label): option gtt :=
  match l with
    | []           => Datatypes.None
    | (l1,s,g)::xs => if Nat.eqb l1 lbl then Datatypes.Some g else findpath xs lbl
  end.

Inductive gttstep (R: gtt -> gtt -> part -> part -> Prop): gtt -> gtt -> part -> part -> Prop :=
  | steq : forall p q l xs gc,
(*                eqb p q = false -> *)
                  Datatypes.Some gc = findpath xs l -> gttstep R (gtt_send p q xs) gc p q
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
                  gttstep R (gtt_send r s (zip (zip L S) xs)) (gtt_send p q (zip (zip L S) ys)) p q.

Definition gttstepC g1 g2 p q := paco4 gttstep bot4 g1 g2 p q.

Parameter mergeList: forall {A: Type}, list A -> A -> Prop.

Inductive projection (R: part -> gtt -> ltt -> Prop): part -> gtt -> ltt -> Prop :=
  | proj_end : forall g r, (coseqIn r (gparts g) -> False) -> projection R r g (ltt_end)
  | proj_in  : forall p r l s xs ys,
               List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
               projection R r (gtt_send p r (zip (zip l s) xs)) (ltt_recv p (zip (zip l s) ys))
  | proj_out : forall p r l s xs ys,
               List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
               projection R r (gtt_send r p (zip (zip l s) xs)) (ltt_send p (zip (zip l s) ys))
  | proj_cont: forall p q r l s xs ys T,
               r <> p ->
               r <> q ->
               List.Forall (fun u => R r (fst u) (snd u)) (zip xs ys) ->
               @mergeList ltt ys T ->
               projection R r (gtt_send p q (zip (zip l s) xs)) T.

Definition projectionC r g t := paco3 projection bot3 r g t.

Definition dropDups {A: Type} (l1 l2: list A) := 
  (forall x, In x l1 <-> In x l2) /\ NoDup l2.

Inductive dropM {A : Type} : A -> list A -> list A -> Prop :=
  | drop0: forall a, dropM a [] []
  | drop1: forall x l1 xs, In x l1 -> ~In x xs -> (forall a, In a (x::xs) <-> In a l1) -> dropM x l1 xs.

Inductive mergeH {A B C: Type}: list (A*B*C) -> list (A*B*C) -> list (A*B*C) -> Prop :=
  | merge0: mergeH [] [] []
  | merge1: forall l1 s1 c1 xs L1 L2 L3,
            In (l1,s1,c1) L1 ->
            (forall s2 c2, (In (l1,s2,c2) L2) -> False) ->
            dropM (l1,s1,c1) L1 L3 ->
            mergeH L3 L2 xs ->
            mergeH L1 L2 ((l1,s1,c1)::xs)
  | merge2: forall l2 s2 c2 xs L1 L2 L3,
            In (l2,s2,c2) L2 ->
            (forall s1 c1, (In (l2,s1,c1) L1) -> False) ->
            dropM (l2,s2,c2) L2 L3 ->
            mergeH L1 L3 xs ->
            mergeH L1 L2 ((l2,s2,c2)::xs)
  | merge3: forall x xs L1 L2 L3 L4,
            In x L1 ->
            In x L2 ->
            dropM x L1 L3 ->
            dropM x L2 L4 ->
            mergeH L3 L4 xs ->
            mergeH L1 L2 (x::xs).

Definition merge {A B C: Type} (l1 l2 l3: list (A*B*C)) :=
  mergeH l1 l2 l3 /\ dropDups (l1 ++ l2) l3.

Inductive merge_branch: ltt -> ltt -> ltt -> Prop :=
  | mbc: forall p l1 l2 l3, merge l1 l2 l3 ->
                            merge_branch (ltt_recv p l1) (ltt_recv p l2) (ltt_recv p l3)
  | mbe: forall L1 L2, L1 = L2 -> merge_branch L1 L2 L1.

Definition t1 := [(3,sint,ltt_end); (5,snat,ltt_end)].

Definition t2 := [(4,sint,ltt_end); (5,snat,ltt_end)].

Definition t3 := [(3,sint,ltt_end); (5,snat,ltt_end); (4,sint,ltt_end)].

Example _39_d: merge_branch (ltt_recv "q" t1) (ltt_recv "q" t2) (ltt_recv "q" t3).
Proof. constructor.
       unfold merge.
       split.
       unfold t1, t2, t3.
       specialize (merge1 3 sint ltt_end
                   ([(5, snat, ltt_end); (4, sint, ltt_end)])
                   [(3, sint, ltt_end); (5, snat, ltt_end)] [(4, sint, ltt_end); (5, snat, ltt_end)]
                   [(5, snat, ltt_end)] 
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

       specialize (merge3 (5,snat,ltt_end) [(4, sint, ltt_end)]
                  [(5, snat, ltt_end)] [(4, sint, ltt_end); (5, snat, ltt_end)]
                  [] [(4, sint, ltt_end)]
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
       intros ((u,v),y).

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
                   [] [(4, sint, ltt_end)] []
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
       intros ((l1,s1),c1).
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

Definition t4 := [(0,snat,ltt_end)].

Definition t5 := [(0,sint,ltt_end)].

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

Definition t6 := [(3,snat,ltt_end)].

Definition t7 := [(3,snat,ltt_recv "q" [(3,snat,ltt_end)])].

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
           specialize (H6 snat (ltt_recv "q" [(3,snat,ltt_end)])).
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

Example _39_c: forall l, merge_branch (ltt_send "q" [(3,snat,ltt_end)]) (ltt_send "q" [(4,snat,ltt_end)]) l -> False.
Proof. intros.
       inversion H.
       subst. easy.
Qed.

Example _39_a: merge_branch (ltt_send "q" [(0,snat,ltt_end)]) (ltt_send "q" [(0,snat,ltt_end)]) (ltt_send "q" [(0,snat,ltt_end)]).
Proof. constructor.
       easy.
Qed.

Example _39_b: forall l, merge_branch (ltt_send "p" [(0,snat,ltt_end)]) (ltt_send "q" [(0,snat,ltt_end)]) l -> False.
Proof. intros l H.
       inversion H.
       easy.
Qed.

Lemma _37: forall {A B C: Type} (t1 t2 t3 t4 t5 t6: list (A * B * C)), 
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


