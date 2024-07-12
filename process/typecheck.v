From SST Require Import aux.unscoped aux.expressions process.processes type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Inductive ctx: Type :=
  | empty: ctx
  | consS: fin -> sort -> ctx -> ctx
  | consT: fin -> ltt -> ctx -> ctx.

Fixpoint memS (n: fin) (s: sort) (m: ctx): Prop :=
  match m with
    | consS u v m1 => (n = u /\ (subsort s v \/ v = s)) \/ memS n s m1
    | consT u v m1 => memS n s m1
    | _            => False
  end.

Fixpoint memT (n: fin) (t: ltt) (m: ctx): Prop :=
  match m with
    | consT u v m1 => (n = u /\ (subtypeC t v \/ v = t)) \/ memT n t m1
    | consS u v m1 => memT n t m1
    | _            => False
  end.

Definition extendS (m: ctx) (s: fin) (t: expressions.sort) :=
  consS s t m.

Definition extendT (m: ctx) (s: fin) (t: ltt) :=
  consT s t m.

Fixpoint lookupS (m: ctx) (s: fin): option expressions.sort :=
  match m with
    | empty          => None
    | consS s' t' xs => if Nat.eqb s s' then Some t' else lookupS xs s
    | consT s' t' xs => lookupS xs s
  end.

Fixpoint lookupT (m: ctx) (s: fin): option ltt :=
  match m with
    | empty          => None
    | consT s' t' xs => if Nat.eqb s s' then Some t' else lookupT xs s
    | consS s' t' xs => lookupT xs s
  end.

Fixpoint infr_expr (m: ctx) (e: expr): option sort :=
  match e with
    | e_var x   => lookupS m x
    | e_val v   => 
      match v with
        | vint i  => Some sint
        | vbool b => Some sbool
        | vunit u => Some sunit
        | vnat n =>  Some snat
      end
    | e_succ e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some gint => Some sint
        | _         => None
      end
    | e_neg e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some gint => Some sint
        | _         => None
      end
    | e_not e1 => 
      let se1 := infr_expr m e1 in
      match se1 with
        | Some goobl => Some sbool
        | _          => None
      end
    | e_gt e1 e2 => 
      let se1 := infr_expr m e1 in
      let se2 := infr_expr m e2 in
      match pair se1 se2 with
        | pair (Some sint) (Some sint) => Some sbool
        | _                            => None
      end
    | e_plus e1 e2 => 
      let se1 := infr_expr m e1 in
      let se2 := infr_expr m e2 in
      match pair se1 se2 with
        | pair (Some sint) (Some sint) => Some sint
        | _                            => None
      end
  end.

Inductive subCtx: ctx -> ctx -> Prop :=
  | sctx1: forall m t t' c c', subCtx c c' -> subtypeC t t' -> subCtx (consT m t c) (consT m t' c')
  | sctx2: forall m t c c', subCtx c c' -> subCtx (consT m t c) (consT m t c')
  | sctx3: forall m s s' c c', subCtx c c' -> subsort s s' -> subCtx (consS m s c) (consS m s' c')
  | sctx4: forall m s c c', subCtx c c' -> subCtx (consS m s c) (consS m s c')
  | subctxr: forall c, subCtx c c. 

Fixpoint refCtxT (c1 c2: ctx): Prop :=
  match (c1, c2) with
    | (consT u1 v1 m1, consT u2 v2 m2) => (u1 = u2 /\ (subtypeC v1 v2 \/ v1 = v2)) /\ refCtxT m1 m2
    | (consS u1 v1 m1, consS u2 v2 m2) => (u1 = u2 /\ (subsort  v1 v2 \/ v1 = v2)) /\ refCtxT m1 m2
    | (empty, empty)                   => True
    | _                                => False
  end.

Definition eq_ctx (m1 m2: ctx) := 
  (forall n s, memS n s m1 <-> memS n s m2) /\
  (forall n t, memT n t m1 <-> memT n t m2).

Definition eq_ctxL (m1 m2: ctx) := 
  (forall n s, memS n s m1 -> memS n s m2) /\
  (forall n t, memT n t m1 -> memT n t m2).

Inductive typ_expr: ctx -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = lookupS c s -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c c' e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 refCtxT c c' ->
                                 typ_expr c' e s'
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint.

Fixpoint matchSel (l: label) (xs: list(label*(expressions.sort)*ltt)%type): option ((sort)*ltt)%type :=
  match xs with
    | nil           => None
    | (lbl,s,t)::ys => if Nat.eqb l lbl then Some(s,t) else matchSel l ys
  end.

(* Require Import Coq.Init.Logic. *)

(* Definition sub_ctx (m1 m2: ctx) :=
  ((forall n s s', subsort s s'  -> (memS n s m1 <-> memS n s' m2)) \/ eq_ctx m1 m2) /\
  ((forall n t t', subtypeC t t' -> (memT n t m1 <-> memT n t' m2)) \/ eq_ctx m1 m2). *)

Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Fixpoint findCtx (n: fin) (t: ltt) (m: ctx): Prop :=
  match m with
    | consT u v m1 => (n = u /\ v = t) \/ findCtx n t m1
    | consS u v m1 => findCtx n t m1
    | _            => False
  end.

Inductive typ_proc: fin -> fin -> ctx -> process -> ltt -> Prop :=
  | tc_inact: forall m em c, typ_proc m em c (p_inact) (ltt_end)
  | tc_var  : forall m em c s t, Some t = lookupT c s ->
                                 typ_proc m em c (p_var s) t
  | tc_mu   : forall m em c p t, let c' := extendT c m t in
                                 typ_proc (S m) em c' p t ->
                                 typ_proc m em c (p_rec p) t
  | tc_ite  : forall m em c e p1 p2 T, typ_expr c e sbool ->
                                       typ_proc m em c p1 T ->
                                       typ_proc m em c p2 T ->
                                       typ_proc m em c (p_ite e p1 p2) T
  | tc_sub  : forall m em c c' p t t', typ_proc m em c p t ->
                                       subtypeC t t' ->
                                       refCtxT c c' -> 
                                       typ_proc m em c' p t'
  | tc_recv : forall m em c p L ST P T,
                     length L = length ST ->
                     length ST = length P ->
                     length P = length T ->
                     List.Forall (fun u => typ_proc m (S em) (extendS c em (fst u)) (fst (snd u)) (snd (snd u))) (zip ST (zip P T)) ->
                     typ_proc m em c (p_recv p (zip (zip L ST) P)) (ltt_recv p (zip (zip L ST) T))
  | tc_send: forall m em c p l e P S T, typ_expr c e S ->
                                        typ_proc m em c P T ->
                                        typ_proc m em c (p_send p l e P) (ltt_send p [(l,S,T)]).

Lemma _a23_d: forall P m em Q T G,
  typ_proc m em G P T ->
  (P = (p_rec Q) -> typ_proc (S m) em (extendT G m T) Q T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
(*        destruct H0 as (Ha, Hb). *)
(*        inversion Ha. subst.  *)
       unfold c' in *.
       easy.

       specialize(tc_sub (S m) em (extendT c m t) (extendT c' m t') Q t t'); intro Hs.
       apply Hs.
       apply IHtyp_proc. easy. easy.
       simpl.
       split. split. easy.
       left. easy.
       easy.
Qed.

Definition PBob: process := p_recv "Alice" [(1, snat, p_send "Carol" 2 (e_val (vnat 100)) p_inact);
                                            (4, snat, p_send "Carol" 2 (e_val (vnat 2)) p_inact)].

Definition TBob: ltt := ltt_recv "Alice" [(1, snat, ltt_send "Carol" [(2, snat, ltt_end)]);
                                          (4, snat, ltt_send "Carol" [(2, snat, ltt_end)])].

Example _317_b: typ_proc 0 0 empty PBob TBob.
Proof. unfold PBob, TBob.
       (* typechecking the outermost structure *)
       specialize(tc_recv 0 0 empty "Alice"
                         [1; 4]
                         [snat; snat]
                         [(p_send "Carol" 2 (e_val (vnat 100)) p_inact); (p_send "Carol" 2 (e_val (vnat 2)) p_inact)]
                         [(ltt_send "Carol" [(2, snat, ltt_end)]); (ltt_send "Carol" [(2, snat, ltt_end)])]
                         ); intro HR.
       simpl in HR.
       apply HR; clear HR; try easy.
       apply Forall_forall.
       intros (s, (p, l)) HIn.
       simpl in HIn.
       destruct HIn as [HIn | HIn].
       inversion HIn. simpl.
       subst.

       (* typechecking the first continuation *)
       specialize(tc_send 0 1 (extendS empty 0 snat) "Carol"
                          2
                          (e_val (vnat 100))
                          p_inact
                          snat
                          ltt_end
         ); intro HS.
       simpl in HS.
       apply HS; clear HS.

       (*expression typcheck*)
       constructor.

       constructor.
       simpl.
       destruct HIn as [HIn | HIn].
       inversion HIn. simpl.
       subst.
       (* typechecking the second continuation *)
       specialize(tc_send 0 1 (extendS empty 0 snat) "Carol"
                          2
                          (e_val (vnat 2))
                          p_inact
                          snat
                          ltt_end
         ); intro HS.
       simpl in HS.
       apply HS; clear HS.

       (*expression typcheck*)
       constructor.

       constructor.

       easy.
Qed.

Definition PBob2: process := p_rec (p_send "Carol" 2 (e_val (vnat 100)) (p_var 0)).
CoFixpoint TBob2: ltt := ltt_send "Carol" [(2, snat, TBob2)].

Example newEx: typ_proc 0 0 empty PBob2 TBob2.
Proof. unfold PBob2.
       rewrite(ltt_eq TBob2). simpl.
       constructor.
       constructor.
       constructor.
       constructor.
       simpl.
       rewrite(ltt_eq TBob2) at 1. simpl.
       easy.
Qed.




(* Lemma ref_ctx_1: forall c c' t t' u,
 refCtxT t t' c c' -> refCtxT u u c c'.
Proof. intro c.
       induction c; intros.
       - case_eq c'; intros.
         + easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - case_eq c'; intros.
         + subst. simpl in H. simpl. easy.
         + subst. simpl. simpl in H.
           destruct H as (Ha, (Hb, Hc)).
           subst. split. easy. split. easy.
           apply IHc with (t := t) (t' := t'). easy.
         + subst. simpl in H. easy.
       - case_eq c'; intros.
         + subst. simpl in H. simpl. easy.
         + subst. simpl in H. easy.
         + subst. simpl. simpl in H.
           destruct H as (Ha, Hb).
           destruct Ha as [Ha | Ha].
           destruct Ha as (Ha,(Hc,Hd)).
           subst.
           
           subst. split. easy. split. easy.
           apply IHc with (t := t) (t' := t'). easy. *)


Lemma _a23_a: forall m em p L S Q P G T, 
  typ_proc m em G P T ->
  P = (p_recv p (zip (zip L S) Q)) -> 
  (exists T', length T' = length L -> length T' = length S -> length T' = length Q -> subtypeC (ltt_recv p (zip (zip L S) T')) T /\  
  List.Forall (fun u => typ_proc m (Datatypes.S em) (extendS G em (fst u)) (fst (snd u)) (snd (snd u))) (zip S (zip Q T'))).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T',IHtyp_proc).
       exists T'. intros Hla1 Hla2 Hla3.
       split.
       specialize(IHtyp_proc Hla1 Hla2 Hla3).
       destruct IHtyp_proc as (IHtyp_proc, Ha).
       specialize(stTrans (ltt_recv p (zip (zip L S) T')) t t' IHtyp_proc); intro HT.
       apply HT.
       
        easy.
       
       (**)
       destruct IHtyp_proc as (IHtyp_proc, Ha). easy. easy. easy.
       apply Forall_forall.
       intros (x1,(x2,x3)) Hx.
       simpl in *.
       rewrite Forall_forall in Ha.
       specialize(Ha (x1,(x2,x3))). simpl in Ha.
       specialize(tc_sub m (Datatypes.S em) (extendS c em x1) (extendS c' em x1) x2 x3 x3); intro HTC.
       apply HTC.
(*        specialize(tc_sub m (Datatypes.S em) c); intro HTC. *)
       apply Ha. easy.
       apply stRefl.
       simpl.
       split. split. easy.  right. easy. easy.

       rewrite Forall_forall in H3.
       exists T.
       intros Hla1 Hla2 Hla3.
       split.
       inversion H0. subst.
       assert(length (zip L0 ST) = length L0) as Hasrt1.
       { symmetry.
         apply zip_len. easy.
       }
       assert(L = L0).
       { specialize(zip_eq (zip L0 ST) (zip L S) P Q); intro HH.
         assert(length (zip L0 ST) = length P).
         { symmetry.
           rewrite <- H1, <- H.
           apply zip_len. easy.
         }
         assert(length P = length (zip L S)).
         {
           rewrite H2, Hla1. apply zip_len.
           rewrite <- Hla1. easy.
         }
         assert(length (zip L S) = length Q).
         {  rewrite <- Hla3, Hla1.
            symmetry. apply zip_len.
            rewrite <- Hla1.  easy.
         }
         specialize(HH H4 H5 H7 H6).
         destruct HH as (HHa,HHb).
         specialize(zip_eq L0 L ST S); intro HH1.
         subst.
         assert(length ST = length L).
         { rewrite H1, <- Hla3. easy. }
         assert(length L = length S).
         { rewrite <- Hla1. easy. }
         specialize(HH1 H H8 H9 HHa). easy.
       }
       assert(S = ST).
       {
         specialize(zip_eq (zip L0 ST) (zip L S) P Q); intro HH.
         assert(length (zip L0 ST) = length P).
         { rewrite Hasrt1, H. easy. }
         assert(length P = length (zip L S)).
         { rewrite H2, Hla1. apply zip_len.
           rewrite <- Hla1. easy.
         }
         assert(length (zip L S) = length Q).
         {  rewrite <- Hla3, Hla1.
            symmetry. apply zip_len.
            rewrite <- Hla1.  easy.
         }
         specialize(HH H5 H7 H8 H6).
         destruct HH as (HHa,HHb).
         specialize(zip_eq L0 L ST S); intro HH1.
         assert(length ST = length L).
         { rewrite H1, H2. easy. }
         assert(length L = length S).
         { rewrite <- Hla1.  easy. }
         specialize(HH1 H H9 H10 HHa). easy.
       }
       assert(P = Q).
       {
         specialize(zip_eq (zip L0 ST) (zip L S) P Q); intro HH.
         assert(length (zip L0 ST) = length P).
         { symmetry.
           rewrite <- H1, <- H.
           apply zip_len. easy.
         }
         assert(length P = length (zip L S)).
         {
           rewrite H2, Hla1. apply zip_len.
           rewrite <- Hla1. easy.
         }
         assert(length (zip L S) = length Q).
         {  rewrite <- Hla3, Hla1.
            symmetry. apply zip_len.
            rewrite <- Hla1.  easy.
         }
         specialize(HH H7 H8 H9 H6). easy.
       }
       subst.
       pfold.
       apply sub_in. easy. easy.
       clear H H1 H2 H3 H6 Hla1 Hla2 Hla3 Hasrt1.
       apply Forall_forall.
       intros (x1,x2) Hx.
       induction ST; intros.
       simpl in Hx. easy.
       simpl in Hx.
       destruct Hx as [Hx | Hx].
       inversion Hx. subst.
       simpl. apply srefl.
       simpl. apply IHST. easy. easy.

       apply Forall_forall.
       intros (x1,x2) Hx.
       clear H H1 H2 H3 Hla1 Hla2 Hla3 Hasrt1.
       induction T; intros.
       simpl in Hx. easy.
       simpl in Hx.
       simpl in IHT.
       destruct Hx as [Hx | Hx].
       inversion Hx. subst. simpl.
       specialize(stRefl x2); intro HT.
       punfold HT. apply st_mon.
       simpl. apply IHT. easy.
       
       (**)
       apply Forall_forall.
       intros (x1,(x2,x3)) Hx.
       simpl in *.
       specialize(H3 (x1,(x2,x3))). simpl in H3.
       inversion H0. subst.
       apply H3.
       assert(L = L0).
       { specialize(zip_eq (zip L0 ST) (zip L S) P Q); intro HH.
         assert(length (zip L0 ST) = length P).
         { symmetry.
           rewrite <- H1, <- H.
           apply zip_len. easy.
         }
         assert(length P = length (zip L S)).
         {
           rewrite H2, Hla1. apply zip_len.
           rewrite <- Hla1. easy.
         }
         assert(length (zip L S) = length Q).
         {  rewrite <- Hla3, Hla1.
            symmetry. apply zip_len.
            rewrite <- Hla1.  easy.
         }
         specialize(HH H4 H5 H7 H6).
         destruct HH as (HHa,HHb).
         specialize(zip_eq L0 L ST S); intro HH1.
         subst.
         assert(length ST = length L).
         { rewrite H1, <- Hla3. easy. }
         assert(length L = length S).
         { rewrite <- Hla1. easy. }
         specialize(HH1 H H8 H9 HHa). easy.
       }
       assert(S = ST).
       {
         specialize(zip_eq (zip L0 ST) (zip L S) P Q); intro HH.
         assert(length (zip L0 ST) = length P).
         { rewrite <- H1, <- H.
           symmetry. apply zip_len. easy.  }
         assert(length P = length (zip L S)).
         { rewrite H2, Hla1. apply zip_len.
           rewrite <- Hla1. easy.
         }
         assert(length (zip L S) = length Q).
         {  rewrite <- Hla3, Hla1.
            symmetry. apply zip_len.
            rewrite <- Hla1.  easy.
         }
         specialize(HH H5 H7 H8 H6).
         destruct HH as (HHa,HHb).
         specialize(zip_eq L0 L ST S); intro HH1.
         assert(length ST = length L).
         { rewrite H1, H2. easy. }
         assert(length L = length S).
         { rewrite <- Hla1.  easy. }
         specialize(HH1 H H9 H10 HHa). easy.
       }
       assert(P = Q).
       {
         specialize(zip_eq (zip L0 ST) (zip L S) P Q); intro HH.
         assert(length (zip L0 ST) = length P).
         { symmetry.
           rewrite <- H1, <- H.
           apply zip_len. easy.
         }
         assert(length P = length (zip L S)).
         {
           rewrite H2, Hla1. apply zip_len.
           rewrite <- Hla1. easy.
         }
         assert(length (zip L S) = length Q).
         {  rewrite <- Hla3, Hla1.
            symmetry. apply zip_len.
            rewrite <- Hla1.  easy.
         }
         specialize(HH H7 H8 H9 H6). easy.
       }
       subst.
       easy.
Qed.

Lemma _a23_bA: forall m em p l e Q P G T, 
  typ_proc m em G P T ->
  (P = (p_send p l e Q) -> exists S T', typ_expr G e S /\ typ_proc m em G Q T' /\ (forall S', subsort S' S -> subtypeC (ltt_send p [(l,S',T')]) T)).
Proof. intros m em p l e Q P G T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H2).
       destruct IHtyp_proc as (S',(T',Ha)).
       exists S'. exists T'.
       split.
       specialize(sc_sub c c' e S' S'); intro HSS.
       apply HSS.
       apply Ha. constructor. easy.
       split.
       specialize(tc_sub m em c c' Q T' T'); intro HTS.
       apply HTS.
       apply Ha. apply stRefl. easy.
       intros.
       destruct Ha as (Ha,(Hb,Hc)).
       specialize(Hc S'0 H3).
(*        destruct Hc as (Hc,Hd). *)
       specialize(stTrans (ltt_send p [(l, S'0, T')]) t t' Hc H0); intro HT.
       apply HT.
       exists S. exists T.
       intros.
       inversion H1. subst.
       split. easy. split. easy.
       intros.
       specialize(sub_out (upaco2 subtype bot2)
          p [l] [S] [S'] [T] [T]
        ); intros HHa.
       simpl in HHa.
       pfold.
       apply HHa. easy. easy.
       apply Forall_forall. simpl.
       intros (s1, s2) Hs. destruct Hs.
       inversion H3. subst. simpl. easy.
       easy.
       apply Forall_forall. simpl.
       intros (T1, T2) Hs. destruct Hs.
       inversion H3. subst.
       simpl. left. pfold.
       specialize(stRefl T2); intro HT.
       punfold HT. apply st_mon.
       easy.
Qed.

Lemma _a23_b: forall m em p l e Q P G T, 
  typ_proc m em G P T ->
  (P = (p_send p l e Q) -> exists S S' T', typ_expr G e S /\ typ_proc m em G Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,S',T')]) T).
Proof. intros m em p l e Q P G T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H2).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split.
       specialize(sc_sub c c' e S S); intro HSS.
       apply HSS. easy. apply srefl. easy.
       split.
       specialize(tc_sub m em c c' Q T' T'); intro HTS.
       apply HTS. easy.
       apply stRefl. easy. split. easy.
       destruct Ha as (Ha,(Hb,(Hc,Hd))).
       specialize(stTrans (ltt_send p [(l, S', T')]) t t' Hd H0); intro HT.
       apply HT.
       exists S. exists S. exists T.
       inversion H1. subst.
       split. easy. split. easy.
       split. apply srefl. 
       specialize(sub_out (upaco2 subtype bot2)
          p [l] [S] [S] [T] [T]
        ); intros HHa.
       simpl in HHa.
       pfold.
       apply HHa. easy. easy.
       apply Forall_forall. simpl.
       intros (s1, s2) Hs. destruct Hs.
       inversion H2. subst. simpl. apply srefl.
       easy.
       apply Forall_forall. simpl.
       intros (T1, T2) Hs. destruct Hs.
       inversion H2. subst.
       simpl. left. pfold.
       specialize(stRefl T2); intro HT.
       punfold HT. apply st_mon.
       easy.
Qed.

Lemma _a23_c: forall P m em e Q1 Q2 T G,
  typ_proc m em G P T ->
  (P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc m em G Q1 T1 /\ typ_proc m em G Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
       exists T. exists T.
       split. easy. split. easy. split.
       specialize(stRefl T); intro HT. easy.
       specialize(stRefl T); intro HT. easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T1,(T2,(Ha,(Hb,(Hc,Hd))))).
       exists T1. exists T2.
       split.
       specialize(tc_sub m em c c' Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. easy. 
       split.
       specialize(tc_sub m em c c' Q2 T2 T2); intro HTS.
       apply HTS. easy. apply stRefl. easy. 
       split.
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       specialize(stTrans T2 t t' Hd H1); intro HT. easy.
Qed.


(* Lemma _a23_d_v2: forall P m em Q T G,
  typ_proc m em G P T ->
  (exists T', (P = (p_rec Q) /\ subtypeC T T') -> typ_proc (S m) em (extendT G m T') Q T').
Proof. intros.
       induction H; try (exists ltt_end; easy).
       exists t.
       intros (Ha, Hb). 
       inversion Ha. subst. 
       unfold c' in *.
       easy.

       destruct IHtyp_proc as (T', Hp).
       exists T'.
       intros (Ha, Hb).
       apply Hp.
       split. easy.
       specialize(stTrans t t' T' H0 Hb); intro HT.
       exact HT.
Qed.
 *)

Lemma helper0: forall c d n s, refCtxT c d -> memS n s c -> memS n s d.
Proof. intro c.
       induction c; intros.
       - case_eq d; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. easy.
       - case_eq d; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. simpl.
           simpl in H0.
           destruct H0.
           destruct H0.
           subst. 
           destruct H1. left.
           split. easy.
           destruct H. destruct H. destruct H2.
           subst. left.
           apply sstrans with (s2 := s); easy.
           subst. left. easy.
           subst. left.
           destruct H.
           destruct H. split. easy.
           destruct H1. left. easy. right. easy.
           right.
           apply IHc. easy. easy.
           subst. simpl in H. easy.
       - case_eq d; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy. 
         + subst. simpl in H. simpl.
           apply IHc. easy.
           simpl in H0. easy.
Qed.

Lemma helper1: forall c d n s, refCtxT c d -> memT n s c -> memT n s d.
Proof. intro c.
       induction c; intros.
       - case_eq d; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. easy.
       - case_eq d; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. simpl.
           apply IHc. easy. easy.
           subst. simpl in H. easy.
       - case_eq d; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. simpl.
           simpl in H0.
           destruct H0.
           destruct H0.
           subst. 
           destruct H1. left.
           split. easy.
           destruct H. destruct H. destruct H2.
           subst. left.
           specialize (stTrans s l l0 H0 H2); intro HT. easy.
           subst. left. easy.
           subst. left.
           destruct H.
           destruct H. split. easy.
           destruct H1. left. easy. right. easy.
           right.
           apply IHc. easy. easy.
Qed.

Lemma helper: forall c c' u, refCtxT c c' -> eq_ctxL u c -> eq_ctxL u c'. 
Proof. intro c.
       induction c; intros.
       - case_eq c'; intros.
         + subst. easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - case_eq c'; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H.
           destruct H as ((Ha1,Ha2),Hb).
           unfold eq_ctxL in H0.
           unfold eq_ctxL.
           split. 
           intros.
           apply H0 in H. simpl in H.
           simpl.
           destruct H. left. subst.
           split. easy. 
           destruct Ha2.
           destruct H. destruct H2.
           left.
           apply sstrans with (s2 := s); easy.
           subst. left. easy.
           subst. easy.
           right. 
           apply helper0 with (c := c); easy.
           intros.
           apply H0 in H. simpl in H.
           simpl.  
           apply helper1 with (c := c); easy.
           subst. simpl in H. easy.
       - case_eq c'; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
         + subst. simpl in H.
           destruct H as ((Ha1,Ha2),Hb).
           unfold eq_ctxL in H0.
           unfold eq_ctxL.
           split. 
           intros.
           apply H0 in H. simpl in H.
           simpl.
           apply helper0 with (c := c); easy.
           intros. 
           apply H0 in H. simpl in H.
           destruct H. left. subst.
           split. easy. 
           destruct Ha2.
           destruct H. destruct H2.
           left.
           specialize (stTrans t l l0 H2 H1); intro HT. easy.
           subst. left. easy.
           subst. easy.
           right.
           apply helper1 with (c := c); easy.
Qed.

(* Search (?a + ?b = ?b + ?a). *)

Lemma _a23_e: forall P (n: fin) m em n T G,
  typ_proc m em G P T ->
  (P = (p_var n) -> exists T' G', eq_ctxL (extendT G' n T') G /\ subtypeC T' T).
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       induction c; intros.
       simpl in H. easy.
       simpl in H.
       specialize(IHc H).
       destruct IHc as (T',(G',(Ha,Hb))).
       exists  T'. exists (consS n1 s G').

       split.
       unfold extendT.
       unfold eq_ctxL in *. 
       split.
       intros n2 s0 HH. simpl.
       destruct Ha as (Ha1,Ha2).

       destruct HH as [HH | HH].
       destruct HH as( H1a, H1b).
       destruct H1b as [HH | HH].
       subst. unfold extendT. simpl.
       left. split. easy. left. easy.
       left. split. easy.
       right. easy.
       right.
       apply Ha1. easy.
       
       intros.
       simpl. simpl in H1.
 
       destruct Ha as (Ha,Hc).
       apply Hc in H1.
       simpl in H1. easy.
       easy.

(*        intro HH.
       simpl in HH.
       destruct HH as [HH | HH].
       destruct HH as( H1a, H1b).
       destruct H1b as [HH | HH].
       subst. unfold extendT. simpl.
       left. split. easy. left. easy.
       left. split. easy.
       right. easy.
       right.
       apply Ha1. easy. *)

(*        intros.
       destruct Ha as (Ha1,Ha2).
       split. intro HH.
       simpl in HH. simpl.
       apply Ha2 in HH.
       unfold extendT in HH. simpl in HH. easy.
       intro HH.
       simpl. simpl in HH.
       apply Ha2. simpl. easy.
       easy. *)

       simpl in H.
       case_eq((Nat.eqb n0 n1)); intro Heq.
       rewrite Heq in H. inversion H. subst.
       exists l. exists c. split. unfold extendT.
       apply Nat.eqb_eq in Heq. subst. easy.
       specialize(stRefl l); intro HT. easy.
       rewrite Heq in H.
       specialize(IHc H).
       destruct IHc as (T',(G',(Ha,Hb))).
       exists T'. exists (consT n1 l G').
       split.

       unfold eq_ctxL, extendT in *.
       split.
       intros. simpl.
       destruct Ha as (Ha1,Ha2).
(*        split. intro HH. *)
       apply Ha1. easy.
       intros. simpl. simpl in H1.
       
       destruct H1.
       right. apply Ha.
       simpl. left. easy.
       destruct H1.
       left. easy.
       right.
       apply Ha. simpl. right. easy.
       easy.

       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T',(G',(Ha,Hb))).
       exists T'. exists G'.
       split.
       apply helper with (c := c); easy.
       specialize(stTrans T' t t' Hb H1); intro HT. easy.
Qed.

Lemma _a23_f: forall P m em T G,
  typ_proc m em G P T ->
  (P = (p_inact) -> T = ltt_end).
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc eq_refl).
       subst.
       punfold H1. inversion H1. easy.
       apply st_mon.
Qed.

Lemma refCtxT_refl: forall G, refCtxT G G.
Proof. intro G.
       induction G; intros.
       - easy.
       - simpl. split. split. easy. right. easy.
         easy.
       - simpl. split. split. easy. right. easy.
         easy.
Qed.

Lemma asd: forall T T' m em, subtypeC T T' ->
  typ_proc m em (extendT empty m T') (p_var m) T.
Proof. intros.
       specialize(tc_sub m em (extendT empty m T) ((extendT empty m T')) (p_var m) T T); intro HH.
       apply HH.
       constructor. simpl.
       rewrite Nat.eqb_refl.
       
Fail Qed. *)

Lemma _a21: forall P Q m em T T' G,
  typ_proc m em G Q T' ->
  typ_proc (S m) em (extendT G m T') P T ->
  typ_proc m em G (subst_proc Q P) T.
Proof. intro P.
       induction P; intros.
       - admit.
       - admit.
       - simpl.
         inversion H0.
         + specialize(_a23_bA (S m) em s n e P p c t); intro HH.
           subst.
           specialize (HH H1 eq_refl).
           destruct HH as (S, (T'',(Ha, (Hb, Hc)))).
           assert(subsort S S) as HHSS by constructor.
           specialize(Hc S HHSS).
           specialize(stTrans  _ _ _ Hc H2); intro HT.
           specialize(tc_sub m em G G (p_send s n e (subst_proc Q P)) (ltt_send s [(n, S, T'')]) T); intro HS.
           apply HS.
           constructor.
           admit.
           apply IHP with (T' := T'). easy.
           specialize(tc_sub (Datatypes.S m) em c (extendT G m T') P T'' T''); intro HSs.
           apply HSs. easy. apply stRefl. easy.
           easy. apply refCtxT_refl.
         + subst. constructor.
           admit.
           apply IHP with (T' := T'). easy.
           easy. 
       - admit.
       - admit.
       - admit.
Admitted.






