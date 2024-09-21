From mathcomp Require Import all_ssreflect.
From SST Require Import src.expressions process.processes process.typecheck process.inversion type.global type.local type.isomorphism.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Lemma inv_expr_var : forall ex n Gs S,
  typ_expr Gs ex S -> ex = (e_var n) -> 
  exists S', onth n Gs = Some S' /\ subsort S' S.
Proof.
  intros. induction H; intros; try easy.
  - inversion H0. subst. exists t. split. easy. apply srefl.
  - specialize(IHtyp_expr H0); intros. destruct IHtyp_expr. destruct H2.
    exists x. split. easy. specialize(sstrans x s s' H3 H1); easy.
Qed.

Lemma inv_expr_vali : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_val n) -> ((exists k, S = sint /\ n = vint k) \/ (exists k, subsort snat S /\ n = vnat k) \/ (exists k, S = sbool /\ n = vbool k)).
Proof.
  intros. induction H; intros; try easy. inversion H0. subst.
  - left. exists i. easy. 
  - inversion H0. subst. right. left. exists i. split. apply srefl. easy.
  - inversion H0. subst. right. right. exists b. easy.
  specialize(IHtyp_expr H0); intros. 
  destruct IHtyp_expr. 
  - destruct H2. destruct H2. subst. 
    inversion H1. subst.
    left. exists x. easy.
  - subst. inversion H2. destruct H0. destruct H0. subst. inversion H0. subst.
    inversion H1. subst. right. left. exists x.
    split. apply sni. easy.
  - subst. inversion H1. subst. right. left. exists x. split. apply sni. easy.
    subst. right. left. exists x. easy.
  - inversion H0. destruct H3. subst.
    inversion H1. subst. right. right. exists x. easy.
Qed.
  
Lemma inv_expr_succ : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_succ n) -> typ_expr Gs n snat /\ (S = snat \/ S = sint). 
Proof.
  intros. induction H; intros; try easy. 
  - inversion H0. subst. split. easy. left. easy.
  - specialize(IHtyp_expr H0); intros.
    destruct IHtyp_expr. destruct H3.
    split. easy. inversion H1. subst. right. easy. subst. left. easy.
  - split. easy. subst. inversion H1. subst. right. easy.
Qed. 

Lemma inv_expr_neg : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_neg n) -> S = sint /\ typ_expr Gs n sint.
Proof.
  intros. induction H; try easy. 
  inversion H0. subst. easy.
  inversion H1. subst. 
  - specialize(IHtyp_expr (erefl (e_neg n))). destruct IHtyp_expr. easy.
  - subst. apply IHtyp_expr. easy.
Qed.

Lemma inv_expr_not : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_not n) -> S = sbool /\ typ_expr Gs n sbool.
Proof.
  intros. induction H; try easy.
  inversion H1. subst. 
  specialize(IHtyp_expr (erefl (e_not n))); easy.
  subst. apply IHtyp_expr. easy.
  inversion H0. subst. easy.
Qed.

Lemma inv_expr_gt : forall Gs ex S m n,
  typ_expr Gs ex S -> ex = (e_gt m n) -> S = sbool /\ typ_expr Gs m sint /\ typ_expr Gs n sint.
Proof.
  intros. induction H; try easy.
  - inversion H1; try easy. subst.
    specialize(IHtyp_expr (erefl (e_gt m n))); try easy.
    subst. apply IHtyp_expr; try easy.
  - inversion H0. subst. easy. 
Qed.

Lemma inv_expr_plus : forall Gs ex S m n,
  typ_expr Gs ex S -> ex = (e_plus m n) -> S = sint /\ typ_expr Gs m sint /\ typ_expr Gs n sint.
Proof.
  intros. induction H; try easy.
  - inversion H1; try easy. subst.
    specialize(IHtyp_expr (erefl (e_plus m n ))); try easy.
    subst. apply IHtyp_expr; try easy.
  - inversion H0. subst. try easy.
Qed.

Lemma inv_expr_det : forall Gs ex S m n,
  typ_expr Gs ex S -> ex = (e_det m n) -> exists k, typ_expr Gs m k /\ typ_expr Gs n k /\ subsort k S.
Proof.
  intros. induction H; try easy.
  specialize(IHtyp_expr H0). destruct IHtyp_expr. destruct H2. destruct H3.
  exists x. split; try easy. split; try easy.
  apply sstrans with (s2 := s); intros; try easy.
  exists s. inversion H0. subst. split; try easy. split. easy.
  apply srefl.
Qed.








