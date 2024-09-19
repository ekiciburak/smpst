Require Import List String ZArith.
From SST Require Import src.unscoped.

Variant value: Type :=
  | vint : Z    -> value
  | vbool: bool -> value
  | vunit: unit -> value
  | vnat : nat -> value.


Inductive sort: Type :=
  | sunit: sort
  | sbool: sort
  | sint : sort
  | snat : sort.

Inductive subsort: sort -> sort -> Prop :=
  | sni  : subsort snat sint
  | srefl: forall s, subsort s s.

Lemma sstrans: forall s1 s2 s3, subsort s1 s2 -> subsort s2 s3 -> subsort s1 s3.
Proof. intros.
       induction H.
       inversion H0. subst. constructor.
       easy.
Qed.

Inductive nsubsort: sort -> sort -> Prop :=
  | nsin: nsubsort sint snat
  | nsbi: nsubsort sbool sint
  | nsib: nsubsort sint sbool
  | nsbn: nsubsort sbool snat
  | nsnb: nsubsort snat sbool
  | nsun: nsubsort sunit snat
  | nsnu: nsubsort snat sunit
  | nsbu: nsubsort sbool sunit
  | nsub: nsubsort sunit sbool
  | nsui: nsubsort sunit sint
  | nsiu: nsubsort sint sunit.

Lemma sort_dec: forall s s', subsort s s' \/ nsubsort s s'.
Proof. intro s.
       induction s; intros.
       case_eq s'; intros.
       left. apply srefl.
       right. apply nsub.
       right. apply nsui.
       right. apply nsun.
       case_eq s'; intros.
       right. apply nsbu.
       left. apply srefl.
       right. apply nsbi.
       right. apply nsbn.
       case_eq s'; intros.
       right. apply nsiu.
       right. apply nsib.
       left. apply srefl.
       right. apply nsin.
       case_eq s'; intros.
       right. apply nsnu.
       right. apply nsnb.
       left. apply sni.
       left. apply srefl.
Qed.

Lemma ssnssL: forall s t, subsort s t -> (nsubsort s t -> False).
Proof. intro s.
       induction s; intros; case_eq t; intros; subst; try easy.
Qed.

Lemma ssnssR: forall s t, nsubsort s t -> (subsort s t -> False).
Proof. intro s.
       induction s; intros; case_eq t; intros; subst; try easy.
Qed.

Definition sort_eq (gs1 gs2: sort): bool :=
  match pair gs1 gs2 with
    | pair sint sint   => true
    | pair sbool sbool => true
    | pair sunit sunit => true
    | pair snat snat   => true
    | _                => false 
  end.

Section expr.
Inductive expr  : Type :=
  | e_var : ( fin ) -> expr 
  | e_val : ( value   ) -> expr 
  | e_succ : ( expr   ) -> expr 
  | e_neg : ( expr   ) -> expr 
  | e_not : ( expr   ) -> expr 
  | e_gt : ( expr   ) -> ( expr   ) -> expr
  | e_plus: ( expr   ) -> ( expr   ) -> expr
  | e_det : expr -> expr -> expr.


End expr.

