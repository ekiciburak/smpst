From SST Require Import src.header. 
Require Import List String ZArith.
Notation fin := nat.

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

