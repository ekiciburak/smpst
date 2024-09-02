From Paco Require Import paco.
Require Import Setoid List.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

Inductive colistF (a : Type) (x : Type) :=
  | conil : colistF a x
  | cocons: a -> x -> colistF a x.

CoInductive coseq (a : Type) : Type :=
  Delay
  {
    force: colistF a (coseq a) 
  }.

Arguments force {_} _.
Arguments conil { _ _ } .
Arguments cocons { _ _ } _ _.
Arguments Delay {_} _.

CoInductive stream (a : Type) :=
  | conils : stream a
  | coconss: a -> stream a -> stream a.

Arguments conils { _ } .
Arguments coconss { _ } _ _.

Inductive optionF (a : Type) :=
  | none: optionF a
  | some: a -> optionF a.

CoInductive cooption (a : Type) : Type :=
  DelayO
  {
    forceO: optionF a
  }.

Arguments none {_}.
Arguments some {_} _.
Arguments DelayO {_} _.
Arguments cooption {_}.

Definition coseq_id {A: Type} (s: coseq A): coseq A :=
  Delay
  match force s with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Lemma coseq_eq: forall {A} s, s = @coseq_id A s.
Proof. intros A s.
       unfold coseq_id.
       destruct s.
       simpl.
       destruct force0; easy.
Qed.

Definition stream_id {A: Type} (s: stream A): stream A :=
  match s with
    | conils       => conils
    | coconss x xs => coconss x xs
  end.

Lemma stream_eq: forall {A} s, s = @stream_id A s.
Proof. intros A s.
       unfold stream_id.
       destruct s; easy.
Qed.

Fixpoint conth {A: Type} (s: coseq A) (n: nat): option A :=
  match n with
    | O   => 
      match force s with
        | conil       => None
        | cocons x xs => Some x
      end 
    | S k =>
      match force s with
        | conil       => None
        | cocons x xs => conth xs k
      end
  end.

CoFixpoint nats_from (n : nat) : coseq nat := 
  Delay (cocons n (nats_from (S n))).

CoFixpoint map {A B: Type} (f: A -> B) (xs: coseq A): coseq B := 
  Delay
  match force xs with
    | conil       => conil
    | cocons x xs => cocons (f x) (map f xs)
  end.

CoFixpoint appendC {A: Type} (l ys: coseq A): coseq A := 
  match force l with
    | conil       => ys
    | cocons x xs => Delay (cocons x (appendC xs ys))
  end.

CoFixpoint appendL {A: Type} (l: list A) (ys: coseq A): coseq A := 
  match l with
    | nil       => ys
    | cons x xs => Delay (cocons x (appendL xs ys))
  end.

Lemma anl: forall {A: Type} xs, @appendC A {| force := conil |} xs = xs.
Proof. intros.
       destruct xs. simpl.
       rewrite(coseq_eq(appendC {| force := conil |} {| force := force0 |})).
       unfold coseq_id. simpl.
       destruct force0; easy.
Qed.

Lemma anl2: forall {A: Type} xs, @appendL A nil xs = xs.
Proof. intros.
       destruct xs. simpl.
       simpl.
       rewrite(coseq_eq(appendL nil {| force := force0 |})).
       unfold coseq_id. simpl.
       destruct force0; easy.
Qed.

Lemma app_assoc: forall {A: Type} xs ys zs,
  @appendL A xs (appendL ys zs) = appendL (xs ++ ys) zs.
Proof. intros A xs.
       induction xs; intros.
       simpl. rewrite anl2. easy.
       simpl.
       rewrite(coseq_eq(appendL (a :: xs) (appendL ys zs))).
       unfold coseq_id. simpl.
       rewrite IHxs.
       rewrite(coseq_eq(appendL (a :: xs ++ ys) zs)).
       unfold coseq_id. simpl. easy.
Qed.

(* unsound coinductive membership check *)
Inductive coseqInC {A: Type} (R: A -> coseq A -> Prop): A -> coseq A -> Prop :=
  | CoInSplit1A x xs {ys}: force xs = cocons x ys -> coseqInC R x xs 
  | CoInSplit2A x xs y ys: force xs = cocons y ys -> x <> y -> R x ys -> coseqInC R x xs.

Definition coseqCoIn {A}:= paco2 (@coseqInC A) bot2.

Lemma coseqCoIn_mon: forall {A: Type}, monotone2 (@coseqInC A).

Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - specialize(@CoInSplit1A A r' x xs ys H); intro Ha. apply Ha.
       - specialize(@CoInSplit2A A r' x xs y ys H H0); intro Ha.
         apply Ha, LE, H1.
Qed.

CoFixpoint cA {A: Type} (a: A): coseq A := Delay (cocons a (cA a)).

Lemma unsound_coseqCoIn: forall A (a b: A), a <> b -> coseqCoIn b (cA a).
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(cA a)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (cA a)). simpl. easy. easy.
       right. easy.
Qed.
(**)


