

Inductive Box : Type := 
  | Simple : Box
  | InBox : list Box -> Box.

Inductive Rel : relation Box := 
  | R_refl : forall B, Rel B B
  | R_box  : forall A B, List.Forall2 Rel A B -> Rel (InBox A) (InBox B).

Section Rel_ref.
  Variable P : Box -> Box -> Prop.
  Variable P_list : list Box -> list Box -> Prop.
  Variable P_nil : P_list [] [].
  Variable P_cons : forall t1 t2 l1 l2, P t1 t2 -> P_list l1 l2 -> P_list (t1 :: l1) (t2 :: l2).
  Variable P_refl : forall B, P B B.
  Variable P_box  : forall A B, P_list A B -> P (InBox A) (InBox B).
  
  Fixpoint Rel_ref (B1 B2 : Box) (a : Rel B1 B2) {struct a}: P B1 B2 :=
    let fix go_list (l1 l2 : list Box) (H : List.Forall2 Rel l1 l2) {struct H} : P_list l1 l2 :=
      match H with
        | Forall2_nil  =>  P_nil
        | @Forall2_cons _ _ _ x y xr yr H1 H2 => P_cons x y xr yr (Rel_ref x y H1) (go_list xr yr H2)
      end
    in 
    match a with
      | R_refl B    => P_refl B
      | R_box A B H => P_box A B (go_list A B H)
    end.

End Rel_ref.


Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Section Rel_ind_ref.
  Variable P : Box -> Box -> Prop.
  Variable P_refl : forall B, P B B.
  Variable P_box  : forall A B, Forall2 Rel A B -> Forall2 P A B -> P (InBox A) (InBox B).  
  
  Compute (List.Forall2_cons).
  Compute (List.Forall_cons).

  Fixpoint Rel_ind_ref (B1 B2 : Box) (a : Rel B1 B2) {struct a} : P B1 B2 := 
    match a with
    | R_refl B => P_refl B
    | R_box A B H => P_box A B H (Forall2_mono Rel_ind_ref _ _ H)
    end.
End Rel_ind_ref.
