

(* 
Example simple_mu : process := 
  p_rec 0 (p_send "Alice" 1 (e_val (vnat 100)) (p_var 0)).
  
Example Pcomplex_mu : process := 
  p_rec 0 (p_recv "Alice" [
    (0, p_var 0);
    (1, p_rec 1 (p_recv "Bob" [
       (3, p_var 0);
       (4, p_var 1);
       (5, p_inact)
    ]));
    (2, p_inact)
  ]).
  

CoFixpoint Tcomplex_mu : ltt := 
  ltt_recv "Alice" [
    (0, sbool, Tcomplex_mu);
    (1, sbool, complex_mu_1);
    (2, sbool, ltt_end)
  ]
  with complex_mu_1 : ltt :=
    ltt_recv "Bob" [(3, sbool, Tcomplex_mu); (4, sbool, complex_mu_1); (5, sbool, ltt_end)].

Example recursive_mu : process :=
  p_rec 0 (p_send "A" 0 (e_val (vnat 1)) (
    p_rec 1 (p_recv "B" [
      (1, p_var 0); 
      (2, p_send "C" 2 (e_val (vnat 2)) (p_var 1))
    ])
  )).
  
Example subst_mu : process := 
  p_rec 0 (p_recv "Alice" [
    (0, p_var 0);
    (1, p_recv "Bob" [
       (3, p_var 0);
       (4, p_var 15);
       (5, p_var 16);
       (6, p_rec 2 p_inact)
    ]);
    (2, p_inact)
  ]).
   *)
(* 
Fixpoint fv (P : process) : list fin := 
  match P with
    | p_var x => [x]
    | p_send p l e P' => fv P'
    | p_recv p lis => 
       let fix next xs :=
         match xs with 
          | (_,p)::ys => (fv p) ++ next ys
          | _ => []
         end
       in next lis 
    | p_ite e p q => (fv p) ++ (fv q)
    | p_rec n p => 
      let fix fil k xs :=
        match xs with
          | x::ys => if Nat.eqb x k then fil k ys else x::(fil k ys)
          | _ => []
        end
      in fil n (fv p)
    | _ => []
   end.
    *)
    
    
    
(* 
Definition fresh_from_list (lis : list fin) : fin :=
  match lis with 
    | [] => 0
    | _ => 
      let fix max_lis xs :=
        match xs with
          | x::ys => max x (max_lis ys)
          | _ => 0
        end
      in 1 + (max_lis lis)
    end.

Definition fresh (lis : list process) : fin := 
  let fix max_lis xs :=
    match xs with
      | x::ys => max x (max_lis ys)
      | _ => 0
    end
  in max_lis (list_map (fun x => (fresh_from_list (vars x))) lis). *)
  
  
(* Takes outermost p_rec and renames that and all variables binded to it to a fresh one*)
Definition rename_fresh (P : process) (avoid : list fin) : process := 
  match P with 
    | p_rec x P' => 
        let fre := max (fresh [P']) (fresh_from_list avoid)
        in p_rec fre (rename_force x fre P') 
    | _ => P
  end.


Compute rename_fresh recursive_mu [2;3;4].

(* when fresh variables are generated, overrides previous mappings of that variable (effectively deletes them, acknowledging different binder)*)
Definition rename_pseudo_bruijn (P : process) (avoid : list fin) : process := 
  let fix ren p av mp := 
    match p with
      | p_var x => 
          let fix maps_using xs x := 
            match xs with 
              | (from,to)::ys => if Nat.eqb from x then to else maps_using ys x
              | [] => x
            end 
          in p_var (maps_using mp x)
      | p_send p l e P' => p_send p l e (ren P' av mp)
      | p_recv p lis => p_recv p (list_map (prod_map (fun x => x) (fun x => ren x av mp)) lis)
      | p_ite e p1 p2 => p_ite e (ren p1 av mp) (ren p2 av mp)
      | p_rec x P' => 
          let fre := fresh_from_list av
          in p_rec fre (ren P' (fre::av) ((x,fre)::mp))
      | _ => p
    end
  in ren P (avoid ++ (fv P)) [].
 

Compute rename_pseudo_bruijn recursive_mu [].
Compute recursive_mu.

Definition expr_eq_dec : forall (x y : expr), { x = y } + { x <> y }.
Proof.
decide equality.
decide equality.
decide equality. decide equality. decide equality. decide equality. decide equality. decide equality. decide equality.
Defined.

Definition balpha_equiv (P : process) (Q : process) : bool :=
  let fix syntax_eq P1 P2 :=
    match P1 with 
    | p_var x =>
        match P2 with 
          | p_var y => (Nat.eqb x y)
          | _ => false
        end
    | p_inact =>
        match P2 with
          | p_inact => true 
          | _ => false
        end 
    | p_send p l e P' =>
        match P2 with
          | p_send q l' e' Q' => (eqb p q) && (Nat.eqb l l') && (expr_eq_dec e e') && (syntax_eq P' Q')
          | _ => false 
        end
    | p_recv p lis =>
        match P2 with
          | p_recv q lis' => 
            let fix all_true xs ys := 
              match xs with
                | (l,p')::xs' => 
                  match ys with 
                    | [] => false 
                    | (l',q')::ys' => (Nat.eqb l l') && (syntax_eq p' q') && (all_true xs' ys')
                  end
                | [] => 
                  match ys with
                    | [] => true
                    | _ => false
                  end
              end
            in (eqb p q) && (all_true lis lis')
          | _ => false
        end
    | p_ite e p1 p2 =>
        match P2 with 
          | p_ite e' q1 q2 => (expr_eq_dec e e') && (syntax_eq p1 q1) && (syntax_eq p2 q2)
          | _ => false 
        end
    | p_rec x P' =>
        match P2 with 
          | p_rec y Q' => if Nat.eqb x y then syntax_eq P' Q' else false
          | _ => false 
        end
   end
  in syntax_eq (rename_pseudo_bruijn P (fv P ++ fv Q)) (rename_pseudo_bruijn Q (fv P ++ fv Q)). *)
  
  (* 
Definition al1 := p_rec 0 (p_rec 1 (p_recv "Alice " [(1, p_var 0); (2, p_var 1)])).
Definition al2 := p_rec 1 (p_rec 0 (p_recv "Alice " [(1, p_var 1); (2, p_var 0)])).
Definition al3 := p_rec 20 (p_rec 13 (p_recv "Alice " [(1, p_var 20); (2, p_var 13)])).
Definition al4 := p_rec 0 (p_rec 1 (p_recv "Alice " [(1, p_var 1); (2, p_var 1)])).

Compute balpha_equiv al1 al2.
Compute balpha_equiv al1 al4.
Compute rename_pseudo_bruijn (p_rec 20 (p_rec 13 (p_var 20))) [].

(* Example t : 2 <> 3.
Proof.
  simpl. easy. *)
(*
Lemma stronger_multi {X : Type} (R : relation X) : forall (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros x y z.
   *)
  

Example al1_al3 : alpha_multistep al1 al3. 
Proof.
  unfold al1, al3.
  unfold alpha_multistep.
  apply multi_step with 
  (y := (p_rec 20 (p_rec 1 (p_recv "Alice " [(1, p_var 20); (2, p_var 1)])))).
  apply a_recl. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename. unfold rename_force. simpl. easy.
  
  apply multi_step with 
  (y := (p_rec 20 (p_rec 13 (p_recv "Alice " [(1, p_var 20); (2, p_var 13)])))).
  apply a_rec2. apply a_recl. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename; unfold rename_force. simpl. easy.
  
  apply multi_refl.
  
Qed.

Example al3_al2 : alpha_multistep al3 al2. 
Proof.
  unfold al3, al2.
  unfold alpha_multistep.
  apply multi_step with 
  (y := (p_rec 1 (p_rec 13 (p_recv "Alice " [(1, p_var 1); (2, p_var 13)])))).
  apply a_recl. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename. unfold rename_force. simpl. easy.
  
  apply multi_step with 
  (y := (p_rec 1 (p_rec 0 (p_recv "Alice " [(1, p_var 1); (2, p_var 0)])))).
  apply a_rec2. apply a_recl. 
  - unfold fresh_in. simpl. easy.
  - unfold p_rename; unfold rename_force. simpl. easy.
  
  apply multi_refl.
  
Qed.
 *)
  
  
  (* 
Example al1_al2 : alpha_multistep al1 al2.
Proof. 
  unfold al1, al2.
  apply transitive_multi with 
  (y := al3).
  apply al1_al3.
  apply al3_al2.
Qed. *)