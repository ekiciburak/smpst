From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection type.proj_sub.
Require Import String List Datatypes ZArith Relations PeanoNat.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Open Scope list_scope.
Import ListNotations.


CoFixpoint Ga : gtt := gtt_send "Alice" "Bob" [Some (snat, Ga)].

Example Grec : gttTC (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])) Ga.
Proof.
  pcofix CIH.
  pfold. apply gttT_rec with (Q := g_send "Alice" "Bob" [(Some (snat, (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)]))))]).
  constructor. constructor. right.
  exists snat. exists (g_var 0). exists (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])).
  split; try easy. split; try easy. constructor. easy.
  
  rewrite (gtt_eq Ga). simpl.
  left. pfold.
  constructor. constructor. right. exists snat. exists (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])). exists Ga.
  split; try easy. split; try easy.
  right. easy. easy.
Qed.
