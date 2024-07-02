From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.


Definition PG_agency : process := p_rec (p_recv "Customer" [(0, sbool, p_send "Customer" 1 (e_val (vnat 5000)) (p_recv "Customer" [
  (2, sbool, p_recv "Customer" [(3, snat, (p_send "Customer" 4 (e_val (vnat 25122019)) p_inact))]);
  (5, sbool, p_rec (p_var 0));
  (6, sbool, p_inact)]));
        (7, sbool, p_send "Customer" 1 (e_val (vnat 1000)) (p_recv "Customer" [
  (2, sbool, p_recv "Customer" [(3, snat, (p_send "Customer" 4 (e_val (vnat 25122019)) p_inact))]);
  (5, sbool, p_rec (p_var 0));
  (6, sbool, p_inact)]))
  ]).

CoFixpoint TG_agency : ltt := ltt_recv "Customer" [(0, sbool, ltt_send "Customer" [(1, snat, ltt_recv "Customer" [
  (2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
  (5, sbool, TG_agency);
  (6, sbool, ltt_end)])]);  
        (7, sbool, ltt_send "Customer" [(1, snat, ltt_recv "Customer" [
  (2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
  (5, sbool, TG_agency);
  (6, sbool, ltt_end)])])].

Example _vgi_agency_ : typ_proc 0 0 empty PG_agency TG_agency.
Proof. unfold PG_agency.
  rewrite(ltt_eq TG_agency). simpl.
  constructor.
  
  specialize(tc_recv 1 0 (extendT empty 0
  (ltt_recv "Customer" [
    (0, sbool,
      ltt_send "Customer" [(1, snat,
      ltt_recv "Customer" [(2, sbool,
      ltt_recv "Customer" [(3, snat,
      ltt_send "Customer" [(4, snat, ltt_end)])]);
      (5, sbool, TG_agency); (6, sbool, ltt_end)])]);
    (7, sbool,
      ltt_send "Customer" [(1, snat,
      ltt_recv "Customer" [(2, sbool,
      ltt_recv "Customer" [(3, snat,
      ltt_send "Customer" [(4, snat, ltt_end)])]);
      (5, sbool, TG_agency); (6, sbool, ltt_end)])])])
  ) "Customer"
  [0; 7] 
  [sbool; sbool]
  [p_send "Customer" 1 (e_val (vnat 5000)) (
    p_recv "Customer" [(2, sbool, 
    p_recv "Customer" [(3, snat, (
    p_send "Customer" 4 (e_val (vnat 25122019)) p_inact))]);
    (5, sbool, p_rec (p_var 0));
    (6, sbool, p_inact)]);
  p_send "Customer" 1 (e_val (vnat 1000)) (
    p_recv "Customer" [(2, sbool, 
    p_recv "Customer" [(3, snat, (
    p_send "Customer" 4 (e_val (vnat 25122019)) p_inact))]);
    (5, sbool, p_rec (p_var 0));
    (6, sbool, p_inact)])
  ]
  [ltt_send "Customer" [(1, snat, ltt_recv "Customer" [
  (2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
  (5, sbool, TG_agency);
  (6, sbool, ltt_end)])];
  ltt_send "Customer" [(1, snat, ltt_recv "Customer" [
  (2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
  (5, sbool, TG_agency);
  (6, sbool, ltt_end)])]]
  ); intro HR.
  simpl in HR.
  apply HR. clear HR. try easy. clear HR. 
  try easy. clear HR. try easy. clear HR.
  apply Forall_forall.
  intros (s, (p, l)) HI0.
  simpl in HI0.
  destruct HI0 as [HI0 | HI1].
  inversion HI0. simpl.
  subst.
  constructor.
  constructor.
  specialize(tc_recv 1 1 (extendS
     (extendT empty 0
        (ltt_recv "Customer"
           [(0, sbool,
             ltt_send "Customer"
               [(1, snat,
                 ltt_recv "Customer"
                   [(2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                    (5, sbool, TG_agency); (6, sbool, ltt_end)])]);
            (7, sbool,
             ltt_send "Customer"
               [(1, snat,
                 ltt_recv "Customer"
                   [(2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                    (5, sbool, TG_agency); (6, sbool, ltt_end)])])])) 0 sbool) "Customer"
      [2; 5; 6]
      [sbool; sbool; sbool]
      [
        p_recv "Customer" [(3, snat, p_send "Customer" 4 (e_val (vnat 25122019)) p_inact)];
        p_rec (p_var 0);
        p_inact
      ]
      [
        ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])];
        TG_agency;
        ltt_end
      ]
   ); intro HR. simpl in HR.
  apply HR. try easy. try easy. try easy. clear HR. 
  apply Forall_forall.
  intros (s, (p, l)) HI1. simpl in HI1.
  destruct HI1 as [HI1 | HI2].
  inversion HI1. simpl. subst.
  specialize(tc_recv 1 2 (extendS
     (extendS
        (extendT empty 0
           (ltt_recv "Customer"
              [(0, sbool,
                ltt_send "Customer"
                  [(1, snat,
                    ltt_recv "Customer"
                      [(2, sbool,
                        ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                       (5, sbool, TG_agency); (6, sbool, ltt_end)])]);
               (7, sbool,
                ltt_send "Customer"
                  [(1, snat,
                    ltt_recv "Customer"
                      [(2, sbool,
                        ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                       (5, sbool, TG_agency); (6, sbool, ltt_end)])])])) 0 sbool) 1 sbool) "Customer"
        [3] [snat] [p_send "Customer" 4 (e_val (vnat 25122019)) p_inact] [ltt_send "Customer" [(4, snat, ltt_end)]]
  ); intro HR. simpl in HR. apply HR.
  try easy. try easy. try easy. simpl. clear HR. 
  apply Forall_forall.
  intros (s, (p, l)) HI2. simpl in HI2.
  destruct HI2 as [HI2 | HI3].
  inversion HI2. simpl. subst.
  constructor.
  constructor. constructor.
  simpl.
  inversion HI3.
  destruct HI2 as [HI2 | HI3].
  inversion HI2. subst.
  constructor. constructor. simpl.
  rewrite (ltt_eq TG_agency) at 1. simpl. try easy.
  destruct HI3 as [HI3 | HI4].
  inversion HI3. subst. 
  constructor.
  inversion HI4.
  destruct HI1 as [HI1 | HI2].
  inversion HI1. simpl. subst.
  constructor. constructor. 
  specialize(tc_recv 1 1 (extendS
     (extendT empty 0
        (ltt_recv "Customer"
           [(0, sbool,
             ltt_send "Customer"  
               [(1, snat,
                 ltt_recv "Customer"
                   [(2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                    (5, sbool, TG_agency); (6, sbool, ltt_end)])]);
            (7, sbool,
             ltt_send "Customer"
               [(1, snat,
                 ltt_recv "Customer"
                   [(2, sbool, ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                    (5, sbool, TG_agency); (6, sbool, ltt_end)])])])) 0 sbool) "Customer"
      [2; 5; 6]
      [sbool; sbool; sbool]
      [
        p_recv "Customer" [(3, snat, p_send "Customer" 4 (e_val (vnat 25122019)) p_inact)];
        p_rec (p_var 0);
        p_inact
      ]
      [
        ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])];
        TG_agency;
        ltt_end
      ]
   ); intro HR. simpl in HR.
  apply HR. try easy. try easy. try easy. clear HR.
  apply Forall_forall.
  intros (s, (p, l)) HI4. simpl in HI4.
  destruct HI4 as [HI4 | HI5].
  inversion HI4. simpl. subst.
  specialize(tc_recv 1 2 (extendS
     (extendS
        (extendT empty 0
           (ltt_recv "Customer"
              [(0, sbool,
                ltt_send "Customer"
                  [(1, snat,
                    ltt_recv "Customer"
                      [(2, sbool,
                        ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                       (5, sbool, TG_agency); (6, sbool, ltt_end)])]);
               (7, sbool,
                ltt_send "Customer"
                  [(1, snat,
                    ltt_recv "Customer"
                      [(2, sbool,
                        ltt_recv "Customer" [(3, snat, ltt_send "Customer" [(4, snat, ltt_end)])]);
                       (5, sbool, TG_agency); (6, sbool, ltt_end)])])])) 0 sbool) 1 sbool) "Customer"
        [3] [snat] [p_send "Customer" 4 (e_val (vnat 25122019)) p_inact] [ltt_send "Customer" [(4, snat, ltt_end)]]
  ); intro HR. simpl in HR. apply HR.
  try easy. try easy. try easy. simpl. clear HR. 
  apply Forall_forall.
  intros (s, (p, l)) HI5. simpl in HI5.
  destruct HI5 as [HI5 | HI6].
  inversion HI5. simpl. subst.
  constructor.
  constructor. constructor.
  simpl.
  inversion HI6.
  destruct HI5 as [HI5 | HI6].
  inversion HI5. simpl. subst. 
  constructor. constructor. simpl. 
  rewrite (ltt_eq TG_agency) at 1. simpl. try easy.
  destruct HI6 as [HI6 | HI7].
  inversion HI6. subst. simpl. constructor.
  inversion HI7. inversion HI2.

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


Definition PTestmu : process := p_rec (p_recv "A" [(0, sbool, p_inact)]).
Definition TTestmu : ltt := ltt_recv "A" [(0, sbool, ltt_end)].

Example _testmu_1 : typ_proc 0 0 empty PTestmu TTestmu.
Proof. 
  unfold PTestmu, TTestmu.
  specialize(tc_mu 0 0 empty (p_recv "A" [(0, sbool, p_inact)]) (ltt_recv "A" [(0, sbool, ltt_end)])). intro HR.
  apply HR. clear HR.
  specialize(tc_recv 1 0 (extendT empty 0 (ltt_recv "A" [(0, sbool, ltt_end)])) "A"
    [0] [sbool] [p_inact] [ltt_end]
  ); intro HR.
  simpl in HR. simpl. apply HR. clear HR. 
  try easy. clear HR. 
  try easy. clear HR.
  try easy. clear HR.
  apply Forall_forall.
  intros (s, (p, l)) HIn.
  simpl in HIn. 
  destruct HIn as [HIn | HIn].
  simpl. inversion HIn. 
  constructor.
  simpl. inversion HIn.
Qed.



  
Example pr3 : process := p_rec (p_recv "Alice" [
  (0, sbool, p_var 0);
  (1, sbool, p_rec (p_recv "Bob" [
    (2, sbool, p_var 0);
    (3, sbool, p_var 1);
    (4, sbool, p_inact)
    ]))
  ]).
  





