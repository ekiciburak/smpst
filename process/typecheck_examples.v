From SST Require Import aux.unscoped aux.expressions process.processes process.typecheck type.global tree.global tree.local.
Require Import List String Datatypes ZArith Relations.
Open Scope list_scope.
From mathcomp Require Import ssreflect.seq.
Import ListNotations.
From Paco Require Import paco.

Definition PBob: process := p_recv "Alice" [1; 4] [p_send "Carol" 2 (e_val (vnat 100)) p_inact; p_send "Carol" 2 (e_val (vnat 2)) p_inact].

Definition TBob: ltt := ltt_recv "Alice" [(1, (snat, ltt_send "Carol" [(2, (snat, ltt_end))]));
                                          (4, (snat, ltt_send "Carol" [(2, (snat, ltt_end))]))].

Example _317_b: typ_proc [] [] PBob TBob.
Proof. unfold PBob, TBob.
  specialize(tc_recv [] [] "Alice" [1; 4] [snat; snat]
        [p_send "Carol" 2 (e_val (vnat 100)) p_inact; p_send "Carol" 2 (e_val (vnat 2)) p_inact]
        [ltt_send "Carol" [(2, (snat, ltt_end))]; ltt_send "Carol" [(2, (snat, ltt_end))]]
  ); intros.
  simpl in H. apply H; try easy. clear H.
  apply sort2; try easy. repeat constructor.
  apply sort1; try easy. clear H.
  apply Forall2_cons.
  repeat constructor.
  apply Forall2_cons.
  repeat constructor.
  easy.
Qed.

Definition PG_agency : process := p_rec (p_recv "Customer" [0; 7] [p_send "Customer" 1 (e_val (vnat 5000)) (p_recv "Customer" [2; 5; 6] [
  (p_recv "Customer" [3] [(p_send "Customer" 4 (e_val (vnat 25122019)) p_inact)]);
  (p_var 0);
  (p_inact)]);
        p_send "Customer" 1 (e_val (vnat 1000)) (p_recv "Customer" [2; 5; 6] [
  (p_recv "Customer" [3] [(p_send "Customer" 4 (e_val (vnat 25122019)) p_inact)]);
  (p_var 0);
  (p_inact)])
  ]).

CoFixpoint TG_agency : ltt := ltt_recv "Customer" [(0, (sbool, ltt_send "Customer" [(1, (snat, ltt_recv "Customer" [
  (2, (sbool, ltt_recv "Customer" [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
  (5, (sbool, TG_agency));
  (6, (sbool, ltt_end))]))]));  
                                                   (7, (sbool, ltt_send "Customer" [(1, (snat, ltt_recv "Customer" [
  (2, (sbool, ltt_recv "Customer" [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
  (5, (sbool, TG_agency));
  (6, (sbool, ltt_end))]))]))].

Example _vgi_agency_ : typ_proc [] [] PG_agency TG_agency.
Proof. unfold PG_agency.
  rewrite(ltt_eq TG_agency). simpl.
  apply tc_mu with (t := (ltt_recv "Customer"
     [(0,
       (sbool,
        ltt_send "Customer"
          [(1,
            (snat,
             ltt_recv "Customer"
               [(2,
                 (sbool,
                  ltt_recv "Customer"
                    [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]));
      (7,
       (sbool,
        ltt_send "Customer"
          [(1,
            (snat,
             ltt_recv "Customer"
               [(2,
                 (sbool,
                  ltt_recv "Customer"
                    [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))])); try easy.
  specialize(tc_recv [] [Some
     (ltt_recv "Customer"
        [(0,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]));
         (7,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))])] "Customer" [0; 7] [sbool; sbool]
     [p_send "Customer" 1 (e_val (vnat 5000))
        (p_recv "Customer" [2; 5; 6]
           [p_recv "Customer" [3]
              [p_send "Customer" 4
                 (e_val
                    (vnat
                       (Init.Nat.of_uint
                          (Decimal.D2
                             (Decimal.D5
                                (Decimal.D1
                                   (Decimal.D2
                                      (Decimal.D2
                                         (Decimal.D0
                                            (Decimal.D1
                                               (Decimal.D9 Decimal.Nil)))))))))))
                 p_inact]; p_var 0; p_inact]);
      p_send "Customer" 1 (e_val (vnat 1000))
        (p_recv "Customer" [2; 5; 6]
           [p_recv "Customer" [3]
              [p_send "Customer" 4
                 (e_val
                    (vnat
                       (Init.Nat.of_uint
                          (Decimal.D2
                             (Decimal.D5
                                (Decimal.D1
                                   (Decimal.D2
                                      (Decimal.D2
                                         (Decimal.D0
                                            (Decimal.D1
                                               (Decimal.D9 Decimal.Nil)))))))))))
                 p_inact]; p_var 0; p_inact])] 
      [ltt_send "Customer"
          [(1,
            (snat,
             ltt_recv "Customer"
               [(2,
                 (sbool,
                  ltt_recv "Customer"
                    [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))];
        ltt_send "Customer"
          [(1,
            (snat,
             ltt_recv "Customer"
               [(2,
                 (sbool,
                  ltt_recv "Customer"
                    [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]]); intros. 
  simpl in *. apply H; try easy.
  apply sort2; try easy. repeat constructor. apply sort1; try easy. clear H.
  apply Forall2_cons. repeat constructor.
  specialize(tc_recv [Some
     (fst
        (sbool,
         ltt_send "Customer"
           [(1,
             (snat,
              ltt_recv "Customer"
                [(2,
                  (sbool,
                   ltt_recv "Customer"
                     [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                 (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))]
  [Some
     (ltt_recv "Customer"
        [(0,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]));
         (7,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))])] "Customer" [2; 5; 6] [sbool; sbool; sbool]
     [p_recv "Customer" [3]
        [p_send "Customer" 4
           (e_val
              (vnat
                 (Init.Nat.of_uint
                    (Decimal.D2
                       (Decimal.D5
                          (Decimal.D1
                             (Decimal.D2
                                (Decimal.D2
                                   (Decimal.D0
                                      (Decimal.D1 (Decimal.D9 Decimal.Nil)))))))))))
           p_inact]; p_var 0; p_inact] [
        ltt_recv "Customer"
          [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))];
      TG_agency; ltt_end]); intros.
  apply H; try easy. 
  repeat (apply sort2; repeat constructor). clear H.
  apply Forall2_cons. 
  specialize(tc_recv [Some
     (fst
        (sbool,
         ltt_recv "Customer"
           [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
   Some
     (fst
        (sbool,
         ltt_send "Customer"
           [(1,
             (snat,
              ltt_recv "Customer"
                [(2,
                  (sbool,
                   ltt_recv "Customer"
                     [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                 (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))]
  [Some
     (ltt_recv "Customer"
        [(0,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]));
         (7,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))])] "Customer" [3] [snat]
     [p_send "Customer" 4
        (e_val
           (vnat
              (Init.Nat.of_uint
                 (Decimal.D2
                    (Decimal.D5
                       (Decimal.D1
                          (Decimal.D2
                             (Decimal.D2
                                (Decimal.D0
                                   (Decimal.D1 (Decimal.D9 Decimal.Nil)))))))))))
        p_inact] [ltt_send "Customer" [(4, (snat, ltt_end))]]); intros.
  apply H; try easy.
  repeat (apply sort2; repeat constructor). apply sort1. clear H. 
  repeat constructor.
  repeat constructor. simpl.
  rewrite(ltt_eq TG_agency) at 1. simpl. easy.
  repeat constructor.
  specialize(tc_recv [Some
     (fst
        (sbool,
         ltt_send "Customer"
           [(1,
             (snat,
              ltt_recv "Customer"
                [(2,
                  (sbool,
                   ltt_recv "Customer"
                     [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                 (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))]
  [Some
     (ltt_recv "Customer"
        [(0,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]));
         (7,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))])] "Customer" [2; 5; 6] [sbool; sbool; sbool] 
     [p_recv "Customer" [3]
        [p_send "Customer" 4
           (e_val
              (vnat
                 (Init.Nat.of_uint
                    (Decimal.D2
                       (Decimal.D5
                          (Decimal.D1
                             (Decimal.D2
                                (Decimal.D2
                                   (Decimal.D0
                                      (Decimal.D1 (Decimal.D9 Decimal.Nil)))))))))))
           p_inact]; p_var 0; p_inact] [ltt_recv "Customer"
          [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]; TG_agency; ltt_end]); intros.
  apply H; try easy; clear H.
  repeat (apply sort2; repeat constructor).
  repeat constructor.
  specialize(tc_recv [Some
     (fst
        (sbool,
         ltt_recv "Customer"
           [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
   Some
     (fst
        (sbool,
         ltt_send "Customer"
           [(1,
             (snat,
              ltt_recv "Customer"
                [(2,
                  (sbool,
                   ltt_recv "Customer"
                     [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                 (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))]
  [Some
     (ltt_recv "Customer"
        [(0,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]));
         (7,
          (sbool,
           ltt_send "Customer"
             [(1,
               (snat,
                ltt_recv "Customer"
                  [(2,
                    (sbool,
                     ltt_recv "Customer"
                       [(3, (snat, ltt_send "Customer" [(4, (snat, ltt_end))]))]));
                   (5, (sbool, TG_agency)); (6, (sbool, ltt_end))]))]))])] "Customer" [3] [snat]
    [p_send "Customer" 4
        (e_val
           (vnat
              (Init.Nat.of_uint
                 (Decimal.D2
                    (Decimal.D5
                       (Decimal.D1
                          (Decimal.D2
                             (Decimal.D2
                                (Decimal.D0
                                   (Decimal.D1 (Decimal.D9 Decimal.Nil)))))))))))
        p_inact] [ltt_send "Customer" [(4, (snat, ltt_end))]]); intros.
  apply H; try easy; clear H. apply sort1.
  repeat constructor.
  simpl.
  rewrite(ltt_eq TG_agency) at 1. simpl. easy.
Qed. 






