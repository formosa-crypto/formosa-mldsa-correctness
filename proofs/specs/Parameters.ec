require import AllCore IntDiv List Ring.
require DParams.

abbrev q : int = 8380417.
abbrev n : int = 256.
axiom prime_q : prime q.
abbrev d : int = 13.
op tau : int.                (*    39             49           60      : exact number of 1s in c *)
op lambda : int.             (*   128            192          256      : collision strength of ctilde *)
op gamma1 : int.             (*   2^17           2^19         2^19     : coefficient range of y*)
op gamma2 : int.             (* (q-1)%/88     (q-1)%/32    (q-1)%/32   : low order rounding range *)
(* We have k x l matrices *)
op kvec : int.               (*    4              6             8      : number of rows of A *) 
op lvec : int.               (*    4              5             7      : number of columns of A *)
op Eta : int.                (*    2              4             2      : private key range *)
op Beta : int = tau * Eta.   (*   78             196           120     *)
op w_hint : int.             (*   80              55            75     : max number of 1s in the hint *)
op kappa_max : int.          (* abstract bound on rejection sampling iterations *)

axiom param_sets : 
   (tau,lambda,gamma1,gamma2,kvec,lvec,Eta,w_hint) \in [ (* (39,128,2^17,(q-1)%/88,4,4,2,80); ub_d Fails! *)
                                                  (49,192,2^19,(q-1)%/32,6,5,4,55);
                                                  (60,256,2^19,(q-1)%/32,8,7,2,75)
                                                ].

clone import DParams as MLDSAParams with
  op q <- q,
  op n <- n,
  op eta_ <- Eta,
  op k <- kvec,
  op l <- lvec,
  op gamma1 <- gamma1,
  op gamma2 <- gamma2,
  op beta_ <- Beta,
  op tau <- tau,
  op d <- d
  proof prime_q by exact prime_q
  proof gt0_n by auto
  proof gt0_eta by smt(param_sets)
  proof gt0_k  by smt(param_sets)
  proof gt0_l  by smt(param_sets)
  proof gt0_beta  by smt(param_sets)
  proof tau_bound by smt(param_sets)
  proof  gt0_d by auto
  proof eta_tau_leq_b by smt(param_sets)
  proof gamma2_bound by smt(param_sets)
  proof gamma2_div by smt(param_sets)
  proof beta_gamma2_lt by smt(param_sets)
  proof *.

realize ub_d 
by have  H /=:=param_sets;elim H => /=;rewrite /q /d /=;
  move => [#] ->?? -> * /=;do 12!(rewrite expr_pred //=);rewrite expr1 => /=.

realize beta_gamma1_lt
by rewrite /Beta;
 have  H /=:=param_sets;elim H => /=;rewrite /q /d /=;
  move => [#] ->?->??? -> * /=;do 18!(rewrite expr_pred //=);rewrite expr1 => /=. 
