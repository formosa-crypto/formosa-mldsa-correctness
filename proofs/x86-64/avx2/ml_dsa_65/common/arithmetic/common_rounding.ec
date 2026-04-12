require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import CDR Round Zq.

require import Array256.

(* ================================================================== *)
(* polynomial____make_hint                                              *)
(* For each coefficient i:                                             *)
(*   hints[i] = MakeHint(low_coefficients[i], high_coefficients[i])   *)
(*            = 1 if HighBits(low+high) != HighBits(high), else 0     *)
(* Also returns the total weight (count of 1s).                        *)
(* Spec connection (via poly_MakeHint from Rq.ec):                     *)
(*   liftu_wpoly res.`1 = poly_MakeHint (lifts_wpoly _low)             *)
(*                                       (lifts_wpoly _high)           *)
(*   res.`2 = count (fun i => (liftu_wpoly res.`1).[i] <> Zq.zero)    *)
(*                  (iota_ 0 256)                                      *)
(* ================================================================== *)

lemma polynomial____make_hint_ll : islossless M.polynomial____make_hint.
proof.
proc.
wp; while (offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset);
  last by auto => /> /#. 
by move => *; auto => /> /#. 
qed.

lemma polynomial____make_hint_correct
      (_h : W32.t Array256.t) (_low : W32.t Array256.t) (_high : W32.t Array256.t) :
    hoare [ M.polynomial____make_hint :
        hints = _h /\ low_coefficients = _low /\ high_coefficients = _high /\
        (* low: LowBits output range [-(gamma2-1), gamma2] *)
        wpoly_srng (gamma2 - 1) gamma2 _low /\
        (* high: HighBits (w1) output range [0, (q-1) / (2*gamma2)] *)
        wpoly_urng ((q - 1) %/ (2 * gamma2) + 1) _high
        ==>
        liftu_wpoly res.`1 = poly_MakeHint (lifts_wpoly _low) (lifts_wpoly _high) /\
        res.`2 = count (fun i => (liftu_wpoly res.`1).[i] <> Zq.zero) (iota_ 0 256)
    ].
proof.
admitted.

lemma polynomial____make_hint_ph
      (_h : W32.t Array256.t) (_low : W32.t Array256.t) (_high : W32.t Array256.t) :
    phoare [ M.polynomial____make_hint :
        hints = _h /\ low_coefficients = _low /\ high_coefficients = _high /\
        wpoly_srng (gamma2 - 1) gamma2 _low /\
        wpoly_urng ((q - 1) %/ (2 * gamma2) + 1) _high
        ==>
        liftu_wpoly res.`1 = poly_MakeHint (lifts_wpoly _low) (lifts_wpoly _high) /\
        res.`2 = count (fun i => (liftu_wpoly res.`1).[i] <> Zq.zero) (iota_ 0 256)
    ] = 1%r
  by conseq polynomial____make_hint_ll (polynomial____make_hint_correct _h _low _high).
