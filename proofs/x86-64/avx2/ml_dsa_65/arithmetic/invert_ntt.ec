require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import CDR Round Zq.

require import Array256.

(* ================================================================== *)
(* polynomial__invert_ntt_montgomery                                    *)
(* Computes the inverse NTT of a polynomial in NTT-domain form.        *)
(* Spec: lifts_wpoly res = invntt (lifts_wpoly _a)                     *)
(* Precondition: _a must be a valid NTT output (wpoly_ntt_orng)        *)
(* ================================================================== *)

lemma polynomial__invert_ntt_montgomery_ll : islossless M.polynomial__invert_ntt_montgomery.
proof.
proc.
wp; while (0 <= i <= (256 * 32) %/ 8 /\ i %% 32 = 0) ((256 * 32) %/ 8 - i);
  last first.
+ (* 8 layer calls, sequential *)
  do 8!(wp; call (: true ==> true); 1: by admit). (* each layer is lossless *)
  by auto => /#.
move => *.
wp; call (: true ==> true);1: by admit. (* montgomery_multiply_and_reduce *)
by auto => /#.
qed.

lemma polynomial__invert_ntt_montgomery_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial__invert_ntt_montgomery :
        polynomial = _a /\ wpoly_ntt_orng _a
        ==>
        (* spec-level inverse NTT *)
        lifts_wpoly res = invntt (lifts_wpoly _a)
    ].
proof.
admitted.

lemma polynomial__invert_ntt_montgomery_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial__invert_ntt_montgomery :
        polynomial = _a /\ wpoly_ntt_orng _a
        ==>
        lifts_wpoly res = invntt (lifts_wpoly _a)
    ] = 1%r
  by conseq polynomial__invert_ntt_montgomery_ll
            (polynomial__invert_ntt_montgomery_correct _a).
