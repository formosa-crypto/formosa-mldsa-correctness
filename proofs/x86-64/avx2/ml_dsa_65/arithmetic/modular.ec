require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep.

import CDR Round Zq.

require import Array256.

(* ================================================================== *)
(* polynomial__reduce32                                                 *)
(* reduce32(a)[i] = a[i] mod q, centered representative                *)
(* Concretely: a[i] - round(a[i] / 2^23) * q                         *)
(* Spec: lifts_wpoly res = lifts_wpoly _a (same GFq value)             *)
(*       wpoly_srng ((q-1)%/2) ((q-1)%/2) res  (centered rep)         *)
(* ================================================================== *)

lemma polynomial__reduce32_ll : islossless M.polynomial__reduce32.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 32 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
by move => *; auto => /#.
qed.

lemma polynomial__reduce32_correct (_a : W32.t Array256.t) :
    hoare [ M.polynomial__reduce32 :
        polynomial = _a
        ==>
        (* GFq value preserved *)
        lifts_wpoly res = lifts_wpoly _a /\
        (* output is centered representative: |to_sint coeff| <= (q-1)/2 *)
        wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) res
    ].
proof.
admitted.

lemma polynomial__reduce32_ph (_a : W32.t Array256.t) :
    phoare [ M.polynomial__reduce32 :
        polynomial = _a
        ==>
        lifts_wpoly res = lifts_wpoly _a /\
        wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2) res
    ] = 1%r
  by conseq polynomial__reduce32_ll (polynomial__reduce32_correct _a).

(* ================================================================== *)
(* polynomial__pointwise_montgomery_multiply_and_reduce                 *)
(* Computes lhs[i] * rhs[i] in Zq via Montgomery reduction.           *)
(* Both lhs and rhs must be NTT-domain polynomials.                    *)
(* Spec: res = basemul (lifts_wpoly lhs) (lifts_wpoly rhs)             *)
(*       where basemul a b = init (fun i => a.[i] * b.[i]) in Rq      *)
(* ================================================================== *)

lemma polynomial__pointwise_montgomery_multiply_and_reduce_ll :
    islossless M.polynomial__pointwise_montgomery_multiply_and_reduce.
proof.
proc.
wp; while (0 <= offset <= (256 * 32) %/ 8 /\ offset %% 64 = 0)
         ((256 * 32) %/ 8 - offset); last by auto => /#.
move => *.
(* each loop body processes two 32-byte chunks via montgomery_multiply_and_reduce *)
wp; call (: true ==> true); 1: by islossless. (* second call *)
wp; call (: true ==> true); 1: by islossless. (* first call *)
by auto => /#.
qed.

lemma polynomial__pointwise_montgomery_multiply_and_reduce_correct
      (_prod : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t) :
    hoare [ M.polynomial__pointwise_montgomery_multiply_and_reduce :
        product = _prod /\ lhs = _lhs /\ rhs = _rhs /\
        wpoly_ntt_orng _lhs /\ wpoly_ntt_orng _rhs
        ==>
        (* coefficient-wise product in Zq (NTT domain) *)
        lifts_wpoly res = basemul (lifts_wpoly _lhs) (lifts_wpoly _rhs) /\
        wpoly_ntt_orng res
    ].
proof.
admitted.

lemma polynomial__pointwise_montgomery_multiply_and_reduce_ph
      (_prod : W32.t Array256.t) (_lhs : W32.t Array256.t) (_rhs : W32.t Array256.t) :
    phoare [ M.polynomial__pointwise_montgomery_multiply_and_reduce :
        product = _prod /\ lhs = _lhs /\ rhs = _rhs /\
        wpoly_ntt_orng _lhs /\ wpoly_ntt_orng _rhs
        ==>
        lifts_wpoly res = basemul (lifts_wpoly _lhs) (lifts_wpoly _rhs) /\
        wpoly_ntt_orng res
    ] = 1%r
  by conseq polynomial__pointwise_montgomery_multiply_and_reduce_ll
            (polynomial__pointwise_montgomery_multiply_and_reduce_correct _prod _lhs _rhs).
