require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Common_modular.

require import CircuitBindings Bindings XArray48.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

require import Polynomial.
                         
import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

require import Array2 Array32 Array48 Array64 Array256 Array768 Array1280 Array1536
               Array1920 Array1952 Array3309 Array7680.
               require import WArray48.

require import BitEncoding.
from CryptoSpecs require import JWordList.
import BitChunking.

lemma or64_ne0 w1 w2 :
        w1 `|` w2 <> W64.zero <=>
        (w1 <> W64.zero \/ w2 <> W64.zero).
have ? := W64.wordP w1 w2.
have ? := W64.orwE w1 w2.
split => H; 1: by smt(W64.orw0 W64.or0w W64.zerowE).
by elim H; rewrite !wordP /= negb_forall /= /#.
qed.

lemma row_vector____check_infinity_norm_correct (_a : W32.t Array1280.t) (_threshold : int) :
    phoare [ M.row_vector____check_infinity_norm :
       _threshold = (1 `<<` gamma1m1_bits) - 49 * w1_bits /\
       arg.`1 = _a /\ arg.`2 = _threshold /\
       wpolylvec_srng (lvec_unflatten256 _a) (gamma1-1) gamma1 
        ==>
        (wpolylvec_infnorm_lt _threshold (lvec_unflatten256 _a) => res = W64.zero) /\
        (!wpolylvec_infnorm_lt _threshold (lvec_unflatten256 _a) => res <> W64.zero)
    ] = 1%r.
proof.
have Hlvec := mldsa65_lvec.
have Hgamma1 := mldsa65_gamma1.
  
rewrite /(`<<`) /=.
proc => /=.
while (0 <= i <= 5 /\ threshold = _threshold /\ vector = _a /\ _threshold = 524092 /\
       wpolylvec_srng (lvec_unflatten256 _a) (gamma1 - 1) gamma1  /\
       ((forall k, 0<=k<i =>
          wpoly_srng (524092-1) (524092-1) (lvec_unflatten256 _a).[k]) => result = W64.zero) /\
        (! (forall k, 0<=k<i =>
          wpoly_srng (524092-1) (524092-1) (lvec_unflatten256 _a).[k]) => result <> W64.zero)) (5 - i); last first.
+ auto => |> ?; split;1:smt().
  move => i rr;split;1:smt().
  move => ??? Ht Hf; rewrite /wpolylvec_infnorm_lt /wpolylvec_srng !allP /= /#.

 move => ?.
 exlim i => _i.
 wp; call (polynomial____check_infinity_norm_ph ((lvec_unflatten256 _a).[_i]) _threshold).
 rewrite /(`<<`) /=; auto => |> &hr ??Hrng Ht Hf ?;split.
 + split.
   + by rewrite tP => k kb; rewrite initiE 1:/# /= /lvec_unflatten256 initiE 1:/# /= get_of_list /= 1:/# nth_sub /#.
   +  move : Hrng; rewrite /wpolylvec_srng /wpoly_srng !allP /= => H.
      have := H _i _;1:smt().
      by rewrite allP /#. 

move => H H0 rr0 Htp Hfp;do split;1,2,5..:smt().
+ case (result{hr} = W64.zero) => ?; smt(W64.or0w).
+ case (result{hr} = W64.zero) => HH.
  + move => ?; have Hj : !wpoly_srng 524091 524091 (lvec_unflatten256 _a).[_i] by smt().
    move : Hfp; rewrite /wpoly_infnorm_lt /= Hj /= => ->;apply or64_ne0; smt(W64.to_uint_eq W64.of_uintK W64.to_uintK W64.to_uint_cmp pow2_64).
  + move => ?; move : HH.
    by smt(or64_ne0).
qed.

(* ================================================================== *)
(* row_vector____dot_product                                            *)
(* Computes dot product of two row vectors (5 polynomials each):       *)
(*   output = sum_{i=0}^{4} pmmar(lhs[i], rhs[i])                    *)
(* Calls polynomial____zero, polynomial__pointwise_montgomery_multiply *)
(* _and_reduce, polynomial____pointwise_add_to_total in a 5-iter loop.*)
(* Spec: ntt_dotp from VecMat.ec                                       *)
(* ================================================================== *)

lemma row_vector____dot_product_ll : islossless M.row_vector____dot_product.
proof.
proc.
while (0 <= i <= 5) (5 - i); last first.
+ wp; call polynomial____zero_ll.
  by auto => /#.
move => *.
wp; call polynomial____pointwise_add_to_total_ll.
wp; call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
by auto => /#.
qed.

lemma row_vector____dot_product_correct
      (_out : W32.t Array256.t)
      (_lhs : W32.t Array1280.t) (_rhs : W32.t Array1280.t) :
    hoare [ M.row_vector____dot_product :
        output = _out /\ lhs = _lhs /\ rhs = _rhs /\
        wpolylvec_ntt_orng (lvec_unflatten256 _lhs) /\
        wpolylvec_ntt_orng (lvec_unflatten256 _rhs)
        ==>
        lifts_wpoly res = ntt_dotp (lifts_wpolylvec (lvec_unflatten256 _lhs))
                                    (lifts_wpolylvec (lvec_unflatten256 _rhs))
    ].
proof.
admitted.

lemma row_vector____dot_product_ph
      (_out : W32.t Array256.t)
      (_lhs : W32.t Array1280.t) (_rhs : W32.t Array1280.t) :
    phoare [ M.row_vector____dot_product :
        output = _out /\ lhs = _lhs /\ rhs = _rhs /\
        wpolylvec_ntt_orng (lvec_unflatten256 _lhs) /\
        wpolylvec_ntt_orng (lvec_unflatten256 _rhs)
        ==>
        lifts_wpoly res = ntt_dotp (lifts_wpolylvec (lvec_unflatten256 _lhs))
                                    (lifts_wpolylvec (lvec_unflatten256 _rhs))
    ] = 1%r
  by conseq row_vector____dot_product_ll
            (row_vector____dot_product_correct _out _lhs _rhs).

(* ================================================================== *)
(* row_vector____multiply_with_matrix_A                                 *)
(* Computes A * v where A is 6x5 matrix and v is 5-element row vector.*)
(* Calls row_vector____dot_product in a 6-iteration loop.              *)
(* Spec: ntt_mulmxv from VecMat.ec                                     *)
(* ================================================================== *)

lemma row_vector____multiply_with_matrix_A_ll :
    islossless M.row_vector____multiply_with_matrix_A.
proof.
proc.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *.
wp; call row_vector____dot_product_ll.
by auto => /#.
qed.

lemma row_vector____multiply_with_matrix_A_correct
      (_mat : W32.t Array7680.t) (_vec : W32.t Array1280.t) :
    hoare [ M.row_vector____multiply_with_matrix_A :
        matrix_A = _mat /\ vector = _vec /\
        wpolylvec_ntt_orng (lvec_unflatten256 _vec)
        (* matrix_A range: each row is a polylvec with ntt_orng *)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          ntt_mulmxv (liftu_wpolymat (mat_unflatten256 _mat))
                     (lifts_wpolylvec (lvec_unflatten256 _vec))
    ].
proof.
admitted.

lemma row_vector____multiply_with_matrix_A_ph
      (_mat : W32.t Array7680.t) (_vec : W32.t Array1280.t) :
    phoare [ M.row_vector____multiply_with_matrix_A :
        matrix_A = _mat /\ vector = _vec /\
        wpolylvec_ntt_orng (lvec_unflatten256 _vec)
        ==>
        lifts_wpolykvec (kvec_unflatten256 res) =
          ntt_mulmxv (liftu_wpolymat (mat_unflatten256 _mat))
                     (lifts_wpolylvec (lvec_unflatten256 _vec))
    ] = 1%r
  by conseq row_vector____multiply_with_matrix_A_ll
            (row_vector____multiply_with_matrix_A_correct _mat _vec).
