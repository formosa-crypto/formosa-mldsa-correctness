require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge.

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
