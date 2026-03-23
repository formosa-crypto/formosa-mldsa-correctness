require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.

require import CircuitBindings Bindings.

from Spec require import GFq Rq Parameters MLDSA_W32_Rep Symmetric Serialization.

import CDR Round Zq.

require import XArray256 Array256.

require import WArray1024.

op check_inf_norm_circuit (_a : W32.t Array256.t) (_threshold : int) : bool =
   all (fun i => (W32.of_int (-_threshold) \slt _a.[i] /\ _a.[i] \slt W32.of_int (_threshold)))  (iotared 0 256).

lemma polynomial____check_infinity_norm_correct (_a : W32.t Array256.t) (_threshold : int) :
   hoare [ M.polynomial____check_infinity_norm :
       _threshold = (1 `<<` gamma1m1_bits) - 49 * w1_bits /\
       polynomial = _a /\ threshold = _threshold /\
       wpoly_srng (gamma1-1) gamma1 _a
     ==>
       (wpoly_infnorm_lt _threshold _a => res = W64.zero) /\
       (!wpoly_infnorm_lt _threshold _a => res <> W64.zero)
   ].
proof.
rewrite /(`<<`) /=.
proc => /=.
seq 2 : (#pre /\ threshold_vector = W256.of_int (524091)).
+ auto => /> *; rewrite /VMOV_64 /= to_uint_eq to_uint_zeroextu256 of_uintK /=.
  rewrite -(W128.of_uintK 524091); congr; rewrite wordP => i ib.
  rewrite /pack2_t initiE 1:/# /= get_of_list 1:/# /= of_intE /= bits2wE initiE 1:/# /=.
  case (i %/ 64 = 0) => ? /=.
  + rewrite of_intE /= bits2wE initiE 1:/# /=.
    by rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /= nth_mkseq 1:/# /= /#.
  rewrite /BitEncoding.BS2Int.int2bs nth_mkseq 1:/# /=.
  rewrite pdiv_small; last by smt().
  smt(@StdOrder pow2_64).
  
proc change ^while.1 : { coefficients <- if (0 <= offset*8 <= 32*256-256)
                                         then BSWAS_256u32_256.sliceget polynomial (offset*8)
                                         else get256_direct (WArray1024.init32 (fun i => polynomial.[i])) offset; }.
                + auto => /> &2.
                  case (0 <= offset{2} * 8 <= 7936); last by auto.
                  by move => ?; rewrite BSWAS_256u32_256_slicegetE /#.

wp 7.
proc change 7 : { zf <- msb_mask = W32.zero; }.
+ by auto => /= &1 &2 ->; rewrite /TEST_32 /rflags_of_bwop /= /ZF_of  /=.
                  
unroll for ^while.
cfold 131.
wp -1.
conseq (: polynomial = _a /\ threshold_vector = W256.of_int 524091 /\
          all (fun i => W32.of_int (-(524288-1)) \sle _a.[i] /\ _a.[i] \sle W32.of_int 524288) (iotared 0 256) ==>
    zf =  (check_inf_norm_circuit _a 524092)); last 
     by rewrite  /check_inf_norm_circuit /=; circuit.  


(*  Connect circuit form to poly_infnorm spec *)
+ move =>  &1; rewrite iotaredE mldsa65_gamma1 => |>; rewrite /wpoly_srng !allP /= => H.
  move => x; rewrite mem_iota /= => *; rewrite /(\sle) /= !of_sintK /= /smod /= /#.

move => &hr [[H H1] H2] msbm -> /=; rewrite /wpoly_infnorm /wpoly_srng /check_inf_norm_circuit !allP /SETcc;split;rewrite iotaredE /TEST_32 /= => H3.
+ rewrite ifF /=.
  + rewrite  /(\slt) /= !of_sintK /= /smod /=.
    move => x; rewrite mem_iota => ?.
    move : H3; rewrite /wpoly_infnorm_lt /wpoly_srng allP /= /#.
  by rewrite to_uint_eq /=.
    
rewrite ifT /=.
  + rewrite  /(\slt) /= !of_sintK /= /smod /=.
    move : H3; rewrite /wpoly_infnorm_lt /wpoly_srng allP /=;smt(mem_iota).
  by rewrite to_uint_eq /=.
qed.

lemma polynomial____check_infinity_norm_ll : islossless M.polynomial____check_infinity_norm.
proof.
proc.
wp;while (0 <= offset <= 1024 /\ offset %% 32 = 0) (1024 - offset); auto => /> /#.
qed.

lemma polynomial____check_infinity_norm_ph (_a : W32.t Array256.t) (_threshold : int) :
   phoare [ M.polynomial____check_infinity_norm :
       _threshold = (1 `<<` gamma1m1_bits) - 49 * w1_bits /\
       polynomial = _a /\ threshold = _threshold /\
       wpoly_srng (gamma1-1) gamma1 _a
     ==>
       (wpoly_infnorm_lt _threshold _a => res = W64.zero) /\
       (!wpoly_infnorm_lt _threshold _a => res <> W64.zero)
   ] = 1%r
 by  conseq polynomial____check_infinity_norm_ll (polynomial____check_infinity_norm_correct _a _threshold).
