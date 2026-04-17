require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Row_vector Polynomial Commitment T1
                           Common_ntt Common_modular Common_invert_ntt Rounding.

require import CircuitBindings Bindings XArray48.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

require import Array2 Array32 Array48 Array64 Array256 Array768 Array1280 Array1536
               Array1920 Array1952 Array3309 Array7680.
               require import WArray48.

require import BitEncoding.
from CryptoSpecs require import JWordList.
import BitChunking.

lemma compare_commitment_hashes_ll : islossless M.__compare_commitment_hashes.
proof.
proc.
wp;while (0 <=  offset <= 48 /\ offset %% 16 = 0) (48 -  offset); last by auto => />; smt().
auto => /> ; smt().
qed.

lemma compare_commitment_hashes_correct (_lhs _rhs : W8.t Array48.t) :
    phoare [ M.__compare_commitment_hashes :
        arg.`1 = _lhs /\ arg.`2 = _rhs
        ==>
        res = (if _lhs = _rhs then W64.of_int 0 else -W64.one)
    ] = 1%r.
proof.
have hh : hoare [ M.__compare_commitment_hashes :
    arg.`1 = _lhs /\ arg.`2 = _rhs
    ==>
    res = (if _lhs = _rhs then W64.of_int 0 else -W64.one) ].
+ proc => /=.
  proc change 2 : { lhs_bytes <- if (0 <=  offset * 8 <= 48*8-128)
                                  then BSWAS_48u8_128.sliceget lhs (offset * 8)
                                  else get128_direct (WArray48.init8 (fun i => lhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last  by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  proc change 3 : { rhs_bytes <- if (0 <=  offset * 8 <= 48*8-128)
                                  then BSWAS_48u8_128.sliceget rhs ( offset * 8)
                                  else get128_direct (WArray48.init8 (fun i => rhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  proc change ^while.1 : { lhs_bytes <- if (0 <= offset * 8 <= 48*8-128)
                                         then BSWAS_48u8_128.sliceget lhs (offset * 8)
                                         else get128_direct (WArray48.init8 (fun i => lhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  proc change ^while.2 : { rhs_bytes <- if (0 <= offset * 8 <= 48*8-128)
                                         then BSWAS_48u8_128.sliceget rhs (offset * 8)
                                         else get128_direct (WArray48.init8 (fun i => rhs.[i])) (offset); }.
  + auto => /> &2.
    case (0 <= offset{2} * 8 <= 256); last by auto.
    by move => ?; rewrite -BSWAS_48u8_128_slicegetE /#.
  cfold 1;unroll for ^while.
  cfold 12.
  wp 12.
  conseq (: _ ==> _lhs = _rhs <=> result = W64.of_int 65535).
  + move => &hr [<- <-] rr [Hl Hr].
    case (rr <> W64.of_int 65535); last first.
    + move => HH; rewrite Hr //=.
      move => ?; rewrite ifF 1:/# /=.
      case (lhs{hr} = rhs{hr}) => ?; 1: by
       rewrite to_uint_eq /=; smt(W64.to_uint_cmp pow2_64).
      by rewrite to_uint_eq /= to_uintN /=. 
  by circuit.
conseq compare_commitment_hashes_ll hh;smt().
qed.


(* ================================================================== *)
(* reconstruct_signer_commitment                                       *)
(* Reconstructs w1' = UseHint(h, A*z - c*t1*2^d) for each of 6 rows. *)
(* Per-component loop body:                                            *)
(*   t1_decode → shift_left → NTT → pmmar(c,t1) →                    *)
(*   subtract(az, ct1) → reduce32 → invNTT → cond_add_mod →          *)
(*   use_hints → write back                                            *)
(* Then commitment_encode on the result.                               *)
(* Spec: w1Encode(UseHint(h, Az - c*NTT^{-1}(NTT(t1*2^d)*chat)))    *)
(* ================================================================== *)

lemma reconstruct_signer_commitment_ll :
    islossless M.reconstruct_signer_commitment.
proof.
proc.
wp; call commitment____encode_ll.
while (0 <= i <= 6) (6 - i); last by auto => /#.
move => *; wp.
call polynomial__use_hints_ll; wp.
call polynomial__conditionally_add_modulus_ll.
call polynomial__invert_ntt_montgomery_ll.
call polynomial__reduce32_ll.
call polynomial__subtract_ll; wp.
call polynomial__pointwise_montgomery_multiply_and_reduce_ll.
call polynomial__ntt_ll.
call polynomial____shift_coefficients_left_ll.
call t1__decode_polynomial_ll.
by auto => /#.
qed.

(* Spec-level t1 polykvec obtained from the t1_encoded bytes (6 chunks of 320 bytes, *)
(* each decoded via SimpleBitUnpack with range 2^(q_bits-d)-1 = 1023 = b_t1).        *)
op t1_from_t1enc (_t1enc : W8.t Array1920.t) : polykvec =
   KArray.init (fun i =>
      SimpleBitUnpack
        (take ((n * (q_bits - d)) %/ 8)
              (drop (((n * (q_bits - d)) %/ 8) * i) (to_list _t1enc)))
        (2^(q_bits - d) - 1)).

(* The reconstructed signer commitment at the spec level: the wapprox that the proc *)
(* computes internally, reused by the verify proof after algebra bridging.           *)
op signer_commitment_spec
     (_t1enc : W8.t Array1920.t) (_ch : W32.t Array256.t) (_az : W32.t Array1536.t)
   : polykvec =
   invnttv (lifts_wpolykvec (kvec_unflatten256 _az)
             - ntt_smul (lifts_wpoly _ch)
                        (nttv (smul (t1_from_t1enc _t1enc) (incoeff (2^d))))).

lemma reconstruct_signer_commitment_correct
      (_t1enc : W8.t Array1920.t) (_ch : W32.t Array256.t)
      (_az : W32.t Array1536.t) (_hints : W32.t Array1536.t) :
    hoare [ M.reconstruct_signer_commitment :
        t1_encoded = _t1enc /\ challenge_as_ntt = _ch /\
        a_times_signer_response = _az /\ hints = _hints /\
        wpoly_ntt_orng _ch /\
        wpolykvec_urng (kvec_unflatten256 _hints) 2
        ==>
        BytesW1.of_list (to_list res) =
          w1Encode (UseHint (liftu_wpolykvec (kvec_unflatten256 _hints))
                            (signer_commitment_spec _t1enc _ch _az))
    ].
proof.
admitted.

lemma reconstruct_signer_commitment_ph
      (_t1enc : W8.t Array1920.t) (_ch : W32.t Array256.t)
      (_az : W32.t Array1536.t) (_hints : W32.t Array1536.t) :
    phoare [ M.reconstruct_signer_commitment :
        t1_encoded = _t1enc /\ challenge_as_ntt = _ch /\
        a_times_signer_response = _az /\ hints = _hints /\
        wpoly_ntt_orng _ch /\
        wpolykvec_urng (kvec_unflatten256 _hints) 2
        ==>
        BytesW1.of_list (to_list res) =
          w1Encode (UseHint (liftu_wpolykvec (kvec_unflatten256 _hints))
                            (signer_commitment_spec _t1enc _ch _az))
    ] = 1%r
  by conseq reconstruct_signer_commitment_ll
            (reconstruct_signer_commitment_correct _t1enc _ch _az _hints).

lemma ml_dsa_65_verify_correct _m :
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).verify ~ M.ml_dsa_65_verify :
       Glob.mem{2} = _m /\
       arg{1}.`1 = BytesPK.of_list (to_list arg{2}.`1)
    /\ arg{1}.`2 = BytesSig.init (fun i => arg{2}.`5.[i])
    /\ W64.to_uint arg{2}.`2.[1] <= 255
    /\ 0 <= arg{2}.`4
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < 18446744073709551616
    /\ message_pointer{2} + message_size{2} < 18446744073709551616
    /\ arg{1}.`3 = [W8.zero; truncateu8 arg{2}.`2.[1]]
                   ++ memread _m (W64.to_uint arg{2}.`2.[0]) (W64.to_uint arg{2}.`2.[1])
                   ++ memread _m arg{2}.`3 arg{2}.`4
       ==>
       Glob.mem{2} = _m /\
       res{1} = (res{2} = W64.of_int 0)
   ].
proof.
have Hlvec := mldsa65_lvec.
have Hkvec := mldsa65_kvec.
have HLambda := mldsa65_lambda.
have HEta := mldsa65_Eta.
have Htau := mldsa65_tau.
have Hgamma1 := mldsa65_gamma1.

proc => /=; conseq |>.

sp 0 2.
rcondt {2} ^if; 1: by auto => /> /#.
inline {2} M.__verify_internal.
sp 0 6.
seq 1 9 : #pre; 1: by auto.
sp 1 0.
seq 1 0 : (#pre /\
    rho{1} = Bytes32.of_list (take 32 (BytesPK.to_list pk{1})) /\
    t1{1}  = KArray.init (fun i =>
        SimpleBitUnpack
          (take ((n * (q_bits-d)) %/ 8)
                (drop (((n * (q_bits-d)) %/ 8) * i + 32) (BytesPK.to_list pk{1})))
          (2^(q_bits - d) - 1))).
+ ecall{1} (pkDecode_corr pk{1}).
  by auto.

seq 1 1 : (#pre /\
    ct{1} = BytesCT.init (fun i => signature{2}.[i]) /\
    lifts_wpolylvec (lvec_unflatten256 signer_response{2}) = z{1} /\
    wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1 - 1) gamma1 /\
    (h{1} = None => result1{2} = -W64.one) /\
    (h{1} <> None =>
        result1{2} = W64.zero /\
        liftu_wpolykvec (kvec_unflatten256 hints{2}) = oget h{1} /\
        wpolykvec_urng (kvec_unflatten256 hints{2}) 2)).
+ ecall (signature_decode signature{2}).
  by auto.
seq 0 1 : (#pre /\
    (!wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2}) => result2{2} <> W64.of_int 0) /\
    (wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2})  => result2{2} = W64.zero)).
+ ecall {2} (row_vector____check_infinity_norm_correct signer_response{2} ((1 `<<` gamma1m1_bits) - 49 * w1_bits)).
  auto => /> &1 &2 ?????? rr0.
  have -> : (1 `<<` gamma1m1_bits) - 49 * w1_bits = gamma1 - Beta
    by rewrite /(`<<`) /= /Beta /=; smt(mldsa65_gamma1 mldsa65_tau mldsa65_Eta).
  have Hbnd : 0 < gamma1 - Beta <= q %/ 2
    by rewrite /Beta /=; smt(mldsa65_gamma1 mldsa65_tau mldsa65_Eta). 
  by smt(). 
  
if {1}; last first.
+ sp 0 1; rcondf {2} 1.
  + auto => |> &hr ?????-> ??. 
    have ? : (- W64.one <> W64.zero); last by smt(or64_ne0).
    by rewrite to_uint_eq to_uintN  /=.
  auto => /> &2 ?????  -> ??.
    have ? : (- W64.one <> W64.zero); last by smt(or64_ne0).
    by rewrite to_uint_eq to_uintN  /=.
  
sp;if {2}; last first.
+ wp; call {1} (: true ==> true); 1: by proc*; exlim  rho => _rho;  call (SampleInBall_correct _rho).
  wp; call {1} (: true ==> true); 1: by proc*; exlim  rho => _rho;  call (ExpandA_correct _rho).
  auto => /> &1 &2 ?????????? rr0 rr1.
  have ? : (!wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2})) by smt(or64_ne0).
  have Hrng : wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1-1) gamma1 by smt().
  have Hb : 0 < gamma1 - Beta <= q %/ 2 by rewrite /Beta /=; smt(mldsa65_gamma1 mldsa65_tau mldsa65_Eta).
  have Hq1 : (gamma1-1) + 1 <= q %/ 2 by smt(mldsa65_gamma1).
  have Hq2 : gamma1 <= q %/ 2 by smt(mldsa65_gamma1).
  have ? := wpolylvec_infnorm_unliftE (gamma1-Beta) (gamma1-1) gamma1
              (lvec_unflatten256 signer_response{2}) Hb Hq1 Hq2 Hrng.
  by smt().
  
(* expand A *)
seq 1 1 : (#pre /\
      liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
      wpolymat_urng (mat_unflatten256 matrix_A{2}) q).
  + ecall{1} (ExpandA_correct rho{1}).
    ecall{2} (matrix_A_correct (Array32.init (fun i => verification_key{2}.[i]))).
    auto => |> &1 &2 ??????????? rr0 -> ?;congr.
    apply Bytes32.tP => k kb.
    do 2!(rewrite Bytes32.get_of_list //).
    rewrite get_to_list initiE 1:/# /=.
    rewrite nth_take 1,2:/# BytesPK.get_to_list /=.
    by rewrite BytesPK.get_of_list 1:/# get_to_list.

(* anticipate hashing *)
swap {2} [6..7] -5.

(* verification key hash. *)
sp 1 0.
seq 0 1 : (#pre /\
      verification_key_hash{2} =
        Array64.of_list witness (Bytes64.to_list (H_tr pk{1}))).
  + ecall{2} (hash_verification_key_correct verification_key{2}).
    by auto.

(* message representative *)    
sp 1 0.
seq 0 1 : (#pre /\
      message_representative{2} =
        Array64.of_list witness (Bytes64.to_list mu{1})).
  + ecall{2} (derive_message_representative_ph
                 verification_key_hash{2}
                 (memread _m context_pointer{2} context_size{2})
                 (memread _m message_pointer{2} message_size{2})).
    wp; skip => /> &1 &2 *; do split.
    + by rewrite !size_memread /=; smt(W64.to_uint_cmp).
    + by rewrite !size_memread /=; smt(W64.to_uint_cmp).
    + by rewrite !size_memread /=; smt(W64.to_uint_cmp).
    + by rewrite !size_memread /=;  smt(W64.to_uint_cmp).
    move => ????;do congr.
    + rewrite Bytes64.tP => k kb.
      by rewrite Bytes64.get_of_list // get_to_list get_of_list //.
    + by rewrite size_memread; smt(W64.to_uint_cmp).
   
(* anticipate sib *)
swap {2} [3..4] -2.
  seq 1 1 : (#pre /\ lifts_wpoly challenge{2} = c{1}).
  + call sample_challenge_correct.
    wp; skip => /> &1 &2 *.
    rewrite BytesCT.tP => i ib.
    rewrite BytesCT.initiE 1:/# BytesCT.get_of_list 1:/#.
    by rewrite get_to_list initiE /#.

(* jump over algebra *)
seq 2 4 :
  (#pre /\
    BytesW1.of_list (to_list reconstructed_signer_commitment{2}) = w1Encode w1{1}); last first.

(* recompute hash *)
sp 1 0.
seq 0 1 : (#pre /\
      expected_commitment_hash{2} =
        Array48.of_list witness (BytesCT.to_list (H_ct mu{1} (w1Encode w1{1})))).
  + ecall{2} (derive_commitment_hash_ph message_representative{2}
                 reconstructed_signer_commitment{2}).
    wp; skip => /> &1 &2 *; do congr.
    rewrite Bytes64.tP => k kb.
    + by rewrite Bytes64.get_of_list // get_to_list get_of_list //.

 wp; ecall{2} (compare_commitment_hashes_correct expected_commitment_hash{2} (Array48.init (fun (i : int) => signature_encoded{2}.[0 + i]))).
 
 wp;skip => /> &1 &2 *.
 pose xx := H_ct
   (H_mu (H_tr (BytesPK.of_list (to_list verification_key{2})))
      (W8.zero :: truncateu8 context{2}.[1] :: (memread _m (to_uint context{2}.[0]) (to_uint context{2}.[1]) ++  memread _m message_pointer{2} message_size{2}))) (
   w1Encode w1{1}).
have ? : wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2}) by smt(or64_ne0).
have -> /=: infnorm_lt (lifts_wpolylvec (lvec_unflatten256 signer_response{2})) (gamma1 - Beta).
+ have /# := wpolylvec_infnorm_liftE (gamma1-Beta) 
              (lvec_unflatten256 signer_response{2}) _ _; by smt(). 
suff: ((BytesCT.init ("_.[_]" signature{2}) = xx) <=>  (Array48.of_list witness (BytesCT.to_list xx) = Array48.init ("_.[_]" signature{2}))); last first.
+ by rewrite tP BytesCT.tP /=;split => H i ib; have := H i _;[ by smt() | rewrite get_of_list 1:/# BytesCT.get_to_list BytesCT.initiE 1:/# /= initiE /#  | by smt() | rewrite get_of_list 1:/# BytesCT.get_to_list BytesCT.initiE 1:/# /= initiE /# ].

move => -> ; pose bb := Array48.of_list witness (BytesCT.to_list xx) = Array48.init ("_.[_]" signature{2}).
by case (bb) => //=; rewrite to_uint_eq to_uintN /=.

(* algebra *)
admit.

qed.
