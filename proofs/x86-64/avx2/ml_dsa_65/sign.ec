require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Row_vector S1 S2 T0 Mask
                           Sign_norm_checks Common_ntt.

require import Column_vector.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

require import Array2 Array32 Array48 Array64 Array128 Array256
               Array416 Array640 Array768 Array1280 Array1536 Array2496
               Array3309 Array4032 Array7680.

require import BitEncoding.
from CryptoSpecs require import JWordList.
import BitChunking.

(* Correctness of the AVX2 ML-DSA-65 signing function.
   We prove an equiv between:
     - MLDSA(...).sign_derand(sk, m, coins) on the spec side
     - M.ml_dsa_65_sign(sig, sk, ctx, msg_ptr, msg_size, randomness) on the Jasmin side

   The _m parameter is a snapshot of Glob.mem so that memread expressions are stable.
   The precondition connects:
     - sk (BytesSK.t) to the Jasmin signing_key (Array4032)
     - coins via rnd_to_list (abstract rnd_ type) to the Jasmin randomness (Array32)
     - m (W8.t list) to the context-prefixed message read from memory
   The postcondition connects the output signatures byte-for-byte and confirms
   the Jasmin result code is 0 (success, kappa not exceeded). *)

lemma ml_dsa_65_sign_correct _m :
    kappa_max = (65535 - lvec) %/ lvec =>
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).sign_derand
            ~ M.ml_dsa_65_sign :
       Glob.mem{2} = _m
    /\ sk{1} = BytesSK.of_list (to_list signing_key{2})
    /\ rnd_to_list coins{1} = to_list randomness{2}
    /\ W64.to_uint context{2}.[1] <= 255
    /\ 0 <= message_size{2}
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < W64.modulus
    /\ message_pointer{2} + message_size{2} < W64.modulus
    /\ m{1} = [W8.zero; truncateu8 context{2}.[1]]
              ++ memread _m (W64.to_uint context{2}.[0]) (W64.to_uint context{2}.[1])
              ++ memread _m message_pointer{2} message_size{2}
    /\ valid_s1_bytes (Array640.init (fun i => signing_key{2}.[128 + i]))
    /\ valid_s2_bytes (Array768.init (fun i => signing_key{2}.[768 + i]))
       ==>
       Glob.mem{2} = _m
    /\ (res{1}.`1 = None <=> res{2}.`2 = -W64.one)
    /\ (res{1}.`1 <> None =>
          BytesSig.to_list (oget res{1}.`1) = to_list res{2}.`1 /\
          res{2}.`2 = W64.zero)
    ].
proof.
have Hlvec   := mldsa65_lvec.
have Hkvec   := mldsa65_kvec.
have HEta    := mldsa65_Eta.
have Hgamma1 := mldsa65_gamma1.
have Htau    := mldsa65_tau.
move => Hkappa_max.
proc*.
print MLDSA.
transitivity {1} { r <@ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).sign_eager(sk,m, coins); }
    (={sk,m,coins, glob MLDSA_XOFA, glob MLDSA_XOFS, glob MLDSA_XOF_SIB, glob SIB_RO} ==> ={r})
    (   Glob.mem{2} = _m
    /\ sk{1} = BytesSK.of_list (to_list signing_key{2})
    /\ rnd_to_list coins{1} = to_list randomness{2}
    /\ W64.to_uint context{2}.[1] <= 255
    /\ 0 <= message_size{2}
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < W64.modulus
    /\ message_pointer{2} + message_size{2} < W64.modulus
    /\ m{1} = [W8.zero; truncateu8 context{2}.[1]]
              ++ memread _m (W64.to_uint context{2}.[0]) (W64.to_uint context{2}.[1])
              ++ memread _m message_pointer{2} message_size{2}
    /\ valid_s1_bytes (Array640.init (fun i => signing_key{2}.[128 + i]))
    /\ valid_s2_bytes (Array768.init (fun i => signing_key{2}.[768 + i]))
       ==>
       Glob.mem{2} = _m
    /\ (r{1}.`1 = None <=> r{2}.`2 = -W64.one)
    /\ (r{1}.`1 <> None =>
          BytesSig.to_list (oget r{1}.`1) = to_list r{2}.`1 /\
          r{2}.`2 = W64.zero)
    ); 1,2:smt().
+ by call (sign_eager_equiv MLDSA_XOFA MLDSA_XOFS MLDSA_XOF_SIB SIB_RO); auto.
  
call(:  Glob.mem{2} = _m
    /\ sk{1} = BytesSK.of_list (to_list signing_key{2})
    /\ rnd_to_list coins{1} = to_list randomness{2}
    /\ W64.to_uint context{2}.[1] <= 255
    /\ 0 <= message_size{2}
    /\ to_uint context{2}.[0] + to_uint context{2}.[1] < W64.modulus
    /\ message_pointer{2} + message_size{2} < W64.modulus
    /\ m{1} = [W8.zero; truncateu8 context{2}.[1]]
              ++ memread _m (W64.to_uint context{2}.[0]) (W64.to_uint context{2}.[1])
              ++ memread _m message_pointer{2} message_size{2}
    /\ valid_s1_bytes (Array640.init (fun i => signing_key{2}.[128 + i]))
    /\ valid_s2_bytes (Array768.init (fun i => signing_key{2}.[768 + i]))
       ==>
       Glob.mem{2} = _m
    /\ (res{1}.`1 = None <=> res{2}.`2 = -W64.one)
    /\ (res{1}.`1 <> None =>
          BytesSig.to_list (oget res{1}.`1) = to_list res{2}.`1 /\
          res{2}.`2 = W64.zero)
    ); last by auto.
proc => /=.
conseq (: _ ==>
        (zh{1} = None <=> result{2} = - one) /\
  (zh{1} <> None =>
   BytesSig.to_list sigma{1} = to_list signature{2} /\ result{2} = zero)); 1: by smt().
   
(* Jasmin: compute context_pointer and context_size from context array *)
sp 0 2.

(* Jasmin: the context-size guard must hold (given by precondition) *)
rcondt {2} ^if; 1: by auto => /> /#.

(* Inline the Jasmin __sign_internal body *)
inline {2} M.__sign_internal.

sp 0 7.
seq 4 19 : #pre; 1: by auto.

(* ── Step 1: SkDecode (spec only) ────────────────────────────────────────
   Spec: (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk)
   Jasmin: nothing yet (Jasmin decodes each piece separately below) *)
seq 1 0 : (#pre /\
    rho{1} = Bytes32.of_list (take 32 (BytesSK.to_list sk{1})) /\
    _K{1} = Bytes32.of_list (take 32 (drop 32 (BytesSK.to_list sk{1}))) /\
    tr{1} = Bytes64.of_list (take 64 (drop 64 (BytesSK.to_list sk{1}))) /\
    s1{1} = LArray.init (fun i =>
        BitUnpack (take ((n * noise_bits) %/ 8)
                        (drop (128 + i * ((n * noise_bits) %/ 8)) (BytesSK.to_list sk{1})))
                  Eta Eta) /\
    s2{1} = KArray.init (fun i =>
        BitUnpack (take ((n * noise_bits) %/ 8)
                        (drop (128 + s1_bytes + i * ((n * noise_bits) %/ 8)) (BytesSK.to_list sk{1})))
                  Eta Eta) /\
    t0{1} = KArray.init (fun i =>
        BitUnpack (take ((n * d) %/ 8)
                        (drop (128 + s1_bytes + s2_bytes + i * ((n * d) %/ 8)) (BytesSK.to_list sk{1})))
                  (2^(d-1)-1) (2^(d-1))));
   1: by ecall{1} (skDecode_corr sk{1}); auto => |> *; smt().

(* ── Step 3: ExpandA (spec) ~ sample____matrix_A (Jasmin) ───────────────
   Jasmin: matrix_A <@ sample____matrix_A(seed_for_matrix_A) *)
sp;seq 1 1 : (#pre /\
    liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) q).
+ ecall{1} (ExpandA_correct rho{1}).
  ecall{2} (matrix_A_correct seed_for_matrix_A{2}).
  auto => |> &1 &2 H ??????rr  -> Hr;congr; rewrite Bytes32.tP => k kb.
  by rewrite !Bytes32.get_of_list // get_to_list initiE 1:/# /= nth_take 1,2:/# /= BytesSK.get_of_list 1:/# get_to_list.

(* ── Step 4: mu = H_mu tr m (spec simple) ───────────────────────────────
   Spec: mu <- H_mu tr m
   Jasmin: nothing (message representative computed next) *)
sp 1 0.

(* ── Step 5: derive_message_representative (Jasmin) ─────────────────────
   Spec: (mu already assigned above)
   Jasmin: message_representative <@ __derive_message_representative(...) *)
seq 0 1 : (#pre /\
    message_representative{2} =
      Array64.of_list witness (Bytes64.to_list mu{1})).
+ ecall{2} (derive_message_representative_ph
              (Array64.init (fun i => signing_key{2}.[64 + i]))
              (memread _m context_pointer{2} context_size{2})
              (memread _m message_pointer{2} message_size{2})).
  wp; skip => |> &1 &2 *; do split.
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  + rewrite size_memread; smt(W64.to_uint_cmp). 
  move => ????; congr;congr;congr.
  + rewrite Bytes64.tP => k kb.
    by rewrite !Bytes64.get_of_list // get_to_list initiE 1:/# /= nth_take 1,2:/# nth_drop 1,2:/# BytesSK.of_listK ?size_to_list /#.
  by rewrite size_memread; smt(W64.to_uint_cmp). 

(* ── Step 6: rhopp = H_rhopp _K coins mu (spec simple) ─────────────────
   Spec: rhopp <- H_rhopp _K coins mu *)
sp 1 0.

(* ── Step 7: derive_seed_for_mask (Jasmin) ──────────────────────────────
   Spec: (rhopp already assigned above)
   Jasmin: seed_for_mask <@ derive_seed_for_mask(k, randomness, message_representative) *)
seq 0 1 : (#pre /\
    seed_for_mask{2} = Array64.of_list witness (Bytes64.to_list rhopp{1})).
+ ecall{2} (derive_seed_for_mask_ph
              (Array32.init (fun i => signing_key{2}.[32 + i]))
              randomness{2}
              message_representative{2}
              seed_for_mask{2}).
  wp; skip => |> &1 &2 <- *; rewrite /H_rhopp /Hmu.
  rewrite !Bytes64.of_listK ?Keccak1600_Spec.size_SHAKE256 //;1,2: by rewrite size_take // size_drop // BytesSK.size_to_list /#.
  rewrite Bytes32.of_listK; 1: by rewrite size_take // size_drop // BytesSK.size_to_list /#.
  rewrite BytesSK.of_listK; 1: by rewrite size_to_list /#.
  congr;congr;congr.
  + congr;apply (eq_from_nth witness); 1: by rewrite size_to_list // size_take // size_drop // size_to_list /#.
    move => i; rewrite size_to_list /= => ib; rewrite nth_take 1,2:/# initiE 1:/# /= nth_drop /#.
    by rewrite of_listK ?Keccak1600_Spec.size_SHAKE256 //.


(* ── Step 9: Decode s1 (Jasmin) ─────────────────────────────────────────
   Jasmin: s1 <@ s1____decode(signing_key[128:768])
   Spec: (s1 already decoded in Step 1, via skDecode) *)
seq 0 1 : (#pre /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1{1} /\
    wpolylvec_srng (lvec_unflatten256 s1{2}) Eta Eta).
+ ecall{2} (s1_decode_ph (Array640.init (fun i => signing_key{2}.[128 + i]))).
  auto => |> &1 &2 8? rr Hfun Hrng.
  + rewrite Hfun tP => k kb.
    rewrite initiE 1:/# /= mapiE 1:/# /=;do congr.
    apply (eq_from_nth witness).
    + by rewrite size_to_list /= size_take 1:/# size_drop 1:/# BytesSK.size_to_list /#.
    move => i; rewrite size_to_list => ib.
    rewrite get_to_list nth_take 1,2:/# nth_drop 1,2:/#  BytesSK.get_to_list  BytesSK.get_of_list 1:/# get_to_list  initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= initiE /#.
    
(* ── Step 10: Decode s2 (Jasmin) ────────────────────────────────────────
   Jasmin: s2 <@ s2____decode(signing_key[768:1536]) *)
seq 0 1 : (#pre /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2{1} /\
    wpolykvec_srng (kvec_unflatten256 s2{2}) Eta Eta).
+ ecall{2} (s2_decode_ph (Array768.init (fun i => signing_key{2}.[768 + i]))).
  auto => |> &1 &2 10? rr Hfun Hrng.
  + rewrite Hfun tP => k kb.
    rewrite initiE 1:/# /= mapiE 1:/# /=;do congr.
    apply (eq_from_nth witness).
    + by rewrite size_to_list /= size_take 1:/# size_drop 1:/# BytesSK.size_to_list /#.
    move => i; rewrite size_to_list => ib.
    rewrite get_to_list nth_take 1,2:/# nth_drop 1,2:/#  BytesSK.get_to_list  BytesSK.get_of_list 1:/# get_to_list  initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= initiE /#.

   
(* ── Step 11: Decode t0 (Jasmin) ────────────────────────────────────────
   Jasmin: t0 <@ t0__decode(signing_key[1536:4032]) *)
seq 0 1 : (#pre /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0{1} /\
    wpolykvec_srng (kvec_unflatten256 t0{2}) (dpow-1) dpow).
+ ecall{2} (t0_decode_ph (Array2496.init (fun i => signing_key{2}.[1536 + i]))).
  auto => |> &1 &2 12? rr Hfun Hrng.
  + rewrite Hfun tP => k kb.
    rewrite initiE 1:/# /= mapiE 1:/# /=;do congr; last 2 by smt().
    apply (eq_from_nth witness).
    + by rewrite size_to_list /= size_take 1:/# size_drop 1:/# BytesSK.size_to_list /#.
    move => i; rewrite size_to_list => ib.
    rewrite get_to_list nth_take 1,2:/# nth_drop 1,2:/#  BytesSK.get_to_list  BytesSK.get_of_list 1:/# get_to_list  initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= initiE /#.
    
(* ── Step 12: NTT s1/s2/t0 + loop variable inits ───────────────────────
   Jasmin: row_vector__ntt(s1); column_vector__ntt(s2); column_vector__ntt(t0)
           domain_separator_for_mask <- 0
           exit_rejection_sampling_loop <- 0
           kappa_exceeded <- 0
   Spec: (kappa <- 0, zh <- None already done; s1h/s2h/t0h from Step 2 above)
   FIXME: NTT bridge lemmas are not yet proven. *)
seq 0 3 : (#{/~s1{2}}{/~s2{2}}{/~t0{2}}pre /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    wpolylvec_ntt_orng (lvec_unflatten256 s1{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 s2{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 t0{2})).
+ wp; ecall{2} (column_vector__ntt_ph t0{2}).
  wp; ecall{2} (column_vector__ntt_ph s2{2}).
  wp; ecall{2} (row_vector__ntt_ph s1{2}).
  auto => |> &1 &2 *.
  split; first by apply wpolylvec_srng_ntt_irng;
    apply (wpolylvec_srng_widen _ Eta Eta (q-1) (q-1)); smt(mldsa65_Eta).
  move => _ result Hs1_lift Hs1_orng.
  split; first by apply wpolykvec_srng_ntt_irng;
    apply (wpolykvec_srng_widen _ Eta Eta (q-1) (q-1)); smt(mldsa65_Eta).
  move => _ result0 Hs2_lift Hs2_orng.
  split; first by apply wpolykvec_srng_ntt_irng;
    apply (wpolykvec_srng_widen _ (dpow-1) dpow (q-1) (q-1)); smt().
  move => _ result1 Ht0_lift Ht0_orng.
  by rewrite Hs1_lift Hs2_lift Ht0_lift /#.

(* ── Rejection sampling loop + post-loop ──────────────────────────────── *)

seq 3 5 : (
liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) q /\
    seed_for_mask{2} = Array64.of_list witness (Bytes64.to_list rhopp{1}) /\
    message_representative{2} = Array64.of_list witness (Bytes64.to_list mu{1}) /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    wpolylvec_ntt_orng (lvec_unflatten256 s1{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 s2{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 t0{2}) /\
    W16.to_uint domain_separator_for_mask{2} = kappa{1} * lvec /\
    (kappa_exceeded{2} = one) = (kappa_max <= kappa{1}) /\
    (kappa_exceeded{2} <> one => kappa_exceeded{2} = zero) /\
    (exit_rejection_sampling_loop{2} = zero) = (zh{1} = None /\ ! (kappa_max <= kappa{1})) /\
    (zh{1} = None => (kappa_max <= kappa{1})) /\
    (zh{1} <> None => last_norm_check_result{2} = W64.zero) /\
    (zh{1} = None /\ kappa_max <= kappa{1} => last_norm_check_result{2} = W64.one) /\
    (zh{1} <> None =>
       (ct{1} = BytesCT.init (fun i => commitment_hash{2}.[i]) /\
       lifts_wpolylvec (lvec_unflatten256 signer_response{2}) =  (oget zh{1}).`1 /\
       liftu_wpolykvec (kvec_unflatten256 hint_0{2}) = (oget zh{1}).`2 /\
       wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec (liftu_wpolykvec (kvec_unflatten256 hint_0{2})) <= w_hint /\
       wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1-1) gamma1))
); last first.
(* ── Post-loop goal ─────────────────────────────────────────────────── *)
+ if {1}; last first.
  (* failure: zh = None /\ kappa_max <= kappa, so last_norm_check_result = W64.one *)
  + wp; call {2} (: true ==> true).
    + exact signature____encode_ll.
    auto => |> &1 &2 *.
    have -> : last_norm_check_result{2} = W64.one by smt().
    rewrite wordP => i ib.
    by rewrite minus_one /= /(`<<`) /(`|>>`) /= ib /= sarE initiE 1:/# /= nth_one /#.
  (* success: zh <> None, so last_norm_check_result = W64.zero *)
  wp; ecall (signature_encode commitment_hash{2} signer_response{2} hint_0{2}).
  auto => |> &1 &2 ?????????????; do split; 1..6:smt().
  + move => ?????? rr1 rr2 ?.
    have -> : last_norm_check_result{2} = W64.zero by smt().
    split; 1: by rewrite wordP /= minus_one /= /(`<<`) /(`|>>`) /= sarE negb_forall; exists 0 => /=.
    rewrite wordP => i ib.
    by rewrite  /(`<<`) /(`|>>`) /= sarE initiE 1:/# /=. 
     

(* ── Rejection sampling loop  ──────────────────────────────── *)

while (
    liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) q /\
    seed_for_mask{2} = Array64.of_list witness (Bytes64.to_list rhopp{1}) /\
    message_representative{2} = Array64.of_list witness (Bytes64.to_list mu{1}) /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    wpolylvec_ntt_orng (lvec_unflatten256 s1{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 s2{2}) /\
    wpolykvec_ntt_orng (kvec_unflatten256 t0{2}) /\
    W16.to_uint domain_separator_for_mask{2} = kappa{1} * lvec /\
    (kappa_exceeded{2} = W64.of_int 1) = (kappa_max <= kappa{1}) /\
    (kappa_exceeded{2} <> W64.of_int 1 => kappa_exceeded{2} = W64.zero) /\
    (exit_rejection_sampling_loop{2} = W64.of_int 0) =
      (zh{1} = None /\ ! (kappa_max <= kappa{1})) /\
    (zh{1} <> None => last_norm_check_result{2} = W64.zero) /\
    (zh{1} = None /\ kappa_max <= kappa{1} => last_norm_check_result{2} = W64.one) /\
    (zh{1} <> None =>
       ct{1} = BytesCT.init (fun i => commitment_hash{2}.[i]) /\
       lifts_wpolylvec (lvec_unflatten256 signer_response{2}) = (oget zh{1}).`1 /\
       liftu_wpolykvec (kvec_unflatten256 hint_0{2}) = (oget zh{1}).`2 /\
       wpolykvec_urng (kvec_unflatten256 hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec (liftu_wpolykvec (kvec_unflatten256 hint_0{2})) <= w_hint /\
       wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1-1) gamma1)); last
         by auto => |>  &1 &2 *; rewrite !W64.to_uint_eq /=; do split;smt().

 (* ── Loop body ──────────────────────────────────────────────────────── *)
 seq 1 1 : (#pre /\
     lifts_wpolylvec (lvec_unflatten256 mask{2}) = y{1} /\
     wpolylvec_srng (lvec_unflatten256 mask{2}) (gamma1 - 1) gamma1 /\
     W16.to_uint domain_separator_for_mask{2} = (kappa{1} + 1) * lvec).
 + admit. (* ExpandMask bridge + circuit *)

 sp 3 0.
 seq 0 8 : (#pre /\
     lifts_wpolykvec (kvec_unflatten256 w0{2}) = w0{1} /\
     lifts_wpolykvec (kvec_unflatten256 w1{2}) = w1{1} /\
     wpolykvec_srng (kvec_unflatten256 w0{2}) (gamma2 - 1) gamma2 /\
     wpolykvec_urng (kvec_unflatten256 w1{2}) ((q-1) %/ (2*gamma2))).
 + (* Jasmin stmt 1-2: j <- 0; while loop copies mask into mask_as_ntt.
      Narrow admit: just the fact that after the copy loop, mask_as_ntt = mask. *)
   seq 0 2 : (#pre /\ mask_as_ntt{2} = mask{2}).
   + admit. (* circuit-level copy loop mask_as_ntt := mask *)
   (* Jasmin stmts 3-8: row_vector__ntt; multiply_with_matrix_A; reduce32;
      invert_ntt_montgomery; conditionally_add_modulus; decompose. *)
   wp; ecall{2} (column_vector____decompose_ph w{2}).
   wp; ecall{2} (column_vector____conditionally_add_modulus_ph w{2}).
   wp; ecall{2} (column_vector__invert_ntt_montgomery_ph w{2}).
   wp; ecall{2} (column_vector__reduce32_ph w{2}).
   wp; ecall{2} (row_vector____multiply_with_matrix_A_ph matrix_A{2} mask_as_ntt{2}).
   wp; ecall{2} (row_vector__ntt_ph mask_as_ntt{2}).
   auto => |> &1 &2 *.
   have Hbound := invntt_obound_fits_for_caddq.
   have HA_lift : liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} by smt().
   have Hmask_lift : lifts_wpolylvec (lvec_unflatten256 mask{2}) = y{1} by smt().
   split; first by apply wpolylvec_srng_ntt_irng;
     apply (wpolylvec_srng_widen _ (gamma1-1) gamma1 (q-1) (q-1)); smt(mldsa65_gamma1).
   move => _ result Hntt_eq Hntt_orng.
   split; first exact (wpolylvec_ntt_orng_bmul_irng _ Hntt_orng).
   move => _ result0 Hmul_eq Hmul_srng.
   move => result1 Hred_eq Hred_srng.
   split; first by apply wpolykvec_bmul_orng_intt_irng;
     apply (wpolykvec_srng_widen _ ((q-1) %/ 2) ((q-1) %/ 2) (q-1) (q-1)); smt().
   move => _ result2 Hinvntt_eq Hinvntt_srng.
   split;
     first by apply (wpolykvec_srng_widen _ invntt_obound invntt_obound (q-1) (q-1)); smt().
   move => _ result3 Hcond_eq Hcond_urng.
   move => result4 Hw0_eq Hw1_eq Hw0_srng Hw1_urng.
   have Hreachable : lifts_wpolykvec (kvec_unflatten256 result3) =
                     invnttv (ntt_mulmxv _A{1} (nttv y{1})).
   + by rewrite Hcond_eq Hinvntt_eq Hred_eq Hmul_eq Hntt_eq Hmask_lift HA_lift.
   have Heq_liftu_lifts := wpolykvec_urng_lifts_eq_liftu _ Hcond_urng.
   have Hw1_lifts : lifts_wpolykvec (kvec_unflatten256 result4.`2) =
                    liftu_wpolykvec (kvec_unflatten256 result4.`2).
   + apply wpolykvec_urng_lifts_eq_liftu;
     apply (wpolykvec_urng_widen _ ((q-1) %/ (2*gamma2)) q); smt(mldsa65_gamma2).
   by rewrite Hw0_eq Hw1_lifts Hw1_eq -Heq_liftu_lifts Hreachable HA_lift Hmask_lift /#.

 seq 3 3 : (#pre /\
     ct{1} = BytesCT.init (fun i => commitment_hash{2}.[i]) /\
     lifts_wpoly verifier_challenge{2} = c{1} /\
     wpoly_ntt_irng verifier_challenge{2}).
 + admit. (* commitment hash + SampleInBall bridge *)

sp 6 0; seq 1 0 : #pre; 1: by auto.

 seq 0 1 : (#pre /\
     wpoly_ntt_orng verifier_challenge{2} /\
     lifts_wpoly verifier_challenge{2} = ch{1}).
 + ecall{2} (polynomial__ntt_ph verifier_challenge{2}).
   by auto => |> /#.

 (* Jasmin pure: infinity_norm_check_result <- 0 *)
 sp 0 1.

 (* ── Step 1: cs2 norm check ──────────────────────────────── *)
 seq 0 1 : (#pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (infinity_norm_check_result{2} = W64.zero =>
        wpolykvec_infnorm_lt (gamma2 - Beta) (kvec_unflatten256 w0_minus_cs2{2}) /\
        lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2{2}) =
          lifts_wpolykvec (kvec_unflatten256 w0{2}) -
          PolyKVec.invnttv (PolyKVec.ntt_smul
            (lifts_wpoly verifier_challenge{2})
            (lifts_wpolykvec (kvec_unflatten256 s2{2}))))).
 + ecall{2} (__apply_cs2_and_check_norm_ph
              w0_minus_cs2{2} w0{2} s2{2} verifier_challenge{2}
              W64.zero).
   by auto => |> &1 &2 *; smt().

 (* ── Step 2: ct0 norm check ──────────────────────────────── *)
 seq 0 1 : (#pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (infinity_norm_check_result{2} = W64.zero =>
        let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                    (lifts_wpoly verifier_challenge{2})
                    (lifts_wpolykvec (kvec_unflatten256 t0{2}))) in
        PolyKVec.infnorm_lt ct0 gamma2 /\
        lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0{2}) =
          lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2{2}) + ct0)).
 + ecall{2} (__apply_ct0_and_check_norm_ph
              w0_minus_cs2_plus_ct0{2} w0_minus_cs2{2} t0{2}
              verifier_challenge{2} infinity_norm_check_result{2}).
   by auto => |> &1 &2 *; smt().

 (* ── Step 3: z norm check ──────────────────────────────── *)
 seq 0 2 : (#pre /\
     (infinity_norm_check_result{2} = W64.zero \/ infinity_norm_check_result{2} = W64.one) /\
     (infinity_norm_check_result{2} = W64.zero =>
        wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response{2}) /\
        lifts_wpolylvec (lvec_unflatten256 signer_response{2}) =
          lifts_wpolylvec (lvec_unflatten256 mask{2}) +
          PolyLVec.invnttv (PolyLVec.ntt_smul
            (lifts_wpoly verifier_challenge{2})
            (lifts_wpolylvec (lvec_unflatten256 s1{2}))) /\
        wpolylvec_srng (lvec_unflatten256 signer_response{2}) (gamma1 - 1) gamma1)).
 + wp. ecall{2} (__compute_z_and_check_norm_ph
              s1{2} verifier_challenge{2} mask{2} signer_response{2}
              infinity_norm_check_result{2}).
   by auto => |> &1 &2 *; smt().

 (* ── Step 4: make_hint + while invariant ──────────────────── *)
 (* Remaining program: w0mc no-op + make_hint ecall + post-loop kappa/exit.
    The seq postconditions carry enough info for smt to close. *)
 wp.
 ecall{2} (__make_hint_vector_ph
              w0_minus_cs2_plus_ct0{2} w1{2} hint_0{2}
              infinity_norm_check_result{2}).
 by auto => |> &1 &2 *; smt().
qed.
