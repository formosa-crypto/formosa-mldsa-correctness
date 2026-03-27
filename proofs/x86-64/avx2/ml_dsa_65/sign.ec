require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge Row_vector S1 S2 T0 Mask.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

require import Array2 Array32 Array48 Array64 Array128 Array256
               Array640 Array768 Array1280 Array1536 Array2496
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
   the Jasmin result code is 0 (success). *)

lemma ml_dsa_65_sign_correct _m :
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
    /\ BytesSig.to_list res{1}.`1 = to_list res{2}.`1
    /\ res{2}.`2 = W64.of_int 0
    ].
proof.
have Hlvec   := mldsa65_lvec.
have Hkvec   := mldsa65_kvec.
have HEta    := mldsa65_Eta.
have Hgamma1 := mldsa65_gamma1.
have Htau    := mldsa65_tau.

proc => /=; conseq |>.

(* Jasmin: compute context_pointer and context_size from context array *)
sp 0 2.

(* Jasmin: the context-size guard must hold (given by precondition) *)
rcondt {2} ^if; 1: by auto => /> /#.

(* Inline the Jasmin __sign_internal body *)
inline {2} M.__sign_internal.

sp 0 7.
seq 2 19 : #pre;1: by auto.
sp 1 1.

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
                  (2^(d-1)-1) (2^(d-1)))); 1: by  ecall{1} (skDecode_corr sk{1}); auto => |> /#.

sp 3 0.
 seq 1 1 : (#pre /\
    liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
    wpolymat_urng (mat_unflatten256 matrix_A{2}) 1).
+ ecall{1} (ExpandA_correct rho{1}).
  ecall{2} (matrix_A_correct (Array32.init (fun i => signing_key{2}.[0 + i]))).
  auto => |> &1 &2 Hrnd ???? rr -> ?;congr;rewrite Bytes32.tP => k kb.
  by rewrite !Bytes32.get_of_list // get_to_list initiE 1:/# nth_take 1,2:/# BytesSK.of_listK ?size_to_list /#.

sp 1 0.
seq 0 1 : (#pre /\
    message_representative{2} =
      Array64.of_list witness (Bytes64.to_list mu{1})).
+ ecall{2} (derive_message_representative_ph
              (Array64.init (fun i => signing_key{2}.[64 + i]))
              (memread _m context_pointer{2} context_size{2})
              (memread _m message_pointer{2} message_size{2})).
  wp; skip => |> &1 &2 *; do split.
  + by rewrite size_memread; smt(W64.to_uint_cmp).
  + by rewrite size_memread; smt(W64.to_uint_cmp).
  + by rewrite size_memread; smt(W64.to_uint_cmp).
  + by rewrite size_memread; smt(W64.to_uint_cmp).
  move => ????; congr;congr;congr.
  + rewrite Bytes64.tP => k kb. 
    by rewrite !Bytes64.get_of_list // get_to_list initiE 1:/# /= nth_take 1,2:/# nth_drop 1,2:/# BytesSK.of_listK ?size_to_list /#.
    by rewrite size_memread /=;1:smt(W64.to_uint_cmp).

    
sp 1 0.
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
  
(* ── Step 5: Decode s1 (Jasmin) ──────────────────────────────────────────
   Spec: (s1 already decoded in Step 1, via skDecode)
   Jasmin: s1 <@ s1____decode(signing_key[128:768]) *)
seq 0 1 : (#pre /\
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1{1} /\
    wpolylvec_srng (lvec_unflatten256 s1{2}) Eta Eta).
+ ecall{2} (s1_decode_ph (Array640.init (fun i => signing_key{2}.[128 + i]))).
  auto => |> &2 * [Hfun Hrng].
  split.
  + (* FIXME: connect s1{1} (BitUnpack of skDecode output) to s1_decode_ph output *)
    admit.
  + exact Hrng.

(* ── Step 6: Decode s2 (Jasmin) ──────────────────────────────────────────
   Jasmin: s2 <@ s2____decode(signing_key[768:1536]) *)
seq 0 1 : (#pre /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2{1} /\
    wpolykvec_srng (kvec_unflatten256 s2{2}) Eta Eta).
+ ecall{2} (s2_decode_ph (Array768.init (fun i => signing_key{2}.[768 + i]))).
  auto => |> &2 * [Hfun Hrng].
  split.
  + admit. (* FIXME: same functional connection as s1 *)
  + exact Hrng.

(* ── Step 7: Decode t0 (Jasmin) ──────────────────────────────────────────
   Jasmin: t0 <@ t0__decode(signing_key[1536:4032]) *)
seq 0 1 : (#pre /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0{1} /\
    wpolykvec_srng (kvec_unflatten256 t0{2}) (dpow-1) dpow).
+ ecall{2} (t0_decode_ph (Array2496.init (fun i => signing_key{2}.[1536 + i]))).
  auto => |> &2 * [Hfun Hrng].
  split.
  + admit. (* FIXME: t0 functional connection *)
  + exact Hrng.

(* ── Step 8: NTT s1/s2/t0 (Jasmin), kappa/zh/exit_flag init ─────────────
   Jasmin: row_vector__ntt(s1); column_vector__ntt(s2); column_vector__ntt(t0)
   Spec: kappa <- 0; zh <- None (the spec NTTs were already done in Step 2)
   FIXME: NTT bridge lemmas for polylvec/polykvec are not yet proven.
   We admit this step and assert the invariant directly. *)
seq 2 5 : (#pre /\
    (* Jasmin s1/s2/t0 are now NTT-domain representations matching s1h/s2h/t0h *)
    lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1h{1} /\
    lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2h{1} /\
    lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0h{1} /\
    (* Loop initialization *)
    kappa{1} = 0 /\
    zh{1} = None /\
    W16.to_uint domain_separator_for_mask{2} = 0 /\
    exit_rejection_sampling_loop{2} = W8.of_int 0).
+ admit. (* FIXME:
    - NTT bridge: need equiv between row_vector__ntt ~ nttv and column_vector__ntt ~ nttv
    - Pure assigns: kappa <- 0, zh <- None (spec) and domain_sep/exit_flag inits (Jasmin) *)

(* ── Step 9: Rejection-sampling while loop + sigEncode ──────────────────
   This is the main novelty vs. keygen/verify: a rejection-sampling loop.

   Loop invariant (informally):
     kappa{1} = W16.to_uint domain_separator_for_mask{2}
     /\ (zh{1} = None <=> exit_rejection_sampling_loop{2} <> W8.of_int 1)
     /\ seed_for_mask{2}, matrix_A, s1h/s2h/t0h, rho, mu, rhopp are stable
     /\ Glob.mem{2} = _m (memory unchanged throughout)

   Loop body at each iteration:
     - ExpandMask ~ sample____mask  (mask_correct)
     - w = Ay (polynomial multiply + reduce): ADMIT
     - decompose into w0/w1: ADMIT
     - w1Encode ~ commitment____encode: ADMIT
     - H_ct ~ derive_commitment_hash_ph
     - SampleInBall ~ sample____challenge  (sample_challenge_correct)
     - z = y + c*s1, check ||z|| < gamma1 - beta: ADMIT
     - r0 = w0 - c*s2, check ||r0|| < gamma2 - beta: ADMIT
     - ct0 = c*t0, check ||ct0|| < gamma2: ADMIT
     - MakeHint, check hammw <= w_hint: ADMIT
     - acceptance check sets exit_flag / updates zh

   Post-loop (using signature_encode):
     - ecall (signature_encode commitment_hash{2} signer_response{2} hint_0{2})
     - Requires: ct, mods z q, h connected between spec and Jasmin *)
admit. (* FIXME: loop + sigEncode *)

qed.
