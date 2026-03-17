require import AllCore IntDiv List.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat Symmetric Sampling MLDSA_W32_Rep MLDSA.
import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

require import Array2 Array26 Array32 Array48 Array64 Array66 Array128 Array136 Array768 Array1952.
require import WArray2 Array7 WArray32 WArray48 WArray64 WArray66 WArray128 WArray136 WArray208 WArray768 WArray1952.
from CryptoSpecs require import JWordList.

(****************************************************************************)
(* Establish that M's keccak primitives equal Keccak1600_Jazz.M             *)
(****************************************************************************)

from Keccak require import Keccak1600_avx2.
from Keccak require import Keccakf1600_avx2.

equiv state_init_avx2_eq:
 M.__state_init_avx2 ~ Keccak1600_Jazz.M.__state_init_avx2
 : ={arg} ==> ={res}
 by sim.

equiv keccakf1600_avx2_eq:
 M._keccakf1600_avx2 ~ Keccak1600_Jazz.M._keccakf1600_avx2
 : ={arg} ==> ={res}
 by sim.

equiv keccakf1600_st25_avx2_eq:
 M._keccakf1600_st25_avx2 ~ Keccak1600_Jazz.M._keccakf1600_st25_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(* Clone KeccakArrayAvx2 for each array size used in hashing.jinc           *)
(****************************************************************************)

from Keccak require import Keccak1600_fixedsizes_avx2.

clone KeccakArrayAvx2 as A2avx2
 with op _ASIZE <- 2,
      theory A <- Array2,
      theory WA <- WArray2
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A32avx2
 with op _ASIZE <- 32,
      theory A <- Array32,
      theory WA <- WArray32
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A48avx2
 with op _ASIZE <- 48,
      theory A <- Array48,
      theory WA <- WArray48
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A64avx2
 with op _ASIZE <- 64,
      theory A <- Array64,
      theory WA <- WArray64
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A128avx2
 with op _ASIZE <- 128,
      theory A <- Array128,
      theory WA <- WArray128
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A136avx2
 with op _ASIZE <- 136,
      theory A <- Array136,
      theory WA <- WArray136
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A768avx2
 with op _ASIZE <- 768,
      theory A <- Array768,
      theory WA <- WArray768
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

clone KeccakArrayAvx2 as A1952avx2
 with op _ASIZE <- 1952,
      theory A <- Array1952,
      theory WA <- WArray1952
      proof _ASIZE_ge0 by done
      proof _ASIZE_u64 by done.

(****************************************************************************)
(* Equiv lemmas: M.primitive ~ KeccakArray.MM.primitive                     *)
(****************************************************************************)

equiv a2__absorb_avx2_eq:
 M.a2____absorb_avx2 ~ A2avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a32__absorb_avx2_eq:
 M.a32____absorb_avx2 ~ A32avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a_COMMITMENT_HASH__absorb_avx2_eq:
 M.a_COMMITMENT_HASH____absorb_avx2 ~ A48avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a_COMMITMENT_HASH__dumpstate_avx2_eq:
 M.a_COMMITMENT_HASH____dumpstate_avx2 ~ A48avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a64__absorb_avx2_eq:
 M.a64____absorb_avx2 ~ A64avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a64__dumpstate_avx2_eq:
 M.a64____dumpstate_avx2 ~ A64avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a128__absorb_avx2_eq:
 M.a128____absorb_avx2 ~ A128avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a128__dumpstate_avx2_eq:
 M.a128____dumpstate_avx2 ~ A128avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a136__dumpstate_avx2_eq:
 M.a136____dumpstate_avx2 ~ A136avx2.MM.__dumpstate_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a_ENCODED_COMMITMENT__absorb_avx2_eq:
 M.a_ENCODED_COMMITMENT____absorb_avx2 ~ A768avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}.
 proc. 
by  sim; auto => />.
qed.

equiv a_VERIFICATION_KEY__absorb_avx2_eq:
 M.a_VERIFICATION_KEY____absorb_avx2 ~ A1952avx2.MM.__absorb_avx2
 : ={arg} ==> ={res}.
proc. 
by  sim; auto => />.
qed.

(****************************************************************************)
(* Module K: keccak-library wrapper mirroring M's hashing procedures        *)
(****************************************************************************)

module K = {

  proc shake256_absorb_34 (seed:W8.t Array32.t, extra:W8.t Array2.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    var  _1:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A32avx2.MM.__absorb_avx2 (state, 0, seed, 0, 136);
    (state,  _1) <@ A2avx2.MM.__absorb_avx2 (state, 32, extra, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc shake256_absorb_66 (rho_prime:W8.t Array64.t, domain_separator:W16.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var ds:W8.t Array2.t;
    var  _0:int;
    var  _1:int;
    ds <- witness;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A64avx2.MM.__absorb_avx2 (state, 0, rho_prime, 0, 136);
    ds <-
    (Array2.init
    (WArray2.get8
    (WArray2.set16 (WArray2.init8 (fun i => ds.[i])) 0 domain_separator)));
    (state,  _1) <@ A2avx2.MM.__absorb_avx2 (state, 64, ds, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc shake256_absorb_128 (block:W8.t Array128.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A128avx2.MM.__absorb_avx2 (state, 0, block, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc shake256_absorb_commitment_hash (hash:W8.t Array48.t) :
  W256.t Array7.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A48avx2.MM.__absorb_avx2 (state, 0, hash, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    return state;
  }

  proc squeeze_128_bytes (array:W8.t Array128.t, state:W256.t Array7.t) :
  W8.t Array128.t = {
    var  _0:int;
    (array,  _0) <@ A128avx2.MM.__dumpstate_avx2 (array, 0, 128, state);
    return array;
  }

  proc shake256_squeeze_block (block:W8.t Array136.t, state:W256.t Array7.t) :
  W8.t Array136.t = {
    var  _0:int;
    (block,  _0) <@ A136avx2.MM.__dumpstate_avx2 (block, 0, 136, state);
    return block;
  }

  proc squeeze_64_bytes (array:W8.t Array64.t, state:W256.t Array7.t) :
  W8.t Array64.t = {
    var  _0:int;
    (array,  _0) <@ A64avx2.MM.__dumpstate_avx2 (array, 0, 64, state);
    return array;
  }

  proc squeeze_commitment_hash_bytes (array:W8.t Array48.t, state:W256.t Array7.t) :
  W8.t Array48.t = {
    var  _0:int;
    (array,  _0) <@ A48avx2.MM.__dumpstate_avx2 (array, 0, 48, state);
    return array;
  }

  proc hash_verification_key (verification_key_hash:W8.t Array64.t,
                              verification_key:W8.t Array1952.t) :
  W8.t Array64.t = {
    var state:W256.t Array7.t;
    var  _0:int;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A1952avx2.MM.__absorb_avx2 (state, 0, verification_key, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    (verification_key_hash,  _0) <@ A64avx2.MM.__dumpstate_avx2 (
    verification_key_hash, 0, 64, state);
    return verification_key_hash;
  }

  proc __derive_commitment_hash (message_representative:W8.t Array64.t,
                                 encoded_commitment:W8.t Array768.t) :
  W8.t Array48.t = {
    var commitment_hash:W8.t Array48.t;
    var state:W256.t Array7.t;
    var  _0:int;
    var  _1:int;
    commitment_hash <- witness;
    state <- witness;
    state <@ Keccak1600_Jazz.M.__state_init_avx2 ();
    (state,  _0) <@ A64avx2.MM.__absorb_avx2 (state, 0, message_representative, 0, 136);
    (state,  _1) <@ A768avx2.MM.__absorb_avx2 (state, 64, encoded_commitment, 31, 136);
    state <@ Keccak1600_Jazz.M._keccakf1600_avx2 (state);
    (commitment_hash,  _0) <@ A48avx2.MM.__dumpstate_avx2 (commitment_hash, 0, 48, state);
    return commitment_hash;
  }

  (* __derive_message_representative uses the streaming updstate interface
     (variable-length absorb via memory pointers). No abstract EC theory exists
     for updstate in formosa-keccak yet, so K mirrors M exactly — calling M's
     own updstate sub-procedures. The M ~ K equiv is by sim (identical call
     structure). The leaf-level keccakf1600_st25 connection to Keccak1600_Jazz
     is established by keccakf1600_st25_avx2_eq above. *)
  proc __derive_message_representative (verification_key_hash:W8.t Array64.t,
                                        context_pointer:int, context_size:int,
                                        message_pointer:int, message_size:int) :
  W8.t Array64.t = {
    var message_representative:W8.t Array64.t;
    var copied_32_bytes:W256.t;
    var prefix:W8.t Array66.t;
    var state:W64.t Array26.t;
    var buf:int;
    var len:int;
    message_representative <- witness;
    prefix <- witness;
    state <- witness;
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => verification_key_hash.[i])) 0);
    prefix <-
    (Array66.init
    (WArray66.get8
    (WArray66.set256_direct (WArray66.init8 (fun i => prefix.[i])) 0
    copied_32_bytes)));
    copied_32_bytes <-
    (get256_direct (WArray64.init8 (fun i => verification_key_hash.[i])) 32);
    prefix <-
    (Array66.init
    (WArray66.get8
    (WArray66.set256_direct (WArray66.init8 (fun i => prefix.[i])) 32
    copied_32_bytes)));
    prefix.[64] <- (W8.of_int 0);
    prefix.[65] <- (truncateu8 (W64.of_int context_size));
    state <@ M._init_updstate_avx2 (state, 17, 31);
    state <@ M.a66___update_updstate_avx2 (state, prefix);
    buf <- context_pointer;
    len <- context_size;
    state <@ M._absorb_m_updstate_avx2 (state, buf, len);
    buf <- message_pointer;
    len <- message_size;
    state <@ M._absorb_m_updstate_avx2 (state, buf, len);
    state <@ M._finish_updstate_avx2 (state);
    (state, message_representative) <@ M.a64___squeeze_updstate_avx2 (state,
    message_representative);
    return message_representative;
  }

}.

(****************************************************************************)
(* Equiv lemmas: M.proc ~ K.proc                                            *)
(****************************************************************************)

equiv shake256_absorb_34_eq:
 M.shake256_absorb_34 ~ K.shake256_absorb_34
 : ={arg} ==> ={res}.
  proc. 
by inline *;sim; auto => />.
qed.


equiv shake256_absorb_66_eq:
 M.shake256_absorb_66 ~ K.shake256_absorb_66
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv shake256_absorb_128_eq:
 M.shake256_absorb_128 ~ K.shake256_absorb_128
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv shake256_absorb_commitment_hash_eq:
 M.shake256_absorb_commitment_hash ~ K.shake256_absorb_commitment_hash
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv squeeze_128_bytes_eq:
 M.squeeze_128_bytes ~ K.squeeze_128_bytes
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv shake256_squeeze_block_eq:
 M.shake256_squeeze_block ~ K.shake256_squeeze_block
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv squeeze_64_bytes_eq:
 M.squeeze_64_bytes ~ K.squeeze_64_bytes
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv squeeze_commitment_hash_bytes_eq:
 M.squeeze_commitment_hash_bytes ~ K.squeeze_commitment_hash_bytes
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />.
qed.

equiv hash_verification_key_eq:
 M.hash_verification_key ~ K.hash_verification_key
 : ={arg} ==> ={res}.
 proc. 
by inline *;sim; auto => />;sim.
qed.

equiv derive_commitment_hash_eq:
 M.__derive_commitment_hash ~ K.__derive_commitment_hash
 : ={arg} ==> ={res}.
proc. 
seq 4 4 : (={encoded_commitment,state,commitment_hash}); 1: by inline *;sim.
seq 1 1 : (={encoded_commitment,state,commitment_hash}); 2: by inline *;sim.
inline {1} 1; inline {2} 1.
by sim; auto => />.
qed.

equiv derive_message_representative_eq:
 M.__derive_message_representative ~ K.__derive_message_representative
 : ={arg, Glob.mem} ==> ={res, Glob.mem}
 by sim.

(****************************************************************************)
(* Correctness lemmas (absorbed-state characterization)                     *)
(****************************************************************************)

hoare shake256_absorb_34_h' _seed _extra :
 K.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _seed ++ to_list _extra))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A2avx2.absorb_avx2_h (to_list seed) extra 31 136).
wp; ecall (A32avx2.absorb_avx2_h [<:W8.t>] seed 0 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2] ??; split; 1: by smt(Array32.size_to_list).
move => ? [st2 x3] /= -> /=; split; 1: by rewrite /absorb_spec_avx2  stavx2_from_st25K.
by move => ->; rewrite !stavx2_from_st25K.
qed.

lemma shake256_absorb_34_ll: islossless K.shake256_absorb_34.
proof.
proc.
call keccakf1600_avx2_ll.
call A2avx2.absorb_avx2_ll.
call A32avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_34_ph' _seed _extra :
 [ K.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _seed ++ to_list _extra)))
 ] = 1%r.
proof.
by conseq shake256_absorb_34_ll (shake256_absorb_34_h' _seed _extra).
qed.

phoare shake256_absorb_34_ph _seed _extra :
 [ M.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _seed ++ to_list _extra)))
 ] = 1%r.
proof.
by conseq shake256_absorb_34_eq (shake256_absorb_34_ph' _seed _extra) => // /#.
qed.

(* ---------- shake256_absorb_66 ---------- *)

hoare shake256_absorb_66_h' _rho_prime _ds :
 K.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136
      (to_list _rho_prime ++ to_list _ds))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A2avx2.absorb_avx2_h (to_list rho_prime) ds 31 136).
wp.
ecall (A64avx2.absorb_avx2_h [<:W8.t>] rho_prime 0 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2] ??; split; 1: by smt(Array64.size_to_list).
move => ? [st2 x3] /= -> /=; split; 1: by rewrite /absorb_spec_avx2 stavx2_from_st25K.
move => ->; rewrite !stavx2_from_st25K /=;do !congr.
apply (eq_from_nth witness); 1: by rewrite size_to_list /=.
move => i; rewrite size_to_list /= => ib.
by rewrite initiE 1:/# get8_set16_directE //= /#.
qed.

lemma shake256_absorb_66_ll: islossless K.shake256_absorb_66.
proof.
proc.
call keccakf1600_avx2_ll.
call A2avx2.absorb_avx2_ll.
wp.
call A64avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_66_ph' _rho_prime _ds :
 [ K.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136
      (to_list _rho_prime ++ to_list _ds)))
 ] = 1%r.
proof.
by conseq shake256_absorb_66_ll (shake256_absorb_66_h' _rho_prime _ds).
qed.

phoare shake256_absorb_66_ph _rho_prime _ds :
 [ M.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136
      (to_list _rho_prime ++ to_list _ds)))
 ] = 1%r.
proof.
by conseq shake256_absorb_66_eq (shake256_absorb_66_ph' _rho_prime _ds) => // /#.
qed.

(* ---------- shake256_absorb_128 ---------- *)

hoare shake256_absorb_128_h' _block :
 K.shake256_absorb_128
 : arg = _block
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _block))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A128avx2.absorb_avx2_h [<:W8.t>] block 31 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2]; rewrite /absorb_spec_avx2  => H; split; 1: by rewrite stavx2_to_st25K /=; smt( stavx2INV_from_st25).
by move => /= ->; rewrite H !stavx2_from_st25K.
qed.

lemma shake256_absorb_128_ll: islossless K.shake256_absorb_128.
proof.
proc.
call keccakf1600_avx2_ll.
call A128avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_128_ph' _block :
 [ K.shake256_absorb_128
 : arg = _block
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _block)))
 ] = 1%r.
proof.
by conseq shake256_absorb_128_ll (shake256_absorb_128_h' _block).
qed.

phoare shake256_absorb_128_ph _block :
 [ M.shake256_absorb_128
 : arg = _block
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _block)))
 ] = 1%r.
proof.
by conseq shake256_absorb_128_eq (shake256_absorb_128_ph' _block) => // /#.
qed.

(* ---------- shake256_absorb_commitment_hash ---------- *)

hoare shake256_absorb_commitment_hash_h' _hash :
 K.shake256_absorb_commitment_hash
 : arg = _hash
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _hash))).
proof.
proc.
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A48avx2.absorb_avx2_h [<:W8.t>] hash 31 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x2]; rewrite /absorb_spec_avx2 => H; split; 1: by rewrite stavx2_to_st25K /=; smt(stavx2INV_from_st25).
by move => /= ->; rewrite H !stavx2_from_st25K.
qed.

lemma shake256_absorb_commitment_hash_ll: islossless K.shake256_absorb_commitment_hash.
proof.
proc.
call keccakf1600_avx2_ll.
call A48avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare shake256_absorb_commitment_hash_ph' _hash :
 [ K.shake256_absorb_commitment_hash
 : arg = _hash
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _hash)))
 ] = 1%r.
proof.
by conseq shake256_absorb_commitment_hash_ll (shake256_absorb_commitment_hash_h' _hash).
qed.

phoare shake256_absorb_commitment_hash_ph _hash :
 [ M.shake256_absorb_commitment_hash
 : arg = _hash
 ==> res = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 (to_list _hash)))
 ] = 1%r.
proof.
by conseq shake256_absorb_commitment_hash_eq (shake256_absorb_commitment_hash_ph' _hash) => // /#.
qed.


(****************************************************************************)
(* Correctness lemmas (squeeze operations)                                  *)
(****************************************************************************)

(* ---------- squeeze_64_bytes ---------- *)

hoare squeeze_64_bytes_h' _arr _m :
 K.squeeze_64_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array64.of_list witness (SHAKE256 _m 64).
proof.
proc.
ecall (A64avx2.dumpstate_avx2_h _arr 0 64 state).
auto => |> [rr1 rr2] -> ?.
rewrite stavx2_from_st25K.
apply Array64.tP => i Hi /=.
rewrite Array64.get_of_list 1://.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (64 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE.
qed.

lemma squeeze_64_bytes_ll : islossless K.squeeze_64_bytes.
proof.
proc.
call A64avx2.dumpstate_avx2_ll.
by auto.
qed.

phoare squeeze_64_bytes_ph' _arr _m :
 [ K.squeeze_64_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array64.of_list witness (SHAKE256 _m 64)
 ] = 1%r.
proof.
by conseq squeeze_64_bytes_ll (squeeze_64_bytes_h' _arr _m).
qed.

phoare squeeze_64_bytes_correct _arr _m :
 [ M.squeeze_64_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array64.of_list witness (SHAKE256 _m 64)
 ] = 1%r.
proof.
by conseq squeeze_64_bytes_eq (squeeze_64_bytes_ph' _arr _m) => // /#.
qed.

(* ---------- squeeze_128_bytes ---------- *)

(* Given a state that results from absorbing _m with SHAKE256 padding,
   squeeze_128_bytes produces the first 128 bytes of SHAKE256(_m). *)

hoare squeeze_128_bytes_h' _arr _m :
 K.squeeze_128_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array128.of_list witness (SHAKE256 _m 128).
proof.
proc.
ecall (A128avx2.dumpstate_avx2_h _arr 0 128 state).
auto => |> [rr1 rr2] -> ?.
rewrite stavx2_from_st25K.
apply Array128.tP => i Hi /=.
rewrite Array128.get_of_list 1://.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (128 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE.
qed.

lemma squeeze_128_bytes_ll : islossless K.squeeze_128_bytes.
proof.
proc.
call A128avx2.dumpstate_avx2_ll.
by auto.
qed.

phoare squeeze_128_bytes_ph' _arr _m :
 [ K.squeeze_128_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array128.of_list witness (SHAKE256 _m 128)
 ] = 1%r.
proof.
by conseq squeeze_128_bytes_ll (squeeze_128_bytes_h' _arr _m).
qed.

phoare squeeze_128_bytes_correct _arr _m :
 [ M.squeeze_128_bytes
 : arg.`1 = _arr /\ arg.`2 = stavx2_from_st25 (keccak_f1600_op (ABSORB1600 (W8.of_int 31) 136 _m))
 ==> res = Array128.of_list witness (SHAKE256 _m 128)
 ] = 1%r.
proof.
by conseq squeeze_128_bytes_eq (squeeze_128_bytes_ph' _arr _m) => // /#.
qed.

(****************************************************************************)
(* Correctness lemmas (complete hash operations)                            *)
(****************************************************************************)
require import Mldsa_65_prelude.
hoare hash_verification_key_h' _vk :
 K.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk)))).
proof.
proc.
ecall (A64avx2.dumpstate_avx2_h verification_key_hash 0 64 state).
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A1952avx2.absorb_avx2_h [<:W8.t>] verification_key 31 136).
wp; call (state_init_avx2_h 136).
auto => |> &hr st0 ? [st1 x1]; rewrite /absorb_spec_avx2 => Hab; split.
+ by rewrite stavx2_to_st25K; smt(stavx2INV_from_st25).
move => -> [rr1 rr2] /= -> ?.
rewrite Hab !stavx2_from_st25K.
apply Array64.tP => i Hi /=.
rewrite Array64.get_of_list 1://.
rewrite Bytes64.get_to_list /H_tr.
rewrite Bytes64.get_of_list 1://.
rewrite BytesPK.of_listK 1:Array1952.size_to_list; 1: by rewrite mldsa65_kvec /=.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (64 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE. 
qed.

lemma hash_verification_key_ll : islossless K.hash_verification_key.
proof.
proc.
call A64avx2.dumpstate_avx2_ll.
call keccakf1600_avx2_ll.
call A1952avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare hash_verification_key_ph' _vk :
 [ K.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk))))
 ] = 1%r.
proof.
by conseq hash_verification_key_ll (hash_verification_key_h' _vk).
qed.

phoare hash_verification_key_correct _vk :
 [ M.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk))))
 ] = 1%r.
proof.
by conseq hash_verification_key_eq (hash_verification_key_ph' _vk) => // /#.
qed.

hoare derive_commitment_hash_h' _mu _w1 :
 K.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1)))).
proof.
proc.
ecall (A48avx2.dumpstate_avx2_h commitment_hash 0 48 state).
ecall (keccakf1600_avx2_h (stavx2_to_st25 state)).
wp; ecall (A768avx2.absorb_avx2_h (to_list message_representative) encoded_commitment 31 136).
wp; ecall (A64avx2.absorb_avx2_h [<:W8.t>] message_representative 0 136).
wp; call (state_init_avx2_h 136).
auto => |> st0 ? [st1 x1] ??; split; 1: by smt(Array64.size_to_list).
move => ? [st2 x2]; rewrite /absorb_spec_avx2 => Hab; split.
+ by rewrite stavx2_to_st25K; smt(stavx2INV_from_st25).
move => -> [rr1 rr2] /= -> ?.
rewrite Hab !stavx2_from_st25K.
apply Array48.tP => i Hi /=.
rewrite Array48.get_of_list 1://.
rewrite BytesCT.get_to_list /H_ct.
rewrite BytesCT.get_of_list 1:// mldsa65_lambda 1:/#.
rewrite Bytes64.of_listK 1:Array64.size_to_list // BytesW1.of_listK 1:Array768.size_to_list; 1: by  rewrite mldsa65_kvec.
rewrite /SHAKE256 /KECCAK1600 /SQUEEZE1600 /squeezeblocks /squeezestate_i /st_i /squeezestate /SHAKE_DS_BYTE /c512_r8.
have -> : (48 - 1) %/ 136 + 1 = 1 by done.
rewrite -iotaredE /= fillE initiE 1:/# /= Hi /= nth_take 1,2:/# flatten1 nth_take 1,2:/#.
rewrite iter1 /= (nth_change_dfl W8.zero witness); 1: by rewrite size_state2bytes /= /#.
by rewrite state2bytesE.
qed.

lemma derive_commitment_hash_ll : islossless K.__derive_commitment_hash.
proof.
proc.
call A48avx2.dumpstate_avx2_ll.
call keccakf1600_avx2_ll.
call A768avx2.absorb_avx2_ll.
call A64avx2.absorb_avx2_ll.
call state_init_avx2_ll.
by auto.
qed.

phoare derive_commitment_hash_ph' _mu _w1 :
 [ K.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1))))
 ] = 1%r.
proof.
by conseq derive_commitment_hash_ll (derive_commitment_hash_h' _mu _w1).
qed.

phoare derive_commitment_hash_ph _mu _w1 :
 [ M.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1))))
 ] = 1%r.
proof.
by conseq derive_commitment_hash_eq (derive_commitment_hash_ph' _mu _w1) => // /#.
qed.

(* 
lemma K_derive_message_representative_ll : islossless K.__derive_message_representative.
proof.
proc.
call a64_squeeze_updstate_avx2_ll.
call finish_updstate_avx2_ll.
call absorb_m_updstate_avx2_ll.
wp;call absorb_m_updstate_avx2_ll.
wp;call a66_update_updstate_avx2_ll.
call init_updstate_avx2_ll.
by auto.
qed.

hoare K_derive_message_representative_h' _vk_hash _ctx _msg :
  K.__derive_message_representative :
    arg.`1 = _vk_hash /\
    arg.`3 = List.size _ctx /\
    memread Glob.mem arg.`2 arg.`3 = _ctx /\
    arg.`5 = List.size _msg /\
    memread Glob.mem arg.`4 arg.`5 = _msg /\
    arg.`2 + List.size _ctx < W64.modulus /\
    arg.`4 + List.size _msg < W64.modulus
    ==>
    res = Array64.of_list witness (SHAKE256
      (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))]
       ++ _ctx ++ _msg) 64).
proof.
proc.
ecall (a64_squeeze_updstate_avx2_h state message_representative
  (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))]
   ++ _ctx ++ _msg)).
wp; ecall (finish_updstate_avx2_h state
  (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))]
   ++ _ctx ++ _msg)).
wp; wp; ecall (absorb_m_updstate_avx2_h Glob.mem state
  (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))] ++ _ctx)
  message_pointer message_size).
wp; wp; ecall (absorb_m_updstate_avx2_h Glob.mem state
  (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))])
  context_pointer context_size).
wp; ecall (a66_update_updstate_avx2_h state prefix ([<:W8.t>])).
wp; ecall (init_updstate_avx2_h).
wp; skip => /> &hr -> -> ?? rr Hrr rr0 ->.
do split.
+ do congr; apply (eq_from_nth witness); 1: by  rewrite size_to_list size_cat size_to_list /=.
  move => i;  rewrite size_to_list /= => ib.
  rewrite nth_cat size_to_list !get_setE 1,2:/#.
  case (i < 64) => ?; last by smt().
  rewrite ifF 1:/# ifF 1:/# initiE 1:/# /=.
  case (32 <= i < 64) => ?.
  + rewrite /get256_direct /pack32_t /(\bits8) wordP  /= => k kb.
    by rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= /#.
  rewrite /get256_direct /set256_direct /get8 /pack32_t /(\bits8) wordP => k kb.
  by rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= ifT 1:/# initiE 1:/# /= initiE 1:/# /= initiE /= 1:/# initiE /= /#.
+ by smt(size_ge0).
+ by smt(size_ge0).
qed.

phoare K_derive_message_representative_ph' _vk_hash _ctx _msg :
 [ K.__derive_message_representative
 : arg.`1 = _vk_hash /\
   arg.`3 = List.size _ctx /\
   memread Glob.mem arg.`2 arg.`3 = _ctx /\
   arg.`5 = List.size _msg /\
   memread Glob.mem arg.`4 arg.`5 = _msg /\
   arg.`2 + List.size _ctx < W64.modulus /\
   arg.`4 + List.size _msg < W64.modulus
 ==> res = Array64.of_list witness (SHAKE256
       (to_list _vk_hash ++ [W8.zero; truncateu8 (W64.of_int (List.size _ctx))]
        ++ _ctx ++ _msg) 64)
 ] = 1%r.
proof.
by conseq K_derive_message_representative_ll
          (K_derive_message_representative_h' _vk_hash _ctx _msg).
qed.
*)
phoare derive_message_representative_ph _vk_hash _ctx _msg :
 [ M.__derive_message_representative
 : arg.`1 = _vk_hash /\
   arg.`3 = List.size _ctx /\
   memread Glob.mem arg.`2 arg.`3 = _ctx /\
   arg.`5 = List.size _msg /\
   memread Glob.mem arg.`4 arg.`5 = _msg /\
   arg.`2 + List.size _ctx < W64.modulus /\
   arg.`4 + List.size _msg < W64.modulus
 ==> res = Array64.of_list witness (Bytes64.to_list
     (H_mu (Bytes64.of_list (to_list _vk_hash))
           ([W8.zero; truncateu8 (W64.of_int (List.size _ctx))] ++ _ctx ++ _msg)))
 ] = 1%r.
 admitted.
 (* 
proof.
have Hconseq := (K_derive_message_representative_ph' _vk_hash _ctx _msg).
conseq derive_message_representative_eq Hconseq => |>.
+ move => &1 ???????; exists Glob.mem{1} arg{1}  =>/=;do split;smt(W64.to_uint_cmp pow2_64).
rewrite Bytes64.of_listK;1: by rewrite size_SHAKE256 // Bytes64.to_listK.
congr;congr.  
rewrite Bytes64.of_listK;1: by rewrite size_to_list. 
by rewrite -!catA /=.
qed.
*)
