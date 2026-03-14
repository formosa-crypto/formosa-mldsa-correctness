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
  proc.  admit.
(* by inline *;sim; auto => />. *)
qed.

equiv derive_message_representative_eq:
 M.__derive_message_representative ~ K.__derive_message_representative
 : ={arg, Glob.mem} ==> ={res, Glob.mem}
 by sim.

(****************************************************************************)
(* Correctness lemmas (absorbed-state characterization)                     *)
(****************************************************************************)

phoare shake256_absorb_34_ph _seed _extra :
 [ M.shake256_absorb_34
 : arg.`1 = _seed /\ arg.`2 = _extra
 ==> absorb_spec_avx2 136 31 (to_list _seed ++ to_list _extra) res
 ] = 1%r.
admitted.

phoare shake256_absorb_66_ph _rho_prime _ds :
 [ M.shake256_absorb_66
 : arg.`1 = _rho_prime /\ arg.`2 = _ds
 ==> absorb_spec_avx2 136 31
      (to_list _rho_prime ++
       to_list (Array2.init (WArray2.get8 (WArray2.set16 (WArray2.init8 (fun i => witness)) 0 _ds))))
      res
 ] = 1%r.
admitted.

phoare shake256_absorb_128_ph _block :
 [ M.shake256_absorb_128
 : arg = _block
 ==> absorb_spec_avx2 136 31 (to_list _block) res
 ] = 1%r.
admitted.

phoare shake256_absorb_commitment_hash_ph _hash :
 [ M.shake256_absorb_commitment_hash
 : arg = _hash
 ==> absorb_spec_avx2 136 31 (to_list _hash) res
 ] = 1%r.
admitted.

(****************************************************************************)
(* Correctness lemmas (complete hash operations)                            *)
(****************************************************************************)

phoare hash_verification_key_ph _vk :
 [ M.hash_verification_key
 : arg.`2 = _vk
 ==> res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _vk))))
 ] = 1%r.
admitted.

phoare derive_commitment_hash_ph _mu _w1 :
 [ M.__derive_commitment_hash
 : arg.`1 = _mu /\ arg.`2 = _w1
 ==> res = Array48.of_list witness (BytesCT.to_list (H_ct (Bytes64.of_list (to_list _mu)) (BytesW1.of_list (to_list _w1))))
 ] = 1%r.
admitted.

(* __derive_message_representative computes SHAKE256 over:
     vk_hash (64 bytes) || 0x00 || context_size_byte || context || message
   which is exactly H_mu(vk_hash, [0x00; context_size_byte] ++ context ++ message).
   Context and message are read from memory via their pointer/size arguments. *)
phoare derive_message_representative_ph _vk_hash _ctx _msg :
 [ M.__derive_message_representative
 : arg.`1 = _vk_hash /\
   arg.`3 = List.size _ctx /\
   memread Glob.mem arg.`2 arg.`3 = _ctx /\
   arg.`5 = List.size _msg /\
   memread Glob.mem arg.`4 arg.`5 = _msg
 ==> res = Array64.of_list witness (Bytes64.to_list
     (H_mu (Bytes64.of_list (to_list _vk_hash))
           ([W8.zero; truncateu8 (W64.of_int (List.size _ctx))] ++ _ctx ++ _msg)))
 ] = 1%r.
admitted.
