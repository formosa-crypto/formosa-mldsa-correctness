require import AllCore List IntDiv.
from Jasmin require import JByte_array JWord.

require import Parameters GFq Rq VecMat Conversion Serialization.
import PolyLVec PolyKVec PolyMat.
import CDR Round Zq BigZMod MLDSAParams.

abbrev gamma1m1_bits = 19.
lemma gamma1_bitlen :  2^(gamma1m1_bits-1) < gamma1-1 (* signed range *) <= 2^(gamma1m1_bits)
  by  have/= H := param_sets; elim H => /> ??->???? /=.

clone import ByteArray as Bytes66 with op size <= 66.
clone import ByteArray as Bytes34 with op size <= 34.
clone import ByteArray as Bytes8 with op size <= 8.
clone import ByteArray as Bytes3 with op size <= 3.
clone import ByteArray as BytesV with op size <= n * (gamma1m1_bits + 1) %/ 8.

(*  H = SHAKE256, G = SHAKE128 *)

op H_sib : BytesCT.t -> Bytes8.t. (* first 64 bytes of SHAKE256 on CTBytes input (48 or 64) *)

module type XOF_SIB = {  (* bytes after 64 prefix of SHAKE256 on CTBytes  (48 or 64) input *)
  proc init(rho : BytesCT.t) : unit
  proc next() : W8.t
}.

module type XOF_RejNTTPoly = {  (* SHAKE128 on 32 bytes input *)
  proc init(rho : Bytes34.t) : unit
  proc next() : Bytes3.t
}.

module type XOF_RejBPoly = {  (* SHAKE256 on 66 bytes input *)
  proc init(rho : Bytes66.t) : unit
  proc next() : W8.t
}.

op H_seed : Bytes34.t -> Bytes32.t * Bytes64.t * Bytes32.t. (* SHAKE256 on 34 byte input,
              but first 32 bytes are secret (PRG) *)

op H_tr : BytesPK.t -> Bytes64.t. (* shake256 on PKbytes input *)

op H_mu : Bytes64.t -> W8.t list -> Bytes64.t.  
  (* SHAKE256 on variable size input prefixed on Htr (64 bytes) + 
         message is prepended by at least 2 bytes *)

type rnd_. (* either 0 or 32 bytes *)
op H_rhopp : Bytes32.t -> rnd_ -> Bytes64.t -> Bytes64.t. (* SHAKE256 on input size 32+rnd_+64 bytes, 
                        but first input is secret (PRF) *)

op H_ct : Bytes64.t -> BytesW1.t -> BytesCT.t. (* SHAKE256 on 64 + W1 bytes input *)

op H_v : Bytes66.t -> BytesV.t. (* SHAKE256 on 66 bytes input, but 64 bytes are secret (PRF) *)

(* NOTE: Strictly speaking ML-DSA is a big mess when it comes to using SHAKE256.
  There are several points where inputs with the same size can occur, due to the
  variable size input of the message hashing.
  When part of the input is secret, one can argue for domain separation.
  However, Hmu can be used with inputs of the same size as  Hct and Htr,
  but still we need to make Hmu and Htr independent random oracles.
  For Htr vs Hmu one can argue that game would need to sample
  a pk such that HashPK is a prefix of PK.
  For Hct vs Hmu one can argue that game would need to sample 
  a pk such that Hash(HashPK) = HashPK.  *)
