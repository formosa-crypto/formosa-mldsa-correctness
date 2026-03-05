require import AllCore List (* IntDiv RealExp StdBigop *).

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Error_vectors T0 T1.
(* from JazzEC require import Array32. *)

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

(* require import ArrayExtra JWord_extra EclibExtra JWordList. *)

require import Array32 Array64 Array128 Array640 Array768 Array1280 Array1536 Array1920 Array1952 Array2496 Array4032 Array7680.
require import WArray32 WArray1952 WArray4032.

lemma hash_verification_key_correct _pk :
    phoare [ M.hash_verification_key :
         arg.`2 = _pk ==>
         res = Array64.of_list witness (Bytes64.to_list (H_tr (BytesPK.of_list (to_list _pk)))) ] = 1%r.
admitted.
