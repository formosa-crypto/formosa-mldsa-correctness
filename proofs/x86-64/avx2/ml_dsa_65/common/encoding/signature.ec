require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2.
from JazzEC require import Array256 Array128.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra EclibExtra JWordList.

require import Array640 Array1280.

import VecMat PolyKVec.

require import Array1536 Array3309.

op  decoded_unflatten(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

     
op count_nonzero_coeffs(p : poly) = size (filter (fun c => c = Zq.one) (to_list p)).
op count_nonzero_coeffs_kvec(v : polykvec) =
     foldr (+) 0 (map count_nonzero_coeffs (to_list v)).

lemma encode_hint _signature _hint :
    kvec = 6 =>
    equiv [ HintPackUnpack.hintBitPack ~ M.signature____encode_hint :
       polykvec_urng (decoded_unflatten _hint) 1
    /\ count_nonzero_coeffs_kvec (decoded_unflatten _hint) = w_hint
    /\ arg{1} = decoded_unflatten _hint
    /\ arg{2}.`1 = _signature 
    /\ liftu_wpolykvec (decoded_unflatten arg{2}.`2) =  decoded_unflatten _hint
     ==>
      res{1} = to_list res{2}
   ].
proof.
move => kvec.
proc.

admit.
qed.
