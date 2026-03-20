require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Hashing
                           Signature Challenge.

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

lemma check_row_vector_infinity_norm_correct (z0 : W32.t Array1280.t) (b0 : int) :
    phoare [ M.row_vector____check_infinity_norm :
        arg = (z0,b0)
        ==>
        ((infnorm (lifts_wpolylvec (lvec_unflatten256 z0)) b0) => res = W64.zero) /\
        ((!infnorm (lifts_wpolylvec (lvec_unflatten256 z0)) (gamma1 - Beta)) => res <> W64.zero) 
    ] = 1%r.
proof.
proc. 
admit. qed.
