require import AllCore.
from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65.

from JazzEC require import Array256 Array640.

require import Bindings.

type polyw_t = W32.t Array256.t.

op gamma1 : int = 524288. (* 2**19 *)

op pre_gamma1_encode_polynomial(c : W32.t) = 
    ( (W32.zero) - (W32.of_int (524287))) \sle c /\ c \sle W32.of_int gamma1. 

op gamma1_encode_polynomial_lane(c : W32.t) : W20.t = 
    truncateu_32_20 ( (W32.of_int gamma1) - c).

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
     polynomial = _a ==> true ].
proc => /=. 
proc change ^while.1 : (W32.of_int gamma1); 1: by auto.
proc change ^while.3 : (W32.of_int gamma1); 1: by auto.
proc change ^while.2 : (W32_sub t0 (polynomial.[2 * i + 0])); 1: by auto.
proc change ^while.4 : (W32_sub t1 (polynomial.[2 * i + 1])); 1: by auto.
proc change ^while.8 : (srl_32 encoded_bytes (W32.of_int 8)); 1: by auto.
proc change ^while.11 : (srl_32 encoded_bytes (W32.of_int 16)); 1: by auto.
proc change ^while.14 : (sll_32 encoded_bytes (W32.of_int 4)); 1: by auto.
proc change ^while.18 : (srl_32 encoded_bytes (W32.of_int 4)); 1: by auto.
proc change ^while.21 : (srl_32 encoded_bytes (W32.of_int 12)); 1: by auto.
unroll for ^while.
cfold 1.
wp -2. 
bdep 32 20 [_a] [polynomial] [encoded] gamma1_encode_polynomial_lane pre_gamma1_encode_polynomial.
simplify.
admitted.

from JazzEC require import Ml_dsa_65_barray.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
     polynomial = _a ==> true ].
proc.
