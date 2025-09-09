require import AllCore.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65.
from JazzEC require import Array256 Array640.
from Spec require import Rq Serialization Conversion.

type poly_t = int Array256.t.
type polyw_t = W32.t Array256.t.

op liftu_wpoly(pw : polyw_t) : poly_t  = map W32.to_uint  pw.
op lifts_wpoly(pw : polyw_t) : poly_t  = map W32.to_sint  pw.
op unlift_poly(p : poly_t)  : polyw_t = map W32.of_int  p.

op poly_urng(p : poly_t, b : int) = all (fun i => 0 <= i < b) p.
op wpoly_urng(pw : polyw_t, b : int) = poly_urng (liftu_wpoly pw) b. 
op poly_srng(p : poly_t, bl bh : int) = all (fun i => -bl <= i <= bh) p.
op wpoly_srng(pw : polyw_t, b : int) = poly_urng (lifts_wpoly pw) b. 

(* natural spec and precondition *)

op gamma1 : int = 524288. (* 2**19 *)
print Serialization. print BitPack. print poly.


(* Circuit spec and precondition *)

op pre_gamma1_encode_polynomial(c : W32.t) = 
    (W32_sub (W32.zero) (W32.of_int (524287))) \sle c /\ c \sle W32.of_int gamma1. 

op gamma1_encode_polynomial_lane(c : W32.t) : W20.t = 
    truncateu_32_20 (W32_sub (W32.of_int gamma1) c).

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
     polynomial = _a /\ wpoly_srng a 524287 524288 ==> true ].
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
(* FIXME: WE NEED CONTEXT FOR THIS PROC CHANGE *)
proc change ^while.15: ((byte  `&` W8.of_int 15) `|` (truncateu8 encoded_bytes));1:by admit.
unroll for ^while.
cfold 1.
wp -2. 
bdep 32 20 [_a] [polynomial] [encoded] gamma1_encode_polynomial_lane pre_gamma1_encode_polynomial.
admitted.

from JazzEC require import Ml_dsa_65_barray.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
     polynomial = _a ==> true ].
proc.
