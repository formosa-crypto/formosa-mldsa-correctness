require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65_avx2.
from JazzEC require import Array256 Array128.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra EclibExtra JWordList.

require import Array640 Array1280.

require import Error_polynomial.

(* For s1, Eta = 4 for ML-DSA-65 *)
abbrev Eta = Error_polynomial.Eta.

import VecMat PolyLVec.

(*
   For s1:
   - Input: 5 polynomials × 256 W32.t coefficients = 1280 W32.t elements (5120 bytes)
   - Output: 1280 coefficients × 4 bits = 5120 bits = 640 bytes
*)

op  input_unflatten(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).
op  output_unflatten(a : 'a Array640.t) =
     LArray.init (fun i => Array128.of_list witness (sub a (128*i) 128)).

lemma s1_encode _a :
    lvec = 5 =>
    hoare [ M.s1____encode :
       s1 = _a /\ wpolylvec_srng (input_unflatten _a) Eta Eta
     ==>
       output_unflatten res =
           LArray.map (fun (p : poly) => Array128.of_list witness (BitPack p Eta Eta)) (lifts_wpolylvec (input_unflatten _a))
   ].
move => Hlvec.
proc => /=.
while (0 <= i <= 5 /\ s1 = _a /\ wpolylvec_srng (input_unflatten _a) Eta Eta  /\
       forall k, 0 <= k < i =>
       (output_unflatten encoded).[k] =
       (map (fun (p : poly) => Array128.of_list witness (BitPack p Eta Eta)) (lifts_wpolylvec (input_unflatten _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (error_polynomial_encode (Array256.init (fun (i_0 : int) => _a.[i * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split;1:smt().
+ move : Hrng; rewrite /wpolylvec_srng /wpoly_srng !allP /=  => Hrng ii iib.
  have := Hrng i{hr} _; 1:smt().
  rewrite allP /= /input_unflatten initiE 1:/# /= => Hrngj.
  have := Hrngj ii _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#.
move => ?? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+
   have -> : (output_unflatten
   (Array640.init
      (fun (i_0 : int) => if 128 * i{hr} <= i_0 < 128 * i{hr} + 128 then rr.[i_0 - 128 * i{hr}] else encoded{hr}.[i_0]))).[k] =
    ((output_unflatten encoded{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> :
   (output_unflatten
   (Array640.init
      (fun (i_0 : int) => if 128 * i{hr} <= i_0 < 128 * i{hr} + 128 then rr.[i_0 - 128 * i{hr}] else encoded{hr}.[i_0]))).[i{hr}]  =
    (rr); last first.
  + have <- := Array128.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /lifts_wpolylvec mapiE 1:/#;congr;rewrite /input_unflatten initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.

rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.

(*
   For s1 decode:
   - Input: 640 bytes = Array640 W8.t
   - Output: 5 polynomials × 256 W32.t coefficients = 1280 W32.t elements
*)

op  decode_input_unflatten(a : 'a Array640.t) =
     LArray.init (fun i => Array128.of_list witness (sub a (128*i) 128)).
op  decode_output_unflatten(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

lemma s1_decode _a :
    lvec = 5 =>
    hoare [ M.s1____decode :
       encoded = _a
     ==>
       lifts_wpolylvec (decode_output_unflatten res) =
           LArray.map (fun (bytes : W8.t Array128.t) => BitUnpack (to_list bytes) Eta Eta) (decode_input_unflatten _a)
   ].
move => Hlvec.
proc => /=.
while (0 <= i <= 5 /\ encoded = _a /\
       forall k, 0 <= k < i =>
       (lifts_wpolylvec (decode_output_unflatten s1)).[k] =
       (map (fun (bytes : W8.t Array128.t) => BitUnpack (to_list bytes) Eta Eta) (decode_input_unflatten _a)).[k]);
       last first.
       + auto => /> &hr *; do split; 1: smt().
         move => r0 j0 *; rewrite tP => k kb; smt().
wp; ecall (error_polynomial_decode (Array128.init (fun (i_0 : int) => _a.[i * 128 + i_0]))).
auto => /> &hr ??H?;split;1:smt().
move => ? rr Hrr;do split;1,2:smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ have -> : (lifts_wpolylvec
   (decode_output_unflatten
      (Array1280.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else s1{hr}.[i_0])))).[k] =
    (lifts_wpolylvec (decode_output_unflatten s1{hr})).[k]; last by smt().
  rewrite !mapiE 1..2:/# initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
  rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /= initiE 1:/# /= !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> : (lifts_wpolylvec
   (decode_output_unflatten
      (Array1280.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else s1{hr}.[i_0])))).[i{hr}]  =
    (lifts_wpoly rr); last first.
  + rewrite Hrr mapiE 1:/# /=;congr;congr;rewrite /input_unflatten initiE 1:/# /= tP => ii iib.
    by rewrite initiE 1:/# get_of_list 1:/# /= nth_sub /#.
rewrite mapiE 1:/# /= initiE 1:/# /= tP => ii iib.
rewrite !mapiE 1,2:/# /= initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.

