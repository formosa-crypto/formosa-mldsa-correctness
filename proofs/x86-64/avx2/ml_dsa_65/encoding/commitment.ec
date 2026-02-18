require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array128.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra (* w2bitsE as int2bs *) EclibExtra (* size_flatten' *) JWordList (* nth_chunk *).
 
(* Words of weird size should be cloned and bound here. *)
lemma truncateu_32_4E (w : W32.t) : truncateu32_4 w = W4.bits2w (take 4 (W32.w2bits w)).
proof.
rewrite /truncateu32_4 W4.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 4 = size (take 4 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

op b_w1 = 15. (* 2^w1_bits - 1 *)
lemma ilog_b_w1 : ilog 2 b_w1 = w1_bits - 1 by rewrite /b_w1 /=.

(* Circuit spec  *)

op commitment_encode_polynomial_lane(c : W32.t) : W4.t = 
    truncateu32_4  c.


lemma SimpleBitPack_liftE (p : wpoly) :
  wpoly_urng b_w1 p =>
    SimpleBitPack (liftu_wpoly p) b_w1
  = to_list
  (init_128_8
     (fun (i0 : int) =>
        W8.init
          (fun (j : int) =>
             (init_256_4 (fun (i1 : int) => commitment_encode_polynomial_lane p.[i1])).[(i0 * 8 + j) %/ 4].[
             (i0 * 8 + j) %% 4]))).
proof.
move=> h @/SimpleBitPack; (pose l := ilog 2 _) => /=.
have := ilog_b_w1; rewrite /bits_w1 /= => ?.
have ? : size
   (flatten (map (fun (x : W32.t) => IntegerToBits (asint (incoeff (to_uint x))) (l + 1)) (to_list p))) = 256*4.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
  by rewrite size_map /= size_to_list  /l /= /#.

rewrite /BitsToBytes !array256_mapE /=.
rewrite  -map_comp &(eq_sym) -map_comp /(\o) /=.
apply (eq_from_nth witness); 1: by rewrite size_to_list /= size_map size_iota /#. 
move => i; rewrite size_to_list => Hi.
rewrite get_to_list (nth_map witness) /=; 1: by rewrite size_iota /#.
rewrite wordP => j jb.
rewrite !initiE //= initiE 1:/# /= get_bits2w // nth_take // 1:/# nth_drop;2: by smt().
+ rewrite nth_iota /#. 
rewrite (nth_flatten false (l+1)).
+ by rewrite allP => x;rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
rewrite nth_iota 1:/#  (nth_map witness) /=; 1: by rewrite size_to_list /= /#. 
rewrite /commitment_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ 4].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_urng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ 4); smt(mem_iota).
move => h. 
rewrite incoeffK truncateu_32_4E get_bits2w 1:/#.
rewrite nth_take 1,2:/#. 
rewrite /IntegerToBits w2bitsE /l ilog_b_w1 /bitlenqm1md /= (modz_small _ q) 1:/# /BS2Int.int2bs.
by rewrite !nth_mkseq 1,2:/# /= /#.
qed. 

lemma commitment_encode_polynomial _a :
   hoare [ M.commitment____encode_polynomial :
       commitment = _a /\ wpoly_urng b_w1 _a
     ==>
       to_list res = SimpleBitPack (liftu_wpoly _a) b_w1
   ].
proc => /=;inline *.
proc change 1 : { temp <- W64.of_int 4097;}; 1: by auto.
proc change 2 : { shift <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().

proc change ^while.1 : { c0 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.3 : { c1 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.5 : { c2 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.7 : { c3 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.9 : { c4 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.11 : { c5 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.13 : { c6 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().
proc change ^while.15 : { c7 <- sliceget256_32_256 commitment (input_offset*8);};1: by auto;smt().

proc change ^while.28 : {encoded <- sliceset128_8_256 encoded (output_offset*8) c0;}; 1: by auto;smt().

unroll for ^while.
cfold 5.
wp -2.

conseq (:  commitment = init_256_32 (fun i => zeroextu4_32 (truncateu32_4 _a.[i])) ==>
    encoded  = let mapped = init_256_4 (fun i => commitment_encode_polynomial_lane _a.[i]) in
    init_128_8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 4].[(i*8+j) %% 4]))); last by circuit. 

+ move => &hr [->+]; rewrite /wpoly_urng allP => ?.
  by rewrite tP => k kb; rewrite initiE 1:/# /= /zeroextu4_32 /truncateu32_4 /= of_uintK /= modz_small 1:/# to_uintK.
+ by move => &hr [<- Hrng] ? /= => ->;rewrite SimpleBitPack_liftE //=.
  
qed.

import VecMat PolyKVec.

require import Array768 Array1536.

lemma commitment_encode _a :
    hoare [ M.commitment____encode :
       commitment = _a /\ wpolykvec_urng (kvec_unflatten256 _a) b_w1 
     ==>
       kvec_unflatten128 res = 
           KArray.map (fun (p : poly) => Array128.of_list witness (SimpleBitPack  p b_w1)) (liftu_wpolykvec (kvec_unflatten256 _a))
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= i <= 6 /\ commitment = _a /\ wpolykvec_urng (kvec_unflatten256 _a) b_w1  /\
       forall k, 0 <= k < i =>
       (kvec_unflatten128 encoded_commitment).[k] =
       (map (fun (p : poly) => Array128.of_list witness (SimpleBitPack  p b_w1)) (liftu_wpolykvec (kvec_unflatten256 _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (commitment_encode_polynomial (Array256.init (fun (i_0 : int) => _a.[i * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split. 
+ move : Hrng; rewrite /wpolykvec_urng /wpoly_urng !allP /=  => Hrng ii iib.
  have := Hrng i{hr} _; 1:smt().
  rewrite allP /= /input_unflatten initiE 1:/# /= => Hrngj.
  have := Hrngj ii _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#. 
move => ? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ 
   have -> : (kvec_unflatten128
   (Array768.init
      (fun (ii : int) => if i{hr} * 128 <= ii < i{hr} * 128 + 128 then rr.[ii - i{hr} * 128] else encoded_commitment{hr}.[ii]))).[k] =
    ((kvec_unflatten128 encoded_commitment{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> : 
   (kvec_unflatten128
   (Array768.init
      (fun (ii : int) => if i{hr} * 128 <= ii < i{hr} * 128 + 128 then rr.[ii - i{hr} * 128] else encoded_commitment{hr}.[ii]))).[i{hr}]  =
    (rr); last first.
  + have <- := Array128.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /liftu_wpolykvec mapiE 1:/#;congr;rewrite /input_unflatten initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.
 
rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.

