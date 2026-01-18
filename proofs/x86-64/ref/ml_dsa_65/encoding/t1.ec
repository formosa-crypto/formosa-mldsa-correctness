require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65_ref.
from JazzEC require import Array256 Array320.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra (* w2bitsE as int2bs *) EclibExtra (* size_flatten' *) JWordList (* nth_chunk *).
 
(* Words of weird size should be cloned and bound here. *)
lemma truncateu_32_10E (w : W32.t) : truncateu_32_10 w = W10.bits2w (take 10 (W32.w2bits w)).
proof.
rewrite /truncateu_32_10 W10.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 10 = size (take 10 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

op bitlenqm1md : int = 10 . (* bitlen (q-1) - d = 23 - 13 *)
op b_t1 = 1023. (* 2^bitlenqm1md - 1 *)
lemma ilog_b_t1 : ilog 2 b_t1 = bitlenqm1md - 1 by rewrite /b_t1 /=.

(* Circuit spec  *)

op t1_encode_polynomial_lane(c : W32.t) : W10.t = 
    truncateu_32_10  c.


lemma SimpleBitPack_liftE (p : wpoly) :
  wpoly_urng b_t1 p =>
    SimpleBitPack (liftu_wpoly p) b_t1
  = to_list
  (init_array320_w8
     (fun (i0 : int) =>
        W8.init
          (fun (j : int) =>
             (init_256_10 (fun (i1 : int) => t1_encode_polynomial_lane p.[i1])).[(i0 * 8 + j) %/ 10].[
             (i0 * 8 + j) %% 10]))).
proof.
move=> h @/SimpleBitPack; (pose l := ilog 2 _) => /=.
have := ilog_b_t1; rewrite /bitlenqm1md /= => ?.
have ? : size
   (flatten (map (fun (x : W32.t) => IntegerToBits (asint (incoeff (to_uint x))) (l + 1)) (to_list p))) = 256*10.
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
rewrite /t1_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ 10].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_urng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ 10); smt(mem_iota).
move => h. 
rewrite incoeffK truncateu_32_10E get_bits2w 1:/#.
rewrite nth_take 1,2:/#. 
rewrite /IntegerToBits w2bitsE /l ilog_b_t1 /bitlenqm1md /= (modz_small _ q) 1:/# /BS2Int.int2bs.
by rewrite !nth_mkseq 1,2:/# /= /#.
qed. 

lemma t1_encode_polynomial _a :
   hoare [ M.t1__encode_polynomial :
       t1 = _a /\ wpoly_urng b_t1 _a
     ==>
       to_list res = SimpleBitPack (liftu_wpoly _a) b_t1
   ].
proc => /=. 
proc change ^while.5 : { encoded_bytes <- srl_32 encoded_bytes (W32.of_int 8);}; 1: by auto.
proc change ^while.8 : { encoded_byte <- sll_32 encoded_byte (W32.of_int 2);}; 1: by auto.
proc change ^while.13 : { encoded_bytes <- srl_32 encoded_bytes (W32.of_int 6);}; 1: by auto.
proc change ^while.16 : { encoded_byte <- sll_32 encoded_byte (W32.of_int w1_bits);}; 1: by auto.
proc change ^while.21 : { encoded_bytes <- srl_32 encoded_bytes (W32.of_int w1_bits);}; 1: by auto.
proc change ^while.24 : { encoded_byte <- sll_32 encoded_byte (W32.of_int 6);}; 1: by auto.
proc change ^while.29 : { encoded_bytes <- srl_32 encoded_bytes (W32.of_int 2);}; 1: by auto.
unroll for ^while.
cfold 1. cfold 1.
wp -3.

conseq (:  t1 = init_256_32 (fun i => zeroextu10_32 (truncateu_32_10 _a.[i])) ==>
    encoded = let mapped = init_256_10 (fun i => t1_encode_polynomial_lane _a.[i]) in
    init_array320_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 10].[(i*8+j) %% 10]))); last by circuit. 

+ move => &hr [->+]; rewrite /wpoly_urng allP => ?.
  by rewrite tP => k kb; rewrite initiE 1:/# /= /zeroextu10_32 /truncateu_32_10 /= of_uintK /= modz_small 1:/# to_uintK.
+ by move => &hr [<- Hrng] ? /= => ->;rewrite SimpleBitPack_liftE //=.
  
qed.

op t1_decode_to_polynomial_lane(c : W10.t) : W32.t = 
    zeroextu10_32 c.


lemma SimpleBitUnpack_liftE (bytes : W8.t Array320.t) :
    SimpleBitUnpack (to_list bytes) b_t1
  =
  liftu_wpoly
  (init_256_32
     (fun (i0 : int) =>
        zeroextu10_32 (W10.init (fun (j : int) => bytes.[(i0 * 10 + j) %/ 8].[(i0 * 10 + j) %% 8])))).
proof.
move=>  @/SimpleBitUnpack /=; rewrite tP => i ib.
rewrite initiE 1://  /liftu_wpoly mapiE 1:// /= (nth_map []) /=.
+ rewrite size_chunk ilog_b_t1 /= 1:/#. 
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /b_t1 /#.
congr.
rewrite initiE 1:/# /= /zeroextu10_32 of_uintK /= modz_small;1: by have /= /#:=W10.to_uint_cmp.
rewrite /W10.to_uint /BitsToInteger;congr.
apply (eq_from_nth false).
+ rewrite size_nth_chunk ilog_b_t1  /= 1:/# 2:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /b_t1 /#.
move => kk.
rewrite size_nth_chunk ilog_b_t1  /= 1:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /b_t1 /#.
move => kkb. 
rewrite (nth_chunk 10) 1,2:/#.
+ rewrite /BytesToBits (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /b_t1 /#.
rewrite initiE 1:/# /= nth_take 1,2:/# /= nth_drop 1,2:/# /= /BytesToBits.
rewrite (nth_flatten false 8);1: by rewrite allP => x /=; rewrite mapP => Hx;elim Hx;smt(W8.size_w2bits).
rewrite (nth_map witness); 1: by  rewrite size_to_list; smt().
by rewrite get_w2bits get_to_list /#.
qed.

lemma t1_decode_polynomial _a :
   hoare [ M.t1__decode_polynomial :
       encoded = _a 
     ==>
       liftu_wpoly res = SimpleBitUnpack (to_list _a) b_t1
   ].
proc => /=. 
proc change ^while.6 : {temp1 <- sll_32 temp1 (W32.of_int 8);}; 1: by auto.
proc change ^while.11 : {coefficient <- srl_32 temp2 (W32.of_int 2);}; 1: by auto.
proc change ^while.15 : {temp1 <- sll_32 temp1 (W32.of_int 6);}; 1: by auto.
proc change ^while.20 : { coefficient <- srl_32 temp2 (W32.of_int w1_bits);}; 1: by auto.
proc change ^while.24 : { temp1 <- sll_32 temp1 (W32.of_int w1_bits);}; 1: by auto.
proc change ^while.29 : { coefficient <- srl_32 temp2 (W32.of_int 6);}; 1: by auto.
proc change ^while.32 : { temp1 <- sll_32 temp1 (W32.of_int 2);}; 1: by auto.

unroll for ^while.

cfold 1. cfold 1.
wp -3.

conseq (: encoded = _a ==>
     t1 = init_256_32 (fun i => zeroextu10_32 (W10.init (fun j => _a.[(i*10+j) %/ 8].[(i*10+j) %% 8])))); last by circuit. 


move=> &hr |>  /=.
by rewrite SimpleBitUnpack_liftE ~-1://. 
qed.

require import Array1920 Array1536.

op  input_unflatten(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).
op  output_unflatten(a : 'a Array1920.t) =
     KArray.init (fun i => Array320.of_list witness (sub a (320*i) 320)).

lemma t1_encode _a :
    kvec = 6 =>
    hoare [ M.t1____encode :
       t1 = _a /\ wpolykvec_urng (input_unflatten _a) b_t1 
     ==>
       output_unflatten res = 
           KArray.map (fun (p : poly) => Array320.of_list witness (SimpleBitPack  p b_t1)) (liftu_wpolykvec (input_unflatten _a))
   ].
move => Hkvec.
proc => /=.
while (0 <= j <= 6 /\ t1 = _a /\ wpolykvec_urng (input_unflatten _a) b_t1  /\
       forall k, 0 <= k < j =>
       (output_unflatten encoded).[k] =
       (map (fun (p : poly) => Array320.of_list witness (SimpleBitPack  p b_t1)) (liftu_wpolykvec (input_unflatten _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (t1_encode_polynomial (Array256.init (fun (i_0 : int) => _a.[j * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split;1:smt().
+ move : Hrng; rewrite /wpolykvec_urng /wpoly_urng !allP /=  => Hrng i ib.
  have := Hrng j{hr} _; 1:smt().
  rewrite allP /= /input_unflatten initiE 1:/# /= => Hrngj.
  have := Hrngj i _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#. 
move => ?? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<j{hr}) => *.
+ 
   have -> : (output_unflatten
   (Array1920.init
      (fun (i : int) => if j{hr} * 320 <= i < j{hr} * 320 + 320 then rr.[i - j{hr} * 320] else encoded{hr}.[i]))).[k] =
    ((output_unflatten encoded{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = j{hr} by smt().
+ have -> : 
   (output_unflatten
   (Array1920.init
      (fun (i : int) => if j{hr} * 320 <= i < j{hr} * 320 + 320 then rr.[i - j{hr} * 320] else encoded{hr}.[i]))).[j{hr}]  =
    (rr); last first.
  + have <- := Array320.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /liftu_wpolykvec mapiE 1:/#;congr;rewrite /input_unflatten initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.
 
rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.
