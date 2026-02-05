require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65_avx2.
from JazzEC require import Array256 Array640.
from Spec require import GFq Rq Serialization Conversion Parameters MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra (* w2bitsE as int2bs *) EclibExtra (* size_flatten' *) JWordList (* nth_chunk *).
 
(* Words of weird size should be cloned and bound here. *)
lemma truncateu_32_20E (w : W32.t) : truncateu_32_20 w = W20.bits2w (take 20 (W32.w2bits w)).
proof.
rewrite /truncateu_32_20 W20.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : gamma1_bits = size (take gamma1_bits (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

op sigextu_20_32(a : W20.t) : W32.t = W32.of_int (to_sint a).
bind op [W20.t & W32.t] sigextu_20_32 "sextend".
realize bvsextendP.
move => bv;rewrite  /sigextu_20_32 /to_sint /smod /= !of_uintK /=.
case (524288 <= to_uint bv); 2: smt(W20.to_uint_cmp).
have ? : 2^20 = 1048576 by auto => />.
move =>?;rewrite -{2}(oppzK (to_uint bv - 1048576)) modNz /=; smt(W20.to_uint_cmp). 
qed.
realize le_size by done.

lemma to_sint_uint_rng_pos_20(xx : W20.t) :
    0 <= to_sint xx  <=> 0 <= to_uint xx < 524288.
 have /= Hxx := W20.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

lemma to_sint_uint_rng_neg_20(xx : W20.t) :
    to_sint xx < 0  <=> 524288 <= to_uint xx <1048576.
 have /= Hxx := W20.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

(* Circuit spec *)

op gamma1 : int = 524288. (* 2**19 *) 
lemma ilog_gamma1 : ilog 2 (gamma1 - 1 + gamma1) = 19 by rewrite /gamma1 /=.

op gamma1_encode_polynomial_lane(c : W32.t) : W20.t = 
    truncateu_32_20 (W32_sub (W32.of_int gamma1) c).

 
lemma BitPack_liftE (p : wpoly) :
  wpoly_srng (gamma1 - 1) gamma1 p =>
    BitPack (lifts_wpoly p) (gamma1 - 1) gamma1
  = to_list (let mapped = init_256_20 (fun i => gamma1_encode_polynomial_lane p.[i]) in
             init_array640_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 20].[(i*8+j) %% 20]))).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have Hlog := ilog_gamma1.
have ? : size
  (flatten (map (fun (x : W32.t) => IntegerToBits (Top.gamma1 - as_sint (incoeff (to_sint x))) (l + 1)) (to_list p))) = 256*20.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
  by rewrite size_map /= size_to_list  /l /= /#.

rewrite /BitsToBytes !array256_mapE /=.
rewrite  -map_comp &(eq_sym) -map_comp /(\o) /=.
apply (eq_from_nth witness);1: by rewrite size_to_list /= size_map size_iota /#. 
move => i; rewrite size_to_list => Hi.
rewrite get_to_list (nth_map witness) /=; 1: by rewrite size_iota /#.
rewrite wordP => j jb.
rewrite !initiE //= initiE 1:/# /= get_bits2w // nth_take // 1:/# nth_drop;2: by smt().
+ rewrite nth_iota /#. 
rewrite (nth_flatten false (l+1)).
+ by rewrite allP => x;rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
rewrite nth_iota 1:/#  (nth_map witness) /=; 1: by rewrite size_to_list /= /#. 
rewrite /gamma1_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ gamma1_bits].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_srng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ gamma1_bits); smt(mem_iota).
move => h. 
rewrite incoeffK_sint_small 1:/# /W32_sub truncateu_32_20E get_bits2w 1:/#.
rewrite nth_take 1,2:/# w2bitsE. 
have  -> := BS2Int.int2bs_cat 20 32 (to_uint (W32.of_int Top.gamma1 - v)) _;1:smt().
rewrite /IntegerToBits nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt(). 
have := (W32.of_uintK (Top.gamma1 - to_sint v)).
rewrite modz_small;1:by smt(pow2_64).
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr. 
rewrite /to_sint /smod /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT //= => ?.
congr;rewrite to_uint_eq of_uintK /=;smt(W32.to_uint_cmp pow2_32). 
qed.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
       polynomial = _a /\ wpoly_srng 524287 524288 _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) (gamma1-1) gamma1
   ].
proc;inline * => /=.
proc change 2 : { temp <- W64.of_int Top.gamma1;}; 1: by auto.
proc change 3 : { gamma1 <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().
proc change ^while.1 : { coefficients <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.13 : {output <- sliceset640_8_128 output (output_offset*8) lower;}; 1: by auto;smt().
proc change ^while.15 : {output <- sliceset640_8_128 output (output_offset*8) upper;}; 1: by auto;smt().
proc change 8 : { coefficients <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change 20 : {output <- sliceset640_8_128 output (output_offset*8) lower;}; 1: by auto;smt().
proc change 22 : {final_output_block <- sliceset16_8_128 final_output_block 0 upper;}; 1: by auto;smt().
unroll for ^while.
unroll for ^while.
cfold 5.
cfold 439.  
wp -3.

conseq (:  _ ==>
           output = let mapped = init_256_20 (fun i => gamma1_encode_polynomial_lane _a.[i]) in
             init_array640_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 20].[(i*8+j) %% 20])));last by circuit.

+ by move => &hr [<- Hrng] ? /= => ->;rewrite BitPack_liftE //=.

qed.


op gamma1_decode_to_polynomial_lane(c : W20.t) : W32.t = 
    (W32_sub (W32.of_int gamma1) (zeroextu_20_32 c)).


lemma BitUnack_liftE (bytes : W8.t Array640.t) :
    BitUnpack (to_list bytes) (gamma1 - 1) gamma1
  =
  (map (fun (w : W32.t) => incoeff (to_sint w))
     (init_256_32
        (fun (i : int) =>
           gamma1_decode_to_polynomial_lane
             (W20.init (fun (j : int) => bytes.[(gamma1_bits * i + j) %/ 8].[(gamma1_bits * i + j) %% 8]))))).
proof.
move=>  @/BitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// mapiE //= initiE 1:/# /=.
pose l1 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota ilog_gamma1 /= /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite (nth_map []) /=.
+ rewrite size_chunk ilog_gamma1 //=.
  rewrite /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
congr; rewrite  /gamma1_decode_to_polynomial_lane /W32_sub.
rewrite ilog_gamma1 /= /zeroextu_20_32. 
rewrite nth_chunk // 1:/#.
+ rewrite /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
have  := BS2Int.bs2int_le2Xs ((take gamma1_bits (drop (gamma1_bits * i) (BytesToBits (to_list bytes))))).
+ rewrite size_take // size_drop 1:/# /max /= (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /=.
  pose ll := if _ then _ else _.
  have -> /= : ll = 20;1: by smt().
rewrite /BitsToInteger.
pose p := BS2Int.bs2int  (take gamma1_bits (drop (gamma1_bits * i) (BytesToBits (to_list bytes)))) .
move => ?.
have ? : 0 <= p by smt(BS2Int.bs2int_ge0).
have <- : p = to_uint (W20.init (fun (j : int) => bytes.[(gamma1_bits * i + j) %/ 8].[(gamma1_bits * i + j) %% 8])); last by have /= :=  W32.to_sintK_small (Top.gamma1 - p); smt().
rewrite /to_uint /p;congr.
apply (eq_from_nth false).
+ rewrite size_take // size_drop 1:/# size_w2bits /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => k kb.
have ? : size (take gamma1_bits (drop (gamma1_bits * i) (BytesToBits (to_list bytes)))) = gamma1_bits.
+ rewrite size_take // size_drop 1:/# /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite nth_take 1,2:/# nth_drop 1,2:/# /BytesToBits.
rewrite (nth_flatten false 8).
+ rewrite allP => j /=.
  rewrite mapP => Hx;elim Hx;smt(W8.size_w2bits).
rewrite (nth_map witness) /=; 1: by rewrite size_to_list /#.
by rewrite initiE 1:/# /=.
qed.


lemma gamma1_decode_to_polynomial _a :
   hoare [ M.gamma1____decode_to_polynomial :
       bytes = _a 
     ==>
       lifts_wpoly res = BitUnpack (to_list _a) (gamma1-1) gamma1
   ].
proc => /=.
proc change 1 : { temp <- W64.of_int Top.gamma1;}; 1: by auto.
proc change 2 : { temp1 <- zeroextu128 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu128E.
  rewrite wordP => i ib.
  rewrite pack2E  initiE 1:/# /= pack2E initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?;1: by rewrite get_of_list /#.
  by rewrite get_of_list 1:/# /= ifF 1:/# /=.
proc change 4 : { temp <- W64.of_int 1048575;}; 1: by auto.
proc change 5 : { temp1 <- zeroextu128 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu128E.
  rewrite wordP => i ib.
  rewrite pack2E  initiE 1:/# /= pack2E initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?;1: by rewrite get_of_list /#.
  by rewrite get_of_list 1:/# /= ifF 1:/# /=.
proc change ^while.1 : { sixteen_bytes <- sliceget640_8_128 bytes (input_offset*8);};1: by auto;smt().
proc change ^while.4 : { sixteen_bytes <- sliceget640_8_128 bytes (input_offset*8);};1: by auto;smt().
proc change ^while.13 : {polynomial <- sliceset256_32_256 polynomial (output_offset*8) coefficients;}; 1: by auto;smt().

unroll for ^while.

cfold 8.
wp -2.
conseq (_: _ ==>
    polynomial = init_256_32 (fun i => gamma1_decode_to_polynomial_lane (W20.init (fun j =>
               _a.[(20*i+j) %/ 8].[(20*i+j) %% 8])))); last by circuit.
            
(* Part 1 *)
move=> &hr |>.
rewrite /lifts_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).


by rewrite BitUnack_liftE ~-1:// !array256_mapE; do 2!congr => //.
qed.

import VecMat PolyLVec.

require import Array1280 Array3200.

op  encode_input_unflatten(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).
op  encode_output_unflatten(a : 'a Array3200.t) =
     LArray.init (fun i => Array640.of_list witness (sub a (640*i) 640)).

lemma gamma1_encode _a :
    lvec = 5 =>
    hoare [ M.gamma1____encode :
       decoded = _a /\ wpolylvec_srng (encode_input_unflatten _a) (gamma1-1) gamma1
     ==>
       encode_output_unflatten res =
           LArray.map (fun (p : poly) => Array640.of_list witness (BitPack p (gamma1-1) gamma1)) (lifts_wpolylvec (encode_input_unflatten _a))
   ].
move => Hlvec.
proc => /=.
while (0 <= i <= 5 /\ decoded = _a /\
       wpolylvec_srng (encode_input_unflatten _a) (gamma1-1) gamma1  /\
       forall k, 0 <= k < i =>
       (encode_output_unflatten encoded).[k] =
       (map (fun (p : poly) => Array640.of_list witness (BitPack p (gamma1-1) gamma1)) (lifts_wpolylvec (encode_input_unflatten _a))).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         by move => r0 j0 *;rewrite tP => k kb; smt().
wp; ecall (gamma1_encode_polynomial (Array256.init (fun (i_0 : int) => _a.[i * 256 + i_0]))).
auto => /> &hr ?? Hrng H ?;do split. 
+ move : Hrng; rewrite /wpolylvec_srng /wpoly_srng !allP /=  => Hrng ii iib.
  have := Hrng i{hr} _; 1:smt().
  rewrite allP /= /encode_input_unflatten initiE 1:/# /= => Hrngj.
  have := Hrngj ii _; 1:smt().
  rewrite initiE 1:/# /= initiE 1:/# /= nth_sub 1:/# /#.
move => ? rr Hrr; do split;1,2: smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+
   have -> : (encode_output_unflatten
   (Array3200.init
      (fun (i_0 : int) => if i{hr} * 640 <= i_0 < i{hr} * 640 + 640 then rr.[i_0 - i{hr} * 640] else encoded{hr}.[i_0]))).[k] =
    ((encode_output_unflatten encoded{hr})).[k]; last by smt().
  rewrite !initiE 1..2:/# /= /of_list /= tP => kk kkb.
  rewrite !initiE 1,2:/# !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> :
   (encode_output_unflatten
   (Array3200.init
      (fun (i_0 : int) => if i{hr} * 640 <= i_0 < i{hr} * 640 + 640 then rr.[i_0 - i{hr} * 640] else encoded{hr}.[i_0]))).[i{hr}]  =
    (rr); last first.
  + have <- := Array640.to_listK witness rr;rewrite Hrr mapiE 1:/# /=;congr;congr.
    rewrite /lifts_wpolylvec mapiE 1:/#;congr;rewrite /encode_input_unflatten initiE 1:/# /=.
    rewrite tP => kk kkb; rewrite !initiE 1,2:/# /= nth_sub /#.

rewrite initiE 1:/# /= tP => ii iib.
rewrite  initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.

op  decode_input_unflatten(a : 'a Array3200.t) =
     LArray.init (fun i => Array640.of_list witness (sub a (640*i) 640)).
op  decode_output_unflatten(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

lemma gamma1_decode _a :
    lvec = 5 =>
    hoare [ M.gamma1____decode :
       encoded = _a
     ==>
       lifts_wpolylvec (decode_output_unflatten res) =
           LArray.map (fun p => BitUnpack (to_list p) (gamma1-1) gamma1) (decode_input_unflatten _a)
   ].
move => Hlvec.
proc => /=.
while (0 <= i <= 5 /\ encoded = _a /\
       forall k, 0 <= k < i =>
       (lifts_wpolylvec (decode_output_unflatten decoded)).[k] =
       (map (fun (p : W8.t Array640.t) => BitUnpack (to_list p) (Top.gamma1 - 1) Top.gamma1) (decode_input_unflatten _a)).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 i0 *;rewrite tP => k kb; smt().
wp; ecall (gamma1_decode_to_polynomial (Array640.init (fun (i_0 : int) => _a.[i * (gamma1_bits * n %/ 8) + i_0]))).
auto => /> &hr ?? H ? rr Hrr;do split;1,2:smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ have -> : (lifts_wpolylvec
   (decode_output_unflatten
      (Array1280.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0])))).[k] =
    (lifts_wpolylvec (decode_output_unflatten decoded{hr})).[k]; last by smt().
  rewrite !mapiE 1..2:/# initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
  rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /= initiE 1:/# /= !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> : (lifts_wpolylvec
   (decode_output_unflatten
      (Array1280.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0])))).[i{hr}]  =
    (lifts_wpoly rr); last first.
  + rewrite Hrr mapiE 1:/# /=;congr;congr;rewrite /decode_input_unflatten initiE 1:/# /= tP => ii iib.
    by rewrite initiE 1:/# get_of_list 1:/# /= nth_sub /#.
rewrite mapiE 1:/# /= initiE 1:/# /= tP => ii iib.
rewrite !mapiE 1,2:/# /= initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.
