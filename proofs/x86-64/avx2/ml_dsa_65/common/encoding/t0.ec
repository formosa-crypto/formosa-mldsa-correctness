require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude.
from JazzEC require import Array256 Array416.
from Spec require import GFq Rq Serialization Conversion Parameters MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra (* w2bitsE as int2bs *) EclibExtra (* size_flatten' *) JWordList (* nth_chunk *).
 
(* Words of weird size should be cloned and bound here. *)
lemma truncateu_32_13E (w : W32.t) : truncateu_32_13 w = W13.bits2w (take 13 (W32.w2bits w)).
proof.
rewrite /truncateu_32_13 W13.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 13 = size (take 13 (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

op sigextu_13_32(a : W13.t) : W32.t = W32.of_int (to_sint a).
bind op [W13.t & W32.t] sigextu_13_32 "sextend".
realize bvsextendP.
move => bv;rewrite  /sigextu_13_32 /to_sint /smod /= !of_uintK /=.
case (4096 <= to_uint bv); 2: smt(W13.to_uint_cmp).
have ? : 2^13 = 8192 by auto => />.
move =>?;rewrite -{2}(oppzK (to_uint bv - 8192)) modNz /=; smt(W13.to_uint_cmp). 
qed.
realize le_size by done.

lemma to_sint_uint_rng_pos_13(xx : W13.t) :
    0 <= to_sint xx  <=> 0 <= to_uint xx < 4096.
 have /= Hxx := W13.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

lemma to_sint_uint_rng_neg_13(xx : W13.t) :
    to_sint xx < 0  <=> 4096 <= to_uint xx < 8192.
 have /= Hxx := W13.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

(* Circuit spec *)

op dpow : int = 4096. (* 2**(d-1) *) 
lemma ilog_dpow : ilog 2 (dpow - 1 + dpow) = 12 by rewrite /dpow /=.

op t0_encode_polynomial_lane(c : W32.t) : W13.t = 
    truncateu_32_13 (W32_sub (W32.of_int dpow) c).

lemma BitPack_liftE (p : wpoly) :
  wpoly_srng (dpow - 1) dpow p =>
    BitPack (lifts_wpoly p) (dpow - 1) dpow
  = to_list (let mapped = init_256_13 (fun i => t0_encode_polynomial_lane p.[i]) in
             init_array416_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 13].[(i*8+j) %% 13]))).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have Hlog := ilog_dpow.
have ? : size
  (flatten (map (fun (x : W32.t) => IntegerToBits (Top.dpow - as_sint (incoeff (to_sint x))) (l + 1)) (to_list p))) = 256*13.
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
rewrite /t0_encode_polynomial_lane .
pose v:=p.[(i * 8 + j) %/ d].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_srng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ d); smt(mem_iota).
move => h. 
rewrite incoeffK_sint_small 1:/# /W32_sub truncateu_32_13E get_bits2w 1:/#.
rewrite nth_take 1,2:/# w2bitsE. 
have  -> := BS2Int.int2bs_cat 13 32 (to_uint (W32.of_int dpow - v)) _;1:smt().
rewrite /IntegerToBits nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt(). 
have := (W32.of_uintK (Top.dpow - to_sint v)).
rewrite modz_small;1:by smt(pow2_64).
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr. 
rewrite /to_sint /smod /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT //= => ?.
congr;rewrite to_uint_eq of_uintK /=;smt(W32.to_uint_cmp pow2_32). 
qed.

lemma t0_encode_polynomial _a :
   hoare [ M.t0__encode_polynomial :
       t0 = _a /\ wpoly_srng (dpow-1) dpow _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) (dpow-1) dpow
   ].
proc;inline * => /=.
proc change ^while.1 : { coefficients <- sliceget256_32_256 t0 (input_offset*8);};1: by auto;smt().
proc change ^while.20 : { t0_encoded <- sliceset416_8_128 t0_encoded (output_offset*8) bytestream;}; 1: by auto;smt().
proc change 5 : { coefficients <- sliceget256_32_256 t0 (input_offset*8);};1: by auto;smt().
proc change 24 : { final_encoded_output <- sliceset16_8_128 final_encoded_output 0 bytestream;}; 1: by auto;smt().

unroll for ^while.
unroll for ^while.
cfold 2.
cfold 622.  
wp -3.

conseq (:  List.all (fun i => 
    _a.[i] \sle W32.of_int (dpow) /\ 
    W32.of_int (1-dpow) \sle _a.[i]) 
    (iota_ 0 256) 
  /\ _a = t0  ==>
           t0_encoded = let mapped = init_256_13 (fun i => t0_encode_polynomial_lane _a.[i]) in
             init_array416_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 13].[(i*8+j) %% 13])));last by circuit.

+ move => &hr [<- +]; rewrite /wpoly_srng allP /= => Hrng.
  rewrite /(\sle) allP => x; rewrite mem_iota /= => Hx.
  rewrite to_sintK_small //=.
  by rewrite of_sintK /= /smod /= /#.

+ by move => &hr [<- Hrng] ? /= => ->;rewrite BitPack_liftE //=.

qed.

op t0_decode_to_polynomial_lane(c : W13.t) : W32.t = 
    (W32_sub (W32.of_int dpow) (zeroextu13_32 c)).


lemma BitUnack_liftE (bytes : W8.t Array416.t) :
    BitUnpack (to_list bytes) (dpow - 1) dpow
  =
  (map (fun (w : W32.t) => incoeff (to_sint w))
     (init_256_32
        (fun (i : int) =>
           t0_decode_to_polynomial_lane
             (W13.init (fun (j : int) => bytes.[(d * i + j) %/ 8].[(d * i + j) %% 8]))))).
proof.
move=>  @/BitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// mapiE //= initiE 1:/# /=.
pose l1 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota ilog_dpow /= /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
rewrite (nth_map []) /=.
+ rewrite size_chunk ilog_dpow //=.
  rewrite /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
congr; rewrite  /t0_decode_to_polynomial_lane /W32_sub.
rewrite ilog_dpow /= /zeroextu13_32. 
rewrite nth_chunk // 1:/#.
+ rewrite /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
have  := BS2Int.bs2int_le2Xs ((take d (drop (d * i) (BytesToBits (to_list bytes))))).
+ rewrite size_take // size_drop 1:/# /max /= (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /=.
  pose ll := if _ then _ else _.
  have -> /= : ll = 13;1: by smt().
rewrite /BitsToInteger.
pose p := BS2Int.bs2int  (take d (drop (d * i) (BytesToBits (to_list bytes)))) .
move => ?.
have ? : 0 <= p by smt(BS2Int.bs2int_ge0).
have <- : p = to_uint (W13.init (fun (j : int) => bytes.[(d * i + j) %/ 8].[ (d * i + j) %% 8])); last by have /= :=  W32.to_sintK_small (dpow - p); smt().
rewrite /to_uint /p;congr.
apply (eq_from_nth false).
+ rewrite size_take // size_drop 1:/# size_w2bits /BytesToBits. 
  rewrite (EclibExtra.size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
move => k kb.
have ? : size (take d (drop (d * i) (BytesToBits (to_list bytes)))) = d.
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


lemma t0_decode_to_polynomial _a :
   hoare [ M.t0____decode_polynomial :
       t0_encoded = _a 
     ==>
       lifts_wpoly res = BitUnpack (to_list _a) (dpow-1) dpow
   ].
proc => /=;inline *.
proc change ^while.1 : { bytestream <- sliceget416_8_128 t0_encoded (input_offset*8);};1: by auto;smt().
proc change ^while.15 : {t0 <- sliceset256_32_256 t0 (output_offset*8) coefficients;}; 1: by auto;smt().
proc change 4 : { bytestream <- sliceget416_8_128 t0_encoded (400*8);}; 1: by auto;smt().
proc change 19 : {t0 <- sliceset256_32_256 t0 (output_offset*8) coefficients;}; 1: by auto;smt().

unroll for ^while.

cfold 1.
cfold 466.
wp -2.
conseq (_: _ ==>
    t0 = init_256_32 (fun i => t0_decode_to_polynomial_lane (W13.init (fun j =>
               _a.[(13*i+j) %/ 8].[(13*i+j) %% 8])))); last by circuit.
            
(* Part 1 *)
move=> &hr |>.
rewrite /lifts_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).


by rewrite BitUnack_liftE ~-1:// !array256_mapE; do 2!congr => //.
qed.


import VecMat PolyLVec.

require import Array1536 Array2496.

op  encoded_unflatten(a : 'a Array2496.t) =
     KArray.init (fun i => Array416.of_list witness (sub a (416*i) 416)).
op  decoded_unflatten(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

lemma t0_decode _a  :
    hoare [ M.t0__decode : 
       encoded = _a 
     ==>
       lifts_wpolykvec (decoded_unflatten res) = 
           KArray.map (fun p => BitUnpack (to_list p) (dpow-1) dpow) (encoded_unflatten _a)
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= i <= 6 /\ encoded = _a /\
       forall k, 0 <= k < i =>
       (lifts_wpolykvec (decoded_unflatten t0)).[k] =
       (map (fun (p : W8.t Array416.t) => BitUnpack (to_list p) (Top.dpow - 1) Top.dpow) (encoded_unflatten _a)).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => i0 t00 *;rewrite tP => k kb; smt().
wp; ecall (t0_decode_to_polynomial (Array416.init (fun (i_0 : int) => _a.[i * (d * n %/ 8) + i_0]))).
auto => /> &hr ?? H ?; split;1:smt().
move => ? rr Hrr;do split;1,2:smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ have -> : (lifts_wpolykvec
   (decoded_unflatten
      (Array1536.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else t0{hr}.[i_0])))).[k] =
    (lifts_wpolykvec (decoded_unflatten t0{hr})).[k]; last by smt().
  rewrite !mapiE 1..2:/# initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
  rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /= initiE 1:/# /= !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> : (lifts_wpolykvec
   (decoded_unflatten
      (Array1536.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else t0{hr}.[i_0])))).[i{hr}]  =
    (lifts_wpoly rr); last first.
  + rewrite Hrr mapiE 1:/# /=;congr;congr;rewrite /input_unflatten initiE 1:/# /= tP => ii iib.
    by rewrite initiE 1:/# get_of_list 1:/# /= nth_sub /#.
rewrite mapiE 1:/# /= initiE 1:/# /= tP => ii iib.
rewrite !mapiE 1,2:/# /= initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.


lemma t0_decode_ll : islossless  M.t0__decode.
proof.
proc => /=.
inline *;while (0<=i<=6) (6-i);auto; last by smt().
conseq(_: _ ==> true);1:smt().
while (0 <= input_offset <=  d * n %/ 8 - d /\ input_offset %% d = 0) (d * n %/ 8 - d - input_offset); auto => /> /#.
qed.

lemma t0_decode_ph _a  :
    phoare [ M.t0__decode : 
       encoded = _a 
     ==>
       lifts_wpolykvec (decoded_unflatten res) = 
           KArray.map (fun p => BitUnpack (to_list p) (dpow-1) dpow) (encoded_unflatten _a)
    ] = 1%r by conseq t0_decode_ll (t0_decode _a).


lemma t0_encode _a  :
    hoare [ M.t0____encode : 
       t0 = _a /\
       wpolykvec_srng (decoded_unflatten _a) (dpow - 1) dpow 
     ==>
      encoded_unflatten res = 
           KArray.map (fun p => (Array416.of_list W8.zero (BitPack p (dpow-1) dpow))) (lifts_wpolykvec (decoded_unflatten _a))
   ].
have Hkvec := mldsa65_kvec.
proc => /=.
while (0 <= j <= 6 /\ t0 = _a /\
       (forall k, 0 <= k < kvec =>
           wpoly_srng (dpow - 1) dpow (decoded_unflatten _a).[k]) /\
       (forall k, 0 <= k < j =>
        (encoded_unflatten encoded).[k] =
         (KArray.map (fun (p : poly) => Array416.of_list W8.zero (BitPack p (dpow - 1) dpow))
          (lifts_wpolykvec (decoded_unflatten _a))).[k]));
       last first.
       + auto => /> &hr; rewrite /wpolykvec_srng allP => *;do split; 1,2: smt().
         move => i0 t00 *;rewrite tP => k kb; smt().
wp; ecall (t0_encode_polynomial (Array256.init (fun (i : int) => t0.[n * j + i]))).
auto => /> &hr ?? H H0 ?; split.
+ move : (H j{hr} _); 1:smt().
  rewrite /decoded_unflatten initiE 1:/# /= /wpoly_srng !allP /= => Hbnd ii iib /=.
  rewrite initiE 1:/# /=.
  move : (Hbnd ii iib).
  by rewrite get_of_list // nth_sub //. 
move => ? rr Hrr;do split;1,2:smt().
move => k kbl kbh.
case(0<=k<j{hr}) => *.
+ have -> : 
   ((encoded_unflatten
   (Array2496.init
      (fun (i : int) => if j{hr} * 416 <= i < j{hr} * 416 + 416 then rr.[i - j{hr} * 416] else encoded{hr}.[i]))).[k] = (encoded_unflatten encoded{hr}).[k]); last by smt().
  rewrite initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
  by rewrite !get_of_list // !nth_sub // initiE 1:/# /= ifF 1:/#.
have -> : k = j{hr} by smt().
+ have -> : (
   ((encoded_unflatten
   (Array2496.init
      (fun (i : int) => if j{hr} * 416 <= i < j{hr} * 416 + 416 then rr.[i - j{hr} * 416] else encoded{hr}.[i]))).[j{hr}]  =
    rr)); last first.
  + have <-:= (Array416.to_listK W8.zero rr).
    rewrite Hrr mapiE 1:/# /=; congr;congr;rewrite /decoded_unflatten mapiE 1:/# /= initiE 1:/# /=;congr;rewrite tP => ??;rewrite get_of_list 1:/# /= initiE 1:/# /= nth_sub /#.
    rewrite /encoded_unflatten initiE 1:/# /= tP => i ib.
by rewrite get_of_list // nth_sub // initiE 1:/# /= /#. 
qed.

lemma t0_encode_ll : islossless  M.t0____encode.
proof.
proc => /=.
inline *;while (0<=j<=6) (6-j);auto; last by smt().
unroll for 28;wp.
conseq(_: _ ==> true);1:smt().
while (0 <= input_offset <=  n * 32 %/ 8 - 32 /\ input_offset %% 32 = 0) (n * 32 %/ 8 - 32 - input_offset); auto => /> /#.
qed.

lemma t0_encode_ph _a  :
    phoare [ M.t0____encode : 
       t0 = _a /\
       wpolykvec_srng (decoded_unflatten _a) (dpow - 1) dpow 
     ==>
      encoded_unflatten res = 
           KArray.map (fun p => (Array416.of_list W8.zero (BitPack p (dpow-1) dpow))) (lifts_wpolykvec (decoded_unflatten _a)) ] = 1%r by conseq t0_encode_ll (t0_encode _a).
