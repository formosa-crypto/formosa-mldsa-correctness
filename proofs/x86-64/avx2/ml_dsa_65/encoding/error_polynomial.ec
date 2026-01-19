require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65_avx2.
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

op sigextu_4_32(a : W4.t) : W32.t = W32.of_int (to_sint a).
bind op [W4.t & W32.t] sigextu_4_32 "sextend".
realize bvsextendP.
move => bv;rewrite  /sigextu_4_32 /to_sint /smod /= !of_uintK /=.
case (8 <= to_uint bv); 2: smt(W4.to_uint_cmp).
have ? : 2^4 = 16 by auto => />.
move =>?;rewrite -{2}(oppzK (to_uint bv - 16)) modNz /=; smt(W4.to_uint_cmp). 
qed.
realize le_size by done.

lemma to_sint_uint_rng_pos_4(xx : W4.t) :
    0 <= to_sint xx  <=> 0 <= to_uint xx < 8.
 have /= Hxx := W4.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

lemma to_sint_uint_rng_neg_4(xx : W4.t) :
    to_sint xx < 0  <=> 8 <= to_uint xx < 16.
 have /= Hxx := W4.to_uint_cmp xx. 
 rewrite /to_sint /smod /= /#.
qed.

(* Circuit spec *)

op Eta = 4.
lemma ilog_Eta : ilog 2 (Eta + Eta) = 3 by rewrite /Eta /=.

op error_polynomial_encode_lane(c : W32.t) : W4.t = 
    truncateu32_4 (W32_sub (W32.of_int Eta) c).

lemma BitPack_liftE (p : wpoly) :
  wpoly_srng Eta Eta p =>
    BitPack (lifts_wpoly p) Eta Eta 
  = to_list (let mapped = init_256_4 (fun i => error_polynomial_encode_lane p.[i]) in
             init_128_8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 4].[(i*8+j) %% 4]))).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have Hlog := ilog_Eta.
have ? : size
  (flatten (map (fun (x : W32.t) => IntegerToBits (Eta - as_sint (incoeff (to_sint x))) (l + 1)) (to_list p))) = 256*4.
+  rewrite  (size_flatten_ctt (l+1)).
  +  by move => x; rewrite mapP => Hx;elim Hx => xw /= [? ->]; rewrite /IntegerToBits BS2Int.size_int2bs //.
  by rewrite size_map /= size_to_list  /l /= Hlog //=.

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
rewrite /error_polynomial_encode_lane .
pose v:=p.[(i * 8 + j) %/ 4].
have -> : p.[(8 * i + j) %/ (l + 1)] = v by smt().
move: h => @/wpoly_srng /array256_allP /(_ v _) //= /=.
+ rewrite /to_list /mkseq mapP; exists ((i * 8 + j) %/ 4); smt(mem_iota).
move => h. 
rewrite incoeffK_sint_small 1:/# /W32_sub truncateu_32_4E get_bits2w 1:/#.
rewrite nth_take 1,2:/# w2bitsE. 
have  -> := BS2Int.int2bs_cat 4 32 (to_uint (W32.of_int Eta - v)) _;1:smt().
rewrite /IntegerToBits nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt(). 
have := (W32.of_uintK (Eta- to_sint v)).
rewrite modz_small;1:by smt().
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr. 
rewrite /to_sint /smod /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT //= => ?.
congr;rewrite to_uint_eq of_uintK /=;smt(W32.to_uint_cmp pow2_32). 
qed. 

lemma encode _a :
   hoare [ M.error_polynomial__encode : 
       polynomial = _a /\ wpoly_srng 4 4 _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) Eta Eta
   ].
proc;inline * => /=.
proc change 1 : { temp <- W64.of_int 4097;}; 1: by auto.
proc change 2 : { shift <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().
proc change 5 : { eta_0 <- zeroextu256 temp; }.
+ auto => &1 &2 ->; rewrite /VMOV_64 zeroextu256E zeroextu256E.
  rewrite wordP => i ib.
  rewrite pack2E pack2E pack4E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  case (i %/ 64 = 0) => ?; 1: by rewrite ifT 1:/# initiE 1:/# /= get_of_list /#.
  case (i %/ 128 = 0) => ?; 2: by auto.
  rewrite initiE 1:/# /= get_of_list 1:/#.
  by have -> /= : (i %% 128 %/ 64) = 1 by smt().

proc change ^while.1 : { c0 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.4 : { c1 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.7 : { c2 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.10 : { c3 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.13 : { c4 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.16 : { c5 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.19 : { c6 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().
proc change ^while.22 : { c7 <- sliceget256_32_256 polynomial (input_offset*8);};1: by auto;smt().

proc change ^while.36 : {encoded <- sliceset128_8_256 encoded (output_offset*8) c0;}; 1: by auto;smt().

unroll for ^while.
cfold 8.
wp -2.

conseq (:  polynomial = init_256_32 (fun i => W32.one)  ==> 
           encoded = let mapped = init_256_4 (fun i => error_polynomial_encode_lane _a.[i]) in
             init_128_8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 4].[(i*8+j) %% 4])));last by circuit.

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

op  input_unflatten(a : 'a Array3200.t) =
     LArray.init (fun i => Array640.of_list witness (sub a (640*i) 640)).
op  output_unflatten(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

lemma gamma1_decode _a :
    lvec = 5 =>
    hoare [ M.gamma1____decode :
       encoded = _a 
     ==>
       lifts_wpolylvec (output_unflatten res) = 
           LArray.map (fun p => BitUnpack (to_list p) (gamma1-1) gamma1) (input_unflatten _a)
   ].
move => Hlvec.
proc => /=.
while (0 <= i <= 5 /\ encoded = _a /\
       forall k, 0 <= k < i =>
       (lifts_wpolylvec (output_unflatten decoded)).[k] =
       (map (fun (p : W8.t Array640.t) => BitUnpack (to_list p) (Top.gamma1 - 1) Top.gamma1) (input_unflatten _a)).[k]);
       last first.
       + auto => /> &hr *;do split;1: smt().
         move => r0 i0 *;rewrite tP => k kb; smt().
wp; ecall (gamma1_decode_to_polynomial (Array640.init (fun (i_0 : int) => _a.[i * (gamma1_bits * n %/ 8) + i_0]))).
auto => /> &hr ?? H ? rr Hrr;do split;1,2:smt().
move => k kbl kbh.
case(0<=k<i{hr}) => *.
+ have -> : (lifts_wpolylvec
   (output_unflatten
      (Array1280.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0])))).[k] =
    (lifts_wpolylvec (output_unflatten decoded{hr})).[k]; last by smt().
  rewrite !mapiE 1..2:/# initiE 1:/# /= initiE 1:/# /= tP =>  ii iib.
  rewrite mapiE 1:/# /= initiE 1:/# /= mapiE 1:/# /= initiE 1:/# /= !nth_sub 1,2:/# initiE 1:/# /= /#.
have -> : k = i{hr} by smt().
+ have -> : (lifts_wpolylvec
   (output_unflatten
      (Array1280.init
         (fun (i_0 : int) => if i{hr} * n <= i_0 < i{hr} * n + n then rr.[i_0 - i{hr} * n] else decoded{hr}.[i_0])))).[i{hr}]  =
    (lifts_wpoly rr); last first.
  + rewrite Hrr mapiE 1:/# /=;congr;congr;rewrite /input_unflatten initiE 1:/# /= tP => ii iib.
    by rewrite initiE 1:/# get_of_list 1:/# /= nth_sub /#.
rewrite mapiE 1:/# /= initiE 1:/# /= tP => ii iib.
rewrite !mapiE 1,2:/# /= initiE 1:/# /= nth_sub 1:/# initiE 1:/# /= /#.
qed.
