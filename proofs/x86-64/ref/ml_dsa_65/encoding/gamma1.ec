require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings JWordList.

from JazzEC require import Ml_dsa_65_ref.
from JazzEC require import Array256 Array640.
from Spec require import GFq Rq Serialization Conversion.
import BitEncoding.
import BitChunking.

import CDR Round Zq.

type wpoly = W32.t Array256.t.

op liftu_wpoly (pw : wpoly) : poly =
  map (fun w => incoeff (W32.to_uint w)) pw.

op lifts_wpoly (pw : wpoly) : poly =
  map (fun w => incoeff (W32.to_sint w)) pw.

op unlift_poly (p : poly) : wpoly = map (fun c => W32.of_int (asint c)) p.

op poly_urng(b : int, p : poly) = all (fun i => 0 <= asint i < b) p.
op poly_srng(bl bh : int, p : poly) = all (fun i => -bl <= as_sint i <= bh) p.

op wpoly_urng(b : int, pw : wpoly) = all (fun i => 0 <= W32.to_uint i < b) pw.
op wpoly_srng(bl bh : int, pw : wpoly) = all (fun i => -bl <= W32.to_sint i <= bh) pw.

(* natural spec and precondition *)
op gamma1 : int = 524288. (* 2**19 *) 

(* Circuit spec and precondition *)

op pre_gamma1_encode_polynomial(c : W32.t) = 
    (W32_sub (W32.zero) (W32.of_int (524287))) \sle c /\ c \sle W32.of_int gamma1. 

op gamma1_encode_polynomial_lane(c : W32.t) : W20.t = 
    truncateu_32_20 (W32_sub (W32.of_int gamma1) c).

import Parameters.

 
(* Move to array theory *)
lemma all_tolist ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  (Array256.all p a) <=> (List.all p (to_list a)) by 
  rewrite /all !allP /to_list /mkseq /=;split => H x Hx; 
   [have /# := mapP ("_.[_]" a) (iota_ 0 n) x | smt(mapP)].
   
lemma all_imply ['a] (p q : 'a -> bool) (s : 'a Array256.t) :
  (forall x, p x => q x) => all p s => all q s
  by rewrite /all !allP /to_list /mkseq /= => H x Hx;smt(mapP).

lemma array256_mapE ['a 'b] (f : 'a -> 'b) (a : 'a Array256.t) :
  Array256.to_list (Array256.map f a) = List.map f (Array256.to_list a).
  rewrite /all /to_list /mkseq /= -{1}map_comp /(\o) /=.
  apply (eq_from_nth witness);1: by rewrite !size_map.
  move => i;rewrite !size_map size_iota /max /= => ib.
  rewrite !(nth_map witness) /=;1,2:smt(size_map size_iota).
  by rewrite /map initiE /=;1:by rewrite nth_iota /#.
qed.
  
lemma array256_map_comp ['a 'b 'c] (f : 'a -> 'b) (g : 'b -> 'c) (a : 'a Array256.t) :
  Array256.map g ((Array256.map f a)) = Array256.map (fun x => g (f x)) a
  by rewrite /map tP => i ib;smt(Array256.initiE).

lemma array256_allP ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  Array256.all p a <=> (forall x, x \in Array256.to_list a => p x).
proof. by rewrite all_tolist allP. qed.
(* *)

(* move to list theory *)
lemma in_map_id ['a] (f : 'a -> 'a) (s : 'a list) :
  (forall x, x \in s => f x = x) => map f s = s.
proof. by move=> id_f; rewrite -{2}[s]map_id &(eq_in_map). qed.

lemma in_map_cancel ['a 'b] (f : 'a -> 'b) (g : 'b -> 'a) (s : 'a list) :
  (forall x, x \in s => g (f x) = x) => map g (map f s) = s.
proof. by move=> can_fg; rewrite -map_comp in_map_id. qed.

(* *)

lemma truncateu_32_20E (w : W32.t) : truncateu_32_20 w = W20.bits2w (take 20 (W32.w2bits w)).
proof.
rewrite /truncateu_32_20 W20.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : gamma1_bits = size (take gamma1_bits (w2bits w)) by rewrite size_take //.
by rewrite BS2Int.bs2intK.
qed.

lemma w2bitsE (w : W32.t) : w2bits w = BS2Int.int2bs 32 (W32.to_uint w).
proof. rewrite to_uintE;smt(W32.size_w2bits BS2Int.bs2intK). qed.

lemma map_W8_w2bits_cancel (s : bool list list) :
     (forall bs, bs \in s => size bs = 8)
  => map W8.w2bits (map W8.bits2w s) = s.
proof.
by move=> h; rewrite in_map_cancel // => bs /h; apply: W8.bits2wK.
qed.

abbrev a256_w20_tobits (a : W20.t Array256.t) : bool list =
  flatten (List.map (W20.w2bits) (Array256.to_list a)).

abbrev l640_w8_ofbits (a : bool list) : W8.t list =
  List.map W8.bits2w (chunk 8 a).

abbrev a640_w8_ofbits (a : bool list) : W8.t Array640.t =
  Array640.of_list witness (l640_w8_ofbits a).

lemma ilog_gamma1 : ilog 2 (gamma1 - 1 + gamma1) = 19 by rewrite /gamma1 /=.
 
lemma BitPack_liftE (p : wpoly) :
  wpoly_srng (gamma1 - 1) gamma1 p =>
    BitPack (lifts_wpoly p) (gamma1 - 1) gamma1
  = to_list (let mapped = init_256_20 (fun i => gamma1_encode_polynomial_lane p.[i]) in
             init_array640_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 20].[(i*8+j) %% 20]))).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
have ? := ilog_gamma1.
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
rewrite nth_take 1,2:/#. 
rewrite /IntegerToBits w2bitsE. 
have  -> := BS2Int.int2bs_cat 20 32 (to_uint (W32.of_int Top.gamma1 - v)) _;1:smt().
rewrite nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt(). 
have := (W32.of_uintK (Top.gamma1 - to_sint v)).
rewrite modz_small;1:by smt(pow2_64).
move => <-; rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr. 
rewrite /to_sint /smod /=.
case (2147483648 <= to_uint v) => ?;last by smt(W32.to_uintK pow2_32).
move : h; rewrite /to_sint /smod ifT //= => ?.
by smt(@W32 pow2_32). 
qed.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
       polynomial = _a /\ wpoly_srng 524287 524288 _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) (gamma1-1) gamma1
   ].
proc => /=.
proc change ^while.1 : { t0 <- W32.of_int gamma1;}; 1: by auto.
proc change ^while.2 : {t0 <- W32_sub t0 (polynomial.[2 * i + 0]);}; 1: by auto.
proc change ^while.3 : { t1 <- W32.of_int gamma1;}; 1: by auto.
proc change ^while.4 : { t1 <- W32_sub t1 (polynomial.[2 * i + 1]);}; 1: by auto.
proc change ^while.8 : { encoded_bytes  <- srl_32 encoded_bytes (W32.of_int 8);}; 1: by auto.
proc change ^while.11 : { encoded_bytes  <- srl_32 encoded_bytes (W32.of_int 16);}; 1: by auto.
proc change ^while.14 : { encoded_bytes  <- sll_32 encoded_bytes (W32.of_int 4);}; 1: by auto.
proc change ^while.18 : { encoded_bytes  <- srl_32 encoded_bytes (W32.of_int 4);}; 1: by auto.
proc change ^while.21 : { encoded_bytes  <- srl_32 encoded_bytes (W32.of_int 12);}; 1: by auto.
proc change ^while.15: { byte <- (byte  `&` W8.of_int 15) `|` (truncateu8 encoded_bytes);}; 1:by admit.
unroll for ^while.
cfold 1.
wp -2.
conseq (:  polynomial = _a ==>
           encoded = let mapped = init_256_20 (fun i => gamma1_encode_polynomial_lane _a.[i]) in
             init_array640_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 20].[(i*8+j) %% 20]))); last by circuit.

+ by auto.
+ by move => &hr [<- Hrng] ? /= => ->;rewrite BitPack_liftE //=.

qed.

op pre_gamma1_decode_to_polynomial(c : W20.t) = true.

op gamma1_decode_to_polynomial_lane(c : W20.t) : W32.t = 
    (W32_sub (W32.of_int gamma1) (zeroextu_20_32 c)).


abbrev l640_w8_tobits (a : W8.t Array640.t) : bool list  =
  flatten (List.map W8.w2bits (to_list a)).

abbrev l256_w20_ofbits (a : bool list) :  W20.t list   =
  List.map W20.bits2w (chunk 20 a).

abbrev a256_w20_ofbits (a : bool list) :  W20.t Array256.t   =
  Array256.of_list witness (l256_w20_ofbits a).


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
rewrite ilog_gamma1 /= /zeroextu_20_32. print nth_chunk.
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
proc change ^while.3 : { temp <- sll_32 temp (W32.of_int 8);}; 1: by auto.
proc change ^while.6 : {temp <- sll_32 temp (W32.of_int 16);}; 1: by auto.
proc change ^while.9 : {coefficient <- W32_sub W32.zero coefficient;}; 1: by auto.
proc change ^while.13 : {coefficient <- srl_32 coefficient (W32.of_int w1_bits);}; 1: by auto.
proc change ^while.15 : {temp <- sll_32 temp (W32.of_int w1_bits);}; 1: by auto.
proc change ^while.18 : {temp <- sll_32 temp (W32.of_int 12);}; 1: by auto.
proc change ^while.20 : { coefficient <- W32_sub W32.zero coefficient;}; 1: by auto.
proc change ^while.21 : { coefficient <- coefficient + W32.of_int 524288;}; 1: by auto.
unroll for ^while.

cfold 1.
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

type wpolylvec = wpoly LArray.t. 

op liftu_wpolylvec(wv : wpolylvec) : polylvec =
  map liftu_wpoly wv.

op lifts_wpolylvec (wv : wpolylvec) : polylvec =
  map lifts_wpoly wv.

op unlift_polylvec (v : polylvec) : wpolylvec = map unlift_poly v.

op polylvec_urng(p : polylvec, b : int) = all (poly_urng b) p.
op polylvec_srng(p : polylvec, bl bh : int) = all (poly_srng bl bh) p.

op wpolylvec_urng(pw : wpolylvec, b : int) = all (wpoly_urng b) pw.
op wpolylvec_srng(pw : wpolylvec, bl bh : int) = all (wpoly_srng bl bh) pw.

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
