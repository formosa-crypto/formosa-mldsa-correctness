require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings JWordList.

from JazzEC require import Ml_dsa_65_ref.
from JazzEC require import Array256 Array320.
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
op bitlenqm1md : int = 10 . (* bitlen (q-1) - d = 23 - 13 *)
op b_t1 = 1023. (* 2^bitlenqm1md - 1 *)

(* Circuit spec and precondition *)

op pre_t1_encode_polynomial(c : W32.t) = c \ule W32.of_int b_t1. 

op t1_encode_polynomial_lane(c : W32.t) : W10.t = 
    truncateu_32_10  c.

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

lemma truncateu_32_10E (w : W32.t) : truncateu_32_10 w = W10.bits2w (take 10 (W32.w2bits w)).
proof.
rewrite /truncateu_32_10 W10.of_intE W32.to_uintE BS2Int.bs2int_mod //;congr.
have {1}-> : 10 = size (take 10 (w2bits w)) by rewrite size_take //.
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

abbrev a256_w10_tobits (a : W10.t Array256.t) : bool list =
  flatten (List.map (W10.w2bits) (Array256.to_list a)).

abbrev l320_w8_ofbits (a : bool list) : W8.t list =
  List.map W8.bits2w (chunk 8 a).

abbrev a320_w8_ofbits (a : bool list) : W8.t Array320.t =
  Array320.of_list witness (l320_w8_ofbits a).

lemma ilog_b_t1 : ilog 2 b_t1 = bitlenqm1md - 1 by rewrite /b_t1 /=.

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
rewrite /IntegerToBits w2bitsE. 
have  -> := BS2Int.int2bs_cat 10 32 (to_uint v) _;1:smt().
rewrite nth_cat ifT;1: by rewrite BS2Int.size_int2bs /#.
congr;2:smt().
congr;1:smt().
smt().
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
print w1_bits. 
proc change ^while.29 : { encoded_bytes <- srl_32 encoded_bytes (W32.of_int 2);}; 1: by auto.
proc change ^while.9: { encoded_bytes <- (encoded_bytes  `&` W32.of_int 3) `|` encoded_byte;};1:by admit.
proc change ^while.17: { encoded_bytes <- (encoded_bytes  `&` W32.of_int 15) `|` encoded_byte;};1:by admit.
proc change ^while.25: { encoded_bytes <- (encoded_bytes  `&` W32.of_int 63) `|` encoded_byte;};1:by admit.  

unroll for ^while.
cfold 1. cfold 1.
wp -3.

conseq (:  t1 = _a ==>
    encoded = let mapped = init_256_10 (fun i => t1_encode_polynomial_lane _a.[i]) in
    init_array320_w8 (fun i => W8.init (fun j => mapped.[(i*8+j) %/ 10].[(i*8+j) %% 10]))); last by circuit. 

+ by auto.
+ by move => &hr [<- Hrng] ? /= => ->;rewrite SimpleBitPack_liftE //=.
  
qed.

op pre_t1_decode_to_polynomial(c : W10.t) = true.

op t1_decode_to_polynomial_lane(c : W10.t) : W32.t = 
    zeroextu10_32 c.


lemma post_lane_commute_out_aligned ['a 'b 'c]
    (lic : 'a list) 
    (lo : 'c list) 
    (tobitsic : 'a -> bool list)
    (ofbitsic : bool list -> 'a)
    (tobitsi : 'b -> bool list)
    (ofbitsi : bool list -> 'b)
    (tobitso : 'c -> bool list)
    (ofbitso : bool list -> 'c)
    (f : 'b -> 'c)
    (nic ni no  : int) :
  0 < nic =>  0 < ni => 0 < no => 
  ni %| nic*size lic =>
  size lo = (nic*size lic) %/ ni =>
  (forall x, size (tobitsic x) = nic) =>
  (forall x, ofbitsic (tobitsic x) = x) =>
  (forall x, size (tobitsi x) = ni) =>
  (forall x, ofbitsi (tobitsi x) = x) =>
  (forall x, size x = ni => tobitsi (ofbitsi x) = x) =>
  (forall x, size (tobitso x) = no) =>
  (forall x, ofbitso (tobitso x) = x) =>
map f (map ofbitsi (chunk ni (flatten (map tobitsic lic)))) =
map ofbitso (chunk no (flatten (map tobitso lo))) => 
   lo =
   map f (map ofbitsi (chunk ni (flatten (map tobitsic lic)))).
move => ????????????; rewrite  map_chunk_flatten_id /#.
qed.

abbrev l320_w8_tobits (a : W8.t Array320.t) : bool list  =
  flatten (List.map W8.w2bits (to_list a)).

abbrev l256_w10_ofbits (a : bool list) :  W10.t list   =
  List.map W10.bits2w (chunk 10 a).

abbrev a256_w10_ofbits (a : bool list) :  W10.t Array256.t   =
  Array256.of_list witness (l256_w10_ofbits a).


lemma SimpleBitUnpack_liftE (bytes : W8.t Array320.t) :
    SimpleBitUnpack (to_list bytes) b_t1
  =
  Array256.map (fun c => incoeff (to_uint c))
    (Array256.map zeroextu10_32 
        (a256_w10_ofbits (l320_w8_tobits bytes))).
proof.
move=>  @/SimpleBitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// get_of_list 1://. 
pose l1 := List.map _ _.
pose l2 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota /BytesToBits.
  rewrite (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /b_t1 /#.
have sl2 : size l2 = n.
+   rewrite /l2;rewrite !size_map size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
suff : l1 = l2 by smt( nth_change_dfl).
apply (eq_from_nth witness) => /=;1: by smt().
move => k kb;rewrite !(nth_map witness).
+ rewrite /b_t1 size_chunk 1:/# (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map /= size_to_list /#.
+ rewrite size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite /b_t1 size_map size_to_list /= /#.
+ rewrite !size_map size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite size_map size_to_list /= /#.
+ rewrite !size_map size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite size_map size_to_list /= /#.
+ rewrite size_chunk 1:/# (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map /= size_to_list /#.
+ rewrite size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite size_map size_to_list /=  /#.
simplify.
congr; rewrite /W32_sub !nth_iota.
+ rewrite  (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite /b_t1 size_map size_to_list /= /#.
+ rewrite  (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite size_map size_to_list /=  /#.
rewrite /b_t1 /zeroextu10_32 /= /W10.to_uint W10.bits2wK.
+ rewrite size_take // size_drop 1:/# /max /= (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /= /#.
pose i1 := BitsToInteger _.
pose i2 := BS2Int.bs2int _.
have -> : i1 = i2 by smt().
rewrite of_uintK  /=.
have ? : 0 <= i2 <= b_t1; last by smt().
split;1: by exact BS2Int.bs2int_ge0.
have := BS2Int.bs2int_le2Xs ((take 10 (drop (10 * k) (l320_w8_tobits bytes)))).
+ rewrite size_take // size_drop 1:/# /max /= (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /= -/i2.
  pose ll := if _ then _ else _.
  have -> /= : ll = 10; by smt().
qed.

lemma t1_decode_polynomial _a :
   hoare [ M.t1__decode_polynomial :
       encoded = _a 
     ==>
       liftu_wpoly res = SimpleBitUnpack (to_list _a) b_t1
   ].
proc => /=. 
proc change ^while.6 : (sll_32 temp1 (W32.of_int 8)); 1: by auto.
proc change ^while.11 : (srl_32 temp2 (W32.of_int 2)); 1: by auto.
proc change ^while.15 : (sll_32 temp1 (W32.of_int 6)); 1: by auto.
proc change ^while.20 : (srl_32 temp2 (W32.of_int w1_bits)); 1: by auto.
proc change ^while.24 : (sll_32 temp1 (W32.of_int w1_bits)); 1: by auto.
proc change ^while.29 : (srl_32 temp2 (W32.of_int 6)); 1: by auto.
proc change ^while.32 : (sll_32 temp1 (W32.of_int 2)); 1: by auto.

unroll for ^while.

cfold 1. cfold 1.
wp -3. 
bdep 10 32 [_a] [encoded] [t1] t1_decode_to_polynomial_lane pre_t1_decode_to_polynomial.

(* Part 1 *)
by move=> &hr |>;rewrite /pre_t1_decode_to_polynomial /= allP /#.

(* Part 2 *)
move=> &hr |>  ae /= h.

have {h}h :=
  post_lane_commute_out_aligned<: W8.t, W10.t, W32.t>
    (to_list encoded{hr}) (to_list ae)
    W8.w2bits W8.bits2w
    W10.w2bits W10.bits2w
    W32.w2bits W32.bits2w
    t1_decode_to_polynomial_lane
    8 10 32 _ _ _ _ _ _ _ _ _ _ _ _ h; move=> //. (* FIXME *)
- by rewrite Array320.size_to_list /(%|).
- by rewrite !size_to_list //.
- by apply: W10.bits2wK.

rewrite /liftu_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).


rewrite SimpleBitUnpack_liftE ~-1:// !array256_mapE h;  do 2!congr => //.
rewrite of_listK. 
- rewrite size_map size_chunk // (size_flatten' 8) => *;1:smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /=.

done.

qed.

import VecMat PolyKVec.

type wpolykvec = wpoly KArray.t. 

op liftu_wpolykvec(wv : wpolykvec) : polykvec =
  map liftu_wpoly wv.

op lifts_wpolykvec (wv : wpolykvec) : polykvec =
  map lifts_wpoly wv.

op unlift_polykvec (v : polykvec) : wpolykvec = map unlift_poly v.

op polykvec_urng(p : polykvec, b : int) = all (poly_urng b) p.
op polykvec_srng(p : polykvec, bl bh : int) = all (poly_srng bl bh) p.

op wpolykvec_urng(pw : wpolykvec, b : int) = all (wpoly_urng b) pw.
op wpolykvec_srng(pw : wpolykvec, bl bh : int) = all (wpoly_srng bl bh) pw.

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
