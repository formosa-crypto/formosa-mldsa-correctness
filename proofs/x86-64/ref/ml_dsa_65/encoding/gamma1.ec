require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings JWordList.

from JazzEC require import Ml_dsa_65.
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

op BitPack (w : poly) (a b : int) : W8.t list =
  let blen_ab = ilog 2 (a + b) + 1 in

  BitsToBytes
    (flatten
       (map (fun (wi : coeff) => IntegerToBits (b - as_sint wi) blen_ab)
          (to_list w))).

op BitUnpack (v : W8.t list) (a b : int) : poly =
  let c = ilog 2 (a + b) + 1 in
  let z = BytesToBits v in
  init
    (fun (i : int) =>
       nth witness (map (fun (co : bool list) => incoeff (b - BitsToInteger co)) (chunk c z)) i).


lemma pre_lane_commute_in_aligned ['a]
    (l : 'a list)
    (tobits : 'a -> bool list)
    (ofbits : bool list -> 'a)
    (P : 'a -> bool)
    (n : int) :
  0 < n =>
  (forall x, size (tobits x) = n) =>
  (forall x, ofbits (tobits x) = x) =>
  all P (map ofbits (chunk n (flatten (map tobits l)))) =
  all P l.
proof.
move => H H0 H1.
congr.
rewrite flattenK //; 1:by move => b;rewrite mapP;smt().
rewrite -map_comp /(\o).
have -> : (fun (x : 'a) => ofbits (tobits x))  = idfun by apply fun_ext;smt().
by apply map_id.
qed.


lemma map_chunk_flatten_id ['a] 
    (li : 'a list) 
    (tobitsi : 'a -> bool list)
    (ofbitsi : bool list -> 'a)
    (ni : int) :
  0 < ni =>  
  (forall x, size (tobitsi x) = ni) =>
  (forall x, ofbitsi (tobitsi x) = x) =>
    (map ofbitsi (chunk ni (flatten (map tobitsi li)))) = li.
proof.
move => *.
apply (eq_from_nth witness).
  + rewrite size_map size_chunk 1:/# (EclibExtra.size_flatten' ni);1: by smt(mapP).
    rewrite size_map /#.
  move => i; rewrite size_map size_chunk 1:/# (EclibExtra.size_flatten' ni);1: by smt(mapP).
  rewrite size_map => Hs.
  rewrite (nth_map []);1: by rewrite size_chunk 1:/# (EclibExtra.size_flatten' ni);by smt(size_map mapP).
  rewrite JWordList.nth_chunk 1,2:/#; 1: by rewrite (EclibExtra.size_flatten' ni);by smt(size_map mapP).
   have -> : (take ni (drop (ni * i) (flatten (map tobitsi li))))  = tobitsi (nth witness li i).
   + rewrite drop_flatten_ctt;1:smt(mapP).
     have /= -> := take_flatten_ctt ni 1 (drop i (map tobitsi li));1:smt(mem_drop mapP).
     rewrite (drop_take1_nth witness) /=;1:smt(size_map).
     rewrite flatten1 /= (nth_map witness) /#.
   by smt().
qed.

lemma post_lane_commute_in_aligned ['a 'b 'c]
    (li : 'a list)
    (loc : 'b list)
    (tobitsi : 'a -> bool list)
    (ofbitsi : bool list -> 'a)
    (tobitsoc : 'b -> bool list)
    (ofbitsoc : bool list -> 'b)
    (tobitso : 'c -> bool list)
    (ofbitso : bool list -> 'c)
    (f : 'a -> 'c)
    (ni no noc  : int) :
  0 < ni =>  0 < no => 0 < noc =>
  no %| noc*size loc =>
  size li = (noc*size loc) %/ no =>
  (forall x, size (tobitsi x) = ni) =>
  (forall x, ofbitsi (tobitsi x) = x) =>
  (forall x, size (tobitso x) = no) =>
  (forall x, ofbitso (tobitso x) = x) =>
  (forall x, size x = no => tobitso (ofbitso x) = x) =>
  (forall x, size (tobitsoc x) = noc) =>
  (forall x, ofbitsoc (tobitsoc x) = x) =>
map f (map ofbitsi (chunk ni (flatten (map tobitsi li)))) =
map ofbitso (chunk no (flatten (map tobitsoc loc))) =>
   flatten (map tobitsoc loc) =
   flatten (map tobitso (map f li)).
proof.
move => 12?.
rewrite map_chunk_flatten_id 1..3:/#.
move => ->.
rewrite -map_comp /(\o) /=. 
have [H _]:= (eq_in_map (fun (x : bool list) => tobitso (ofbitso x)) idfun (chunk no (flatten (map tobitsoc loc)))).
rewrite H /=;1:smt(in_chunk_size).
rewrite map_id.
rewrite chunkK 1:/#;1: rewrite (EclibExtra.size_flatten' noc);  smt(size_map mapP).
qed.


import Parameters.

(* Move to array theory *)
lemma all_tolist ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  (Array256.all p a) <=> (List.all p (to_list a))
    by rewrite /all !allP /to_list /mkseq /=;split => H x Hx;smt(mapP).

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

hint simplify flatten1.

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
  = l640_w8_ofbits (a256_w20_tobits (
       Array256.map (fun w => truncateu_32_20 (W32_sub (W32.of_int gamma1) w)) p)).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
rewrite /BitsToBytes !array256_mapE /=; do 3! congr.
rewrite /lifts_wpoly -map_comp &(eq_sym) -map_comp /(\o) /=  &(eq_in_map) /= => v vp.
 move: h => @/wpoly_srng /array256_allP /(_ v _) //= /= => h. 
rewrite incoeffK_sint_small 1:/# /W32_sub truncateu_32_20E W20.bits2wK;1: by rewrite size_take //.
rewrite /IntegerToBits /l ilog_gamma1 /= w2bitsE.
have  -> := BS2Int.int2bs_cat 20 32 (to_uint (W32.of_int Top.gamma1 - v)) _;1:smt().
rewrite take_catl;1: by rewrite BS2Int.size_int2bs.
rewrite {1}(: gamma1_bits = size (BS2Int.int2bs gamma1_bits (to_uint (W32.of_int Top.gamma1 - v))) );1: by rewrite BS2Int.size_int2bs.
rewrite take_size;congr.
have := (W32.of_uintK (Top.gamma1 - to_sint v)).
rewrite modz_small;1:by smt(pow2_64).
move => <-;congr. rewrite -W32.of_intD';congr.
rewrite W32.of_intN;congr. 
rewrite /to_sint /smod /=;smt(W32.to_uintK pow2_32).
qed.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
       polynomial = _a /\ wpoly_srng 524287 524288 _a
     ==>
       to_list res = BitPack (lifts_wpoly _a) (gamma1-1) gamma1
   ].
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
move=> &hr |> H.
have -> := (pre_lane_commute_in_aligned (to_list polynomial{hr}) W32.w2bits W32.bits2w pre_gamma1_encode_polynomial  32 _ _ _).
done.
smt().
smt().

(* Part 1 *)
apply/all_tolist. move: H.
rewrite /wpoly_srng.            (* FIXME *)
apply: all_imply => /=.
move=> w * @/pre_gamma1_encode_polynomial.
rewrite /W32_sub /= !sleE /gamma1 /= !of_sintK /W32.smod /= /#. (* FIXME: smt? *)

(* Part 2 *)
move=> &hr |> ? ae /= h.

have {h}h :=
  post_lane_commute_in_aligned<: W32.t, W8.t, W20.t>
    (to_list polynomial{hr}) (to_list ae)
    W32.w2bits W32.bits2w
    W8.w2bits W8.bits2w
    W20.w2bits W20.bits2w
    gamma1_encode_polynomial_lane
    32 20 8 _ _ _ _ _ _ _ _ _ _ _ _ h; move=> //. (* FIXME *)
- by rewrite Array640.size_to_list /(%|).
- by rewrite !size_to_list.
- by apply: W20.bits2wK.


apply/(inj_map W8.w2bits)/(flatten_ctt_inj 8) => //.
- by apply: W8.w2bits_inj.
- by move=> ? /mapP[? ->]; apply: W8.size_w2bits.
- by move=> ? /mapP[? ->]; apply: W8.size_w2bits.

have ? := in_chunk_size<:bool>.

rewrite BitPack_liftE ~-1:// h map_W8_w2bits_cancel ~-1:/# chunkK //.
- rewrite (size_flatten' 20) ?(size_map, size_iota) //=.
  by move=> bs /mapP[?] [_ ->]; rewrite W20.size_w2bits.
by rewrite array256_mapE.
qed.

op pre_gamma1_decode_to_polynomial(c : W20.t) = true.

op gamma1_decode_to_polynomial_lane(c : W20.t) : W32.t = 
    (W32_sub (W32.of_int gamma1) (zeroextu_20_32 c)).


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

abbrev l640_w8_tobits (a : W8.t Array640.t) : bool list  =
  flatten (List.map W8.w2bits (to_list a)).

abbrev l256_w20_ofbits (a : bool list) :  W20.t list   =
  List.map W20.bits2w (chunk 20 a).

abbrev a256_w20_ofbits (a : bool list) :  W20.t Array256.t   =
  Array256.of_list witness (l256_w20_ofbits a).


lemma BitUnack_liftE (bytes : W8.t Array640.t) :
    BitUnpack (to_list bytes) (gamma1 - 1) gamma1
  =
  Array256.map (fun c => incoeff (to_sint c))
    (Array256.map (fun w =>(W32_sub (W32.of_int gamma1) (zeroextu_20_32 w))) 
        (a256_w20_ofbits (l640_w8_tobits bytes))).
proof.
move=>  @/BitUnpack /=; rewrite tP => i ib.
rewrite initiE 1:// get_of_list 1://. 
pose l1 := List.map _ _.
pose l2 := List.map _ _.
have sl1 : size l1 = n.
+   rewrite /l1;rewrite !size_map size_iota ilog_gamma1 /= /BytesToBits.
  rewrite (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
have sl2 : size l2 = n.
+   rewrite /l2;rewrite !size_map size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /= /#.
suff : l1 = l2 by smt( nth_change_dfl).
apply (eq_from_nth witness) => /=;1: by smt().
move => k kb;rewrite !(nth_map witness).
+ rewrite ilog_gamma1 /= size_chunk 1:/# (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  by rewrite size_map /= size_to_list /#.
+ rewrite size_iota (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite size_map size_to_list /= ilog_gamma1 /#.
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
  rewrite size_map size_to_list /= ilog_gamma1 /#.
+ rewrite  (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite size_map size_to_list /=  /#.
rewrite ilog_gamma1 /= /zeroextu_20_32 /= /W20.to_uint W20.bits2wK.
+ rewrite size_take // size_drop 1:/# /max /= (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /= /#.
pose i1 := BitsToInteger _.
pose i2 := BS2Int.bs2int _.
have -> : i1 = i2 by smt().
rewrite of_sintK /smod /=.
have ? : 0 <= i2 <= 2*gamma1; last by smt().
split;1: by exact BS2Int.bs2int_ge0.
have := BS2Int.bs2int_le2Xs ((take gamma1_bits (drop (gamma1_bits * k) (l640_w8_tobits bytes)))).
+ rewrite size_take // size_drop 1:/# /max /= (size_flatten' 8);1: by smt(mapP W8.size_w2bits).
  rewrite !size_map !size_iota /max /= -/i2.
  pose ll := if _ then _ else _.
  have -> /= : ll = 20; by smt().
qed.

lemma gamma1_decode_to_polynomial _a :
   hoare [ M.gamma1____decode_to_polynomial :
       bytes = _a 
     ==>
       lifts_wpoly res = BitUnpack (to_list _a) (gamma1-1) gamma1
   ].
proc => /=. 
(* proc change ^while.1 : (W32.of_int gamma1); 1: by auto. 
proc change ^while.3 : (W32.of_int gamma1); 1: by auto. 
proc change ^while.2 : (W32_sub t0 (polynomial.[2 * i + 0])); 1: by auto.
proc change ^while.4 : (W32_sub t1 (polynomial.[2 * i + 1])); 1: by auto. *)
proc change ^while.3 : (sll_32 temp (W32.of_int 8)); 1: by auto.
proc change ^while.6 : (sll_32 temp (W32.of_int 16)); 1: by auto.
proc change ^while.9 : (W32_sub W32.zero coefficient); 1: by auto.
proc change ^while.13 : (srl_32 coefficient (W32.of_int w1_bits)); 1: by auto.
proc change ^while.15 : (sll_32 temp (W32.of_int w1_bits)); 1: by auto.
proc change ^while.18 : (sll_32 temp (W32.of_int 12)); 1: by auto.
proc change ^while.20 : (W32_sub W32.zero coefficient); 1: by auto.
proc change ^while.21 : (coefficient + W32.of_int 524288); 1: by auto.
unroll for ^while.

cfold 1.
wp -2. 
bdep 20 32 [_a] [bytes] [polynomial] gamma1_decode_to_polynomial_lane pre_gamma1_decode_to_polynomial.

(* Part 1 *)
by move=> &hr |>;rewrite /pre_gamma1_decode_to_polynomial /= allP /#.

(* Part 2 *)
move=> &hr |>  ae /= h.

have {h}h :=
  post_lane_commute_out_aligned<: W8.t, W20.t, W32.t>
    (to_list bytes{hr}) (to_list ae)
    W8.w2bits W8.bits2w
    W20.w2bits W20.bits2w
    W32.w2bits W32.bits2w
    gamma1_decode_to_polynomial_lane
    8 gamma1_bits 32 _ _ _ _ _ _ _ _ _ _ _ _ h; move=> //. (* FIXME *)
- by rewrite Array640.size_to_list /(%|).
- by rewrite !size_to_list //.
- by apply: W20.bits2wK.

rewrite /lifts_wpoly /=; apply (inj_eq Array256.to_list Array256.to_list_inj).


rewrite BitUnack_liftE ~-1:// !array256_mapE h; do 2!congr => //.
rewrite of_listK. 
- rewrite size_map size_chunk // (size_flatten' 8) => *;1:smt(mapP W8.size_w2bits).
  by rewrite size_map size_to_list /=.

done.

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
       (map (fun (p : W8.t Array640.t) => Top.BitUnpack (to_list p) (Top.gamma1 - 1) Top.gamma1) (input_unflatten _a)).[k]);
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
