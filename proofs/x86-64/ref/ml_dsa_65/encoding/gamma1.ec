require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.
require import Bindings.

from JazzEC require import Ml_dsa_65.
from JazzEC require import Array256 Array640.
from Spec require import GFq Rq Serialization Conversion.

import CDR Round Zq.

type poly_t  = coeff Array256.t.
type polyw_t = W32.t Array256.t.

op liftu_wpoly (pw : polyw_t) : poly_t =
  map (fun x => incoeff (W32.to_uint x)) pw.

op lifts_wpoly (pw : polyw_t) : poly_t =
  map (fun x => incoeff (W32.to_sint x)) pw.

op unlift_poly (p : poly_t) : polyw_t = map (fun x => W32.of_int (asint x)) p.

op poly_urng(p : poly_t, b : int) = all (fun i => 0 <= asint i < b) p.
op poly_srng(p : poly_t, bl bh : int) = all (fun i => -bl <= as_sint i <= bh) p.

op wpoly_urng(pw : polyw_t, b : int) = all (fun i => 0 <= W32.to_uint i < b) pw.
op wpoly_srng(pw : polyw_t, bl bh : int) = all (fun i => -bl <= W32.to_sint i <= bh) pw.

(* natural spec and precondition *)

op gamma1 : int = 524288. (* 2**19 *)

(* Circuit spec and precondition *)

op pre_gamma1_encode_polynomial(c : W32.t) = 
    (W32_sub (W32.zero) (W32.of_int (524287))) \sle c /\ c \sle W32.of_int gamma1. 

op gamma1_encode_polynomial_lane(c : W32.t) : W20.t = 
    truncateu_32_20 (W32_sub (W32.of_int gamma1) c).

op BitPack (w : poly_t) (a b : int) : W8.t list =
  let blen_ab = ilog 2 (a + b) + 1 in

  BitsToBytes
    (flatten
       (map (fun (wi : coeff) => IntegerToBits (b - as_sint wi) blen_ab)
          (to_list w))).

import BitEncoding.
import BitChunking.

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
proof. admitted.

axiom pE : p = 8380417.

lemma all_tolist ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  (Array256.all p a) <=> (List.all p (to_list a)).
proof. admitted.

lemma all_imply ['a] (p q : 'a -> bool) (s : 'a Array256.t) :
  (forall x, p x => q x) => all p s => all q s.
proof. admitted.

lemma array256_mapE ['a 'b] (f : 'a -> 'b) (a : 'a Array256.t) :
  Array256.to_list (Array256.map f a) = List.map f (Array256.to_list a).
proof. admitted.

lemma array256_map_comp ['a 'b 'c] (f : 'a -> 'b) (g : 'b -> 'c) (a : 'a Array256.t) :
  Array256.map g ((Array256.map f a)) = Array256.map (fun x => g (f x)) a.
proof. admitted.

hint simplify flatten1.

lemma sincoeffK (c : int) :
  -((p-1) %/ 2) <= c < (p-1) %/ 2 => as_sint (incoeff c) = c.
proof. admitted.

lemma truncateu_32_20E (w : W32.t) : truncateu_32_20 w = W20.bits2w (take 20 (W32.w2bits w)).
proof. admitted.

lemma w2bitsE (w : W32.t) : w2bits w = BS2Int.int2bs 32 (W32.to_uint w).
proof. admitted.

lemma in_map_id ['a] (f : 'a -> 'a) (s : 'a list) :
  (forall x, x \in s => f x = x) => map f s = s.
proof. by move=> id_f; rewrite -{2}[s]map_id &(eq_in_map). qed.

lemma in_map_cancel ['a 'b] (f : 'a -> 'b) (g : 'b -> 'a) (s : 'a list) :
  (forall x, x \in s => g (f x) = x) => map g (map f s) = s.
proof. by move=> can_fg; rewrite -map_comp in_map_id. qed.

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

lemma array256_allP ['a] (p : 'a -> bool) (a : 'a Array256.t) :
  Array256.all p a <=> (forall x, x \in Array256.to_list a => p x).
proof. admitted.

lemma BitPack_liftE (p : polyw_t) :
  wpoly_srng p (gamma1 - 1) gamma1 =>

    BitPack (lifts_wpoly p) (gamma1 - 1) gamma1
  = l640_w8_ofbits (a256_w20_tobits (
       Array256.map (fun w => truncateu_32_20 (W32_sub (W32.of_int gamma1) w)) p)).
proof.
move=> h @/BitPack; (pose l := ilog 2 _) => /=.
rewrite /BitsToBytes !array256_mapE /=; do 3! congr.
rewrite -map_comp &(eq_sym) -map_comp /(\o) /= &(eq_in_map) /=.
move=> v vp; move: h => @/wpoly_srng /array256_allP /(_ v vp) /= ?.
rewrite sincoeffK 1:/# /W32_sub.

search Array256.to_list.
admitted.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
       polynomial = _a /\ wpoly_srng _a 524287 524288
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

from JazzEC require import Ml_dsa_65_barray.

lemma gamma1_encode_polynomial _a :
   hoare [ M.gamma1____encode_polynomial :
     polynomial = _a ==> true ].
proc.
