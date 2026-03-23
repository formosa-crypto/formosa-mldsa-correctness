require import AllCore IntDiv List Ring BitEncoding.
require import Array256.

require import GFq Parameters.
import CDR Round Zq BigZMod PolyReduceZq.


(******************************************************)
(* Representations of polynomials in Zq[X]/(X^256+1)  *)
(******************************************************)

import PolyReduce.
type poly = coeff Array256.t.
type apoly = polyXnD1.
op poly2alg(p : poly) : apoly = oget (QSub.insub (canon (oget (to_poly (fun i => p.[i]))))).

op alg2poly(p : apoly) : poly = init (fun i => p.[i]).

lemma alg2polyK : cancel poly2alg alg2poly.
admitted. (* FIXME : PY *)

lemma poly2algK : cancel poly2alg alg2poly.
admitted. (* FIXME : PY *)

op (&*) (a b : poly) = alg2poly (( * ) (poly2alg a) (poly2alg b)).
op (&+) (a b : poly) = alg2poly (( + ) (poly2alg a) (poly2alg b)).
op (&-) (a   : poly) = alg2poly (PolyReduce.([-]) (poly2alg a)).
op poly_zero = create zero.


(**************************************************)
(**************************************************)

(* The NTT operation over ring elements *)

op zroot = incoeff 1753.

op br = BitEncoding.BitReverse.bsrev 8.


op ntt(p : poly) : poly.

op invntt(p : poly) : poly. 

(* The base multiplication in the NTT domain pointwise. *)

op basemul(a b : poly) :  poly = init (fun i => a.[i] * b.[i]).

op poly_Power2Round(p : poly) : poly * poly = 
     (init (fun i => (Power2Round p.[i]).`1), 
      init (fun i => (Power2Round p.[i]).`2)).

op poly_UseHint(h : poly, r : poly) : poly = 
     init (fun ii => UseHint (!h.[ii] = Zq.zero) r.[ii]).

op poly_MakeHint(p1 : poly, p2 : poly) : poly = 
     init (fun ii => incoeff (b2i (MakeHint p1.[ii] p2.[ii]))).

op poly_HighBits(p : poly) : poly = 
     init (fun ii => incoeff (HighBits p.[ii])).

op poly_LowBits(p : poly) : poly =
     init (fun ii => incoeff (LowBits p.[ii])).

op infnorm_lt (p : poly) (bound : int) : bool =
  all (fun j => `|p.[j]| < bound) (iota_ 0 256).
