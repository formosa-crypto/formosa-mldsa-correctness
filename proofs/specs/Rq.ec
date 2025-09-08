require import AllCore IntDiv List Ring BitEncoding.

require import GFq.
import CDR Round Zq BigZMod PolyReduceZq.

(******************************************************)
(* Representations of polynomials in Zq[X]/(X^256+1)  *)
(******************************************************)

type poly = polyXnD1.
op (&*) = PolyReduceZq.( * ) .
op (&+) = PolyReduceZq.( + ) .
op (&-) = PolyReduceZq.([-]).

op init_poly(coeffs : int -> coeff) : poly = 
   oget (QSub.insub (oget (BasePoly.to_poly 
      (fun i => if !(0 <= i < 256) then zero else coeffs i)))).

op "_.[_<-_]" (p : poly, i : int, c : coeff) = 
   init_poly (fun ii => if ii = i then c else p.[i]).

op to_list(p : poly) = mkseq (fun i => p.[i]) 256.

(**************************************************)
(**************************************************)

(* The NTT operation over ring elements *)

op zroot = incoeff 1753.

op br = BitEncoding.BitReverse.bsrev 8.


op ntt(p : poly) : poly.

op invntt(p : poly) : poly. 

(* The base multiplication in the NTT domain pointwise. *)

op basemul(a b : poly) :  poly = init_poly (fun i => a.[i] * b.[i]).

op poly_Power2Round(p : poly) : poly * poly = 
     (init_poly (fun i => (Power2Round p.[i]).`1), 
      init_poly (fun i => (Power2Round p.[i]).`2)).

op poly_UseHint(h : poly, r : poly) : poly = 
     init_poly (fun ii => UseHint (!h.[ii] = Zq.zero) r.[ii]).

op poly_MakeHint(p1 : poly, p2 : poly) : poly = 
     init_poly (fun ii => incoeff (b2i (MakeHint p1.[ii] p2.[ii]))).

op poly_HighBits(p : poly) : poly = 
     init_poly (fun ii => incoeff (HighBits p.[ii])).

op poly_LowBits(p : poly) : poly = 
     init_poly (fun ii => incoeff (LowBits p.[ii])).
