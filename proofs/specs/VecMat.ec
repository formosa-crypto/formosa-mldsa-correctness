require import AllCore List StdBigop.
require import Parameters GFq Rq.
require DVect Subtype.
require import Array256.

import CDR Round Zq BigZMod PolyReduceZq MLDSAParams.

clone import DVect as VecMat with 
  theory DR <= DR,
  op HL.alpha <- 2*gamma2,
  op HL.d     <- d
proof 
  HL.ge2_alpha, 
  HL.alpha_halfq_le, 
  HL.even_alpha, 
  HL.alpha_almost_divides_q.
realize HL.ge2_alpha by smt(gamma2_bound).
realize HL.even_alpha by smt().
realize HL.alpha_halfq_le by smt(gamma2_bound).
realize HL.alpha_almost_divides_q by apply gamma2_div.

import VecMat.MatRq. (* Matrices and Vectors over Rq *)
import VecMat.HL.    (* highBitsV and lowBitsV with HL.alpha = 2 * gamma2 and HL.d = d *)

from Jasmin require import JArray. 
clone export PolyArray as LArray  with
        op size <- lvec
        proof ge0_size by smt(gt0_l).

clone export PolyArray as KArray  with
        op size <- kvec
        proof ge0_size by smt(gt0_k).

clone export PolyArray as KLMatrix  with
        op size <- kvec*lvec
        proof ge0_size by smt(gt0_l gt0_k).

theory PolyLVec.
type polylvec = poly LArray.t.
type apolylvec  = vector.

op polylvec2alg(v : polylvec) : apolylvec. (* Write me: PY *)
op alg2polylvec(v : apolylvec) : polylvec. (* Write me: PY *)

lemma polylvec2algK : cancel alg2polylvec polylvec2alg.
admitted. (* FIXME: PY *)

lemma alg2polylvecK : cancel polylvec2alg alg2polylvec.
admitted. (* FIXME: PY *)

op nttv v = LArray.map ntt v.
op invnttv v = LArray.map invntt v. 
op zerov : polylvec = LArray.init (fun i =>  poly_zero).

op (+) (v1 v2 : polylvec) : polylvec = alg2polylvec ((polylvec2alg v1) + (polylvec2alg v2)).
op ntt_smul(p : poly, v : polylvec) : polylvec = map (fun p' => basemul p' p) v.

op infnorm_lt(v : polylvec, bound : int) : bool =
  all (fun ii => all (fun jj => `|v.[ii].[jj]| < bound) (iota_ 0 256)) (iota_ 0 lvec).

lemma infnorm_lt_polyE (v : polylvec) (bound : int) :
  infnorm_lt v bound <=> all (fun i => infnorm_lt v.[i] bound) (iota_ 0 lvec).
proof.
by rewrite /infnorm_lt  allP /=; split => H i Hi /=.
qed.

op mods(v : polylvec, md : int) : polylvec = 
  map (fun (vi : poly) => map (fun c => incoeff (smod (asint c) md)) vi) v.

 end PolyLVec.

theory PolyKVec.
type polykvec = poly KArray.t.
type apolykvec  = vector.

op polykvec2alg(v : polykvec) : apolykvec. (* Write me: PY *)
op alg2polykvec(v : apolykvec) : polykvec. (* Write me: PY *)

lemma polykvec2algK : cancel alg2polykvec polykvec2alg.
admitted. (* FIXME: PY *)

lemma alg2polykvecK : cancel polykvec2alg alg2polykvec.
admitted. (* FIXME: PY *)


op nttv v = KArray.map ntt v.
op invnttv v = KArray.map invntt v.
op zerov : polykvec = create poly_zero.

op (+) (v1 v2 : polykvec) : polykvec = alg2polykvec ((polykvec2alg v1) + (polykvec2alg v2)).
op (-) (v1 v2 : polykvec) : polykvec = alg2polykvec ((polykvec2alg v1) - (polykvec2alg v2)).
op ntt_smul(p : poly, v : polykvec) : polykvec = map (fun p' => basemul p' p) v.

op smul(v : polykvec, c : coeff) : polykvec = 
   KArray.map (fun (vi : poly) => map (fun ci => c*ci) vi) v.

op Power2Round(t : polykvec) : polykvec * polykvec =
   (map (fun p => (poly_Power2Round p).`1) t, 
    map (fun p => (poly_Power2Round p).`2) t).

op UseHint(h : polykvec, r : polykvec) : polykvec = 
    map2 poly_UseHint h r.

op MakeHint(v1 : polykvec, v2 : polykvec) : polykvec =
    map2 poly_MakeHint v1 v2.

op infnorm_lt(v : polykvec, bound : int) : bool = 
  all (fun ii => all (fun jj => `|v.[ii].[jj]| < bound) (iota_ 0 256)) (iota_ 0 kvec).

import Bigint BIA. 
op hammw(v : polykvec, bound : int) : bool = 
 big predT (fun ii => count (fun jj => v.[ii].[jj] <> Zq.zero) (iota_ 0 256)) (iota_ 0 lvec) <= bound.

op polykvec_HighBits(v : polykvec) : polykvec = 
  map poly_HighBits v.

op polykvec_LowBits(v : polykvec) : polykvec = 
  map poly_LowBits v.

end PolyKVec.

theory PolyMat.
type polymat = poly KLMatrix.t.
type apolymat = matrix.

op "_.[_<-_]" (m : polymat, rc : int * int, p : poly) =
        m.[rc.`1*lvec+rc.`2 <- p].

op nttm m = KLMatrix.map ntt m.
op invnttm m = KLMatrix.map invntt m.
op zerom : polymat = create poly_zero.

op row(m : polymat, r : int) : PolyLVec.polylvec = LArray.init (fun i => m.[r*kvec+i]).
op col(m : polymat, c : int) : PolyKVec.polykvec = KArray.init (fun i => m.[c+lvec*i]).
end PolyMat.

import PolyLVec PolyKVec PolyMat.

op ntt_dotp (v1 v2 : polylvec) : poly =
   foldr (fun (i : int) (a : poly) => (basemul v1.[i] v2.[i]) &+ a) poly_zero (iota_ 0 lvec).

op ntt_mulmxv(m : polymat, v : polylvec) : polykvec = 
   KArray.init (fun i => ntt_dotp (row m i) v).
 
