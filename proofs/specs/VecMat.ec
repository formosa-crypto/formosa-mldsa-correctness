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

(* Componentwise indexing of polylvec addition.
   Same hurdle as polykvec: (+) routes through abstract algebra (FIXME: PY). *)
lemma polylvec_add_iE (v1 v2 : polylvec) k :
  0 <= k < lvec => (v1 + v2).[k] = v1.[k] &+ v2.[k].
  admitted. (* FIXME: PY *)

op ntt_smul(p : poly, v : polylvec) : polylvec = map (fun p' => basemul p' p) v.

lemma invnttv_ntt_smul_k (c : poly) (sv : polylvec) (k : int) :
  0 <= k < lvec =>
  (invnttv (ntt_smul c sv)).[k] = invntt (basemul sv.[k] c).
proof. by move => hk; rewrite /invnttv /ntt_smul !mapiE 1:/# /=. qed.

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

lemma invnttv_ntt_smul_k (c : poly) (sv : polykvec) (k : int) :
  0 <= k < kvec =>
  (invnttv (ntt_smul c sv)).[k] = invntt (basemul sv.[k] c).
proof. by move => hk; rewrite /invnttv /ntt_smul !mapiE 1:/# /=. qed.

(* Componentwise indexing of polykvec subtraction.
   Hurdle: (-) routes through the abstract algebra (polykvec2alg / alg2polykvec),
   whose concrete definitions and alg2polykvecK are admitted (FIXME: PY).
   Once those are filled in this axiom becomes provable by unfolding. *)
lemma polykvec_sub_iE (v1 v2 : polykvec) k :
  0 <= k < kvec => (v1 - v2).[k] = v1.[k] &+ (&-) v2.[k].
  admitted. (* FIXME: PY *)

(* Componentwise indexing of polykvec addition.
   Same hurdle as subtraction: (+) routes through abstract algebra (FIXME: PY). *)
lemma polykvec_add_iE (v1 v2 : polykvec) k :
  0 <= k < kvec => (v1 + v2).[k] = v1.[k] &+ v2.[k].
  admitted. (* FIXME: PY *)

op smul(v : polykvec, c : coeff) : polykvec =
   KArray.map (fun (vi : poly) => map (fun ci => c*ci) vi) v.

op Power2Round(t : polykvec) : polykvec * polykvec =
   (map (fun p => (poly_Power2Round p).`1) t, 
    map (fun p => (poly_Power2Round p).`2) t).

op UseHint(h : polykvec, r : polykvec) : polykvec = 
    map2 poly_UseHint h r.

op MakeHint(v1 : polykvec, v2 : polykvec) : polykvec =
    map2 poly_MakeHint v1 v2.

op MakeHintImpl(v1 : polykvec, v2 : polykvec) : polykvec =
    map2 poly_MakeHintImpl v1 v2.

op infnorm_lt(v : polykvec, bound : int) : bool = 
  all (fun ii => all (fun jj => `|v.[ii].[jj]| < bound) (iota_ 0 256)) (iota_ 0 kvec).

import Bigint BIA. 
op hammw(v : polykvec, bound : int) : bool =
 big predT (fun ii => count (fun jj => v.[ii].[jj] <> Zq.zero) (iota_ 0 256)) (iota_ 0 kvec) <= bound.

op polykvec_HighBits(v : polykvec) : polykvec =
  map poly_HighBits v.

op polykvec_LowBits(v : polykvec) : polykvec =
  map poly_LowBits v.

(* When |cs2| <= Beta at every coefficient, LowBits(w-cs2) and LowBits(w)-cs2 agree
   for the infnorm check at threshold gamma2-Beta.  If cs2 were to cross a
   2*gamma2 rounding boundary, then |LowBits(w)-cs2| >= gamma2 > gamma2-Beta,
   making both sides false; in the no-crossing case the two representations are equal. *)
lemma bz_sync (w cs2 : polykvec) :
    infnorm_lt cs2 (Beta + 1) =>
    infnorm_lt (polykvec_LowBits (w - cs2)) (gamma2 - Beta) =
    infnorm_lt (polykvec_LowBits w - cs2) (gamma2 - Beta).
proof. admit. qed.

(* Coefficient-wise lift of MakeHintImpl_MakeHint_equiv from GFq.ec. *)
lemma polykvec_MakeHintImpl_MakeHint_equiv (w cs2 ct0 : polykvec) :
    infnorm_lt cs2 (Beta + 1) =>
    MakeHintImpl (polykvec_HighBits w) (polykvec_LowBits w - cs2 + ct0) =
    MakeHint (zerov - ct0) (w - cs2 + ct0).
proof. admit. qed.

end PolyKVec.

theory PolyMat.
type polymat = poly KLMatrix.t.
type apolymat = matrix.

op "_.[_<-_]" (m : polymat, rc : int * int, p : poly) =
        m.[rc.`1*lvec+rc.`2 <- p].

op nttm m = KLMatrix.map ntt m.
op invnttm m = KLMatrix.map invntt m.
op zerom : polymat = create poly_zero.

op row(m : polymat, r : int) : PolyLVec.polylvec = LArray.init (fun i => m.[r*lvec+i]).
op col(m : polymat, c : int) : PolyKVec.polykvec = KArray.init (fun i => m.[c+lvec*i]).
end PolyMat.

import PolyLVec PolyKVec PolyMat.

op ntt_dotp (v1 v2 : polylvec) : poly =
   foldr (fun (i : int) (a : poly) => (basemul v1.[i] v2.[i]) &+ a) poly_zero (iota_ 0 lvec).

op ntt_mulmxv(m : polymat, v : polylvec) : polykvec = 
   KArray.init (fun i => ntt_dotp (row m i) v).
 
op dotp_partial (v1 v2 : polylvec) (k : int) : poly =
  foldr (fun (i : int) (a : poly) => (basemul v1.[i] v2.[i]) &+ a)
        poly_zero (iota_ 0 k).

lemma dotp_partialS (v1 v2 : polylvec) (k : int) :
  0 <= k => dotp_partial v1 v2 (k + 1) = basemul v1.[k] v2.[k] &+ dotp_partial v1 v2 k.
proof. admitted. (* todo dotp algebra PY *)

lemma dotp_partial_ntt_dotp (v1 v2 : polylvec) :
  dotp_partial v1 v2 lvec = ntt_dotp v1 v2.
proof. by rewrite /dotp_partial /ntt_dotp. qed.

(* NTT/INTT cancellation + polynomial multiplication norm bound:
   invnttv(ntt_smul(ntt c)(nttv s2)) = c * s2 componentwise, and
   |c * s2|_inf <= tau * Eta = Beta when c has tau nonzero +-1 coefficients
   and |s2|_inf <= Eta.  The infnorm_lt c 2 hypothesis encodes the +-1 bound. *)
lemma cs2_norm_bound (c : poly) (s2 : polykvec) :
    infnorm_lt c 2 =>
    PolyKVec.infnorm_lt s2 (Eta + 1) =>
    PolyKVec.infnorm_lt (PolyKVec.invnttv (PolyKVec.ntt_smul (ntt c) (PolyKVec.nttv s2))) (Beta + 1).
proof. admit. qed.

