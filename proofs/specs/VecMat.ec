require import AllCore List.
require import Parameters GFq Rq.
require DVect Subtype.

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

theory PolyLVec.
subtype polylvec  =
  { x : vector | size x = lvec }.
realize inhabited by exists (offunv (witness,lvec)); rewrite /size offunvK;smt(gt0_l).
op "_.[_]" (v : polylvec) (i : int) : poly = (val v).[i]. 
op "_.[_<-_]" (v : polylvec) (i : int) (c : poly) : polylvec = 
    (insubd (offunv (fun k => if k = i then c else (val v).[k],lvec))).
op mapv(f : poly -> poly, v : polylvec) : polylvec =
    (insubd (mapv f (val v))).
op nttv v = mapv ntt v.
op invnttv v = mapv invntt v.
op zerov : polylvec = (insubd (zerov lvec)).
op (+) (v1 v2 : polylvec) : polylvec = insubd (val v1 + val v2).
op ntt_smul(p : poly, v : polylvec) : polylvec = mapv (fun p' => basemul p' p) v.

   
op infnorm(v : polylvec, bound : int) : bool = 
  all (fun ii => all (fun jj => absZq v.[ii].[jj] < bound) (iota_ 0 256)) (iota_ 0 lvec).

op mods(v : polylvec, md : int) : polylvec = 
  mapv (fun (vi : poly) => pi (BasePoly.to_polyd 
     (fun i => let c = ((BasePoly.of_poly (repr vi)) i) in
          incoeff (smod (asint c) md)))) v.
end PolyLVec.

theory PolyKVec.
subtype polykvec  =
  { x : vector | size x = kvec }.
realize inhabited by exists (offunv (witness,kvec)); rewrite /size offunvK;smt(gt0_k).
op "_.[_]" (v : polykvec) (i : int) : poly = (val v).[i]. 
op "_.[_<-_]" (v : polykvec) (i : int) (c : poly) : polykvec = 
    (insubd (offunv (fun k => if k = i then c else (val v).[k],kvec))).
op mapv(f : poly -> poly, v : polykvec) : polykvec =
    (insubd (mapv f (val v))).
op nttv v = mapv ntt v.
op invnttv v = mapv invntt v.
op zerov : polykvec = (insubd (zerov kvec)).
op (+) (v1 v2 : polykvec) : polykvec = insubd (val v1 + val v2).
op (-) (v1 v2 : polykvec) : polykvec = insubd (val v1 - val v2).
op ntt_smul(p : poly, v : polykvec) : polykvec = mapv (fun p' => basemul p' p) v.
op smul(v : polykvec, c : coeff) : polykvec = 
   mapv (fun (vi : poly) => pi (BasePoly.polyZ c (repr vi))) v.

op Power2Round(t : polykvec) : polykvec * polykvec =
   (mapv (fun p => (poly_Power2Round p).`1) t, 
    mapv (fun p => (poly_Power2Round p).`2) t).


op UseHint(h : polykvec, r : polykvec) : polykvec = 
    (insubd (offunv (fun k => poly_UseHint h.[k] r.[k],kvec))).

op MakeHint(v1 : polykvec, v2 : polykvec) : polykvec = 
    (insubd (offunv (fun k => poly_MakeHint v1.[k] v2.[k],kvec))).


op infnorm(v : polykvec, bound : int) : bool = 
  all (fun ii => all (fun jj => absZq v.[ii].[jj] < bound) (iota_ 0 256)) (iota_ 0 kvec).

op hammw(v : polykvec, bound : int) : bool = 
  all (fun ii => count (fun jj => v.[ii].[jj] <> Zq.zero) (iota_ 0 256) <= bound) (iota_ 0 lvec).

op polykvec_HighBits(v : polykvec) : polykvec = 
  mapv poly_HighBits v.

op polykvec_LowBits(v : polykvec) : polykvec = 
  mapv poly_LowBits v.

end PolyKVec.

theory PolyMat.
subtype polymat  =
  { x : matrix | size x = (kvec,lvec) }.
realize inhabited by exists (offunm (witness,kvec,lvec)); rewrite size_offunm;smt(gt0_k gt0_l).
op "_.[_]" (m : polymat) (ij : int * int) : poly = (val m).[ij].
op "_.[_<-_]" (m : polymat) (ij : int * int) (c : poly) : polymat = 
    (insubd (offunm (fun k l => if (k,l) = ij then c else (val m).[k,l],lvec,kvec))).
op mapm(f : poly -> poly, m : polymat) : polymat =
    (insubd (mapm f (val m))).
op nttm m = mapm ntt m.
op invnttm m = mapm invntt m.
op zerom : polymat = (insubd (zerom lvec kvec)).
end PolyMat.

import PolyLVec PolyKVec PolyMat.

op ntt_dotp (v1 v2 : vector) : polyXnD1 =
      Big.BAdd.bigi predT (fun (i : int) => basemul v1.[i] v2.[i]) 0 (max (size v1) (size v2)).

op ntt_mmul (m1 m2 : matrix) : QuotientMat.matrix =
      offunm (fun (i j : int) => ntt_dotp (row m1 i) (col m2 j), rows m1, cols m2).

op ntt_mulmxv(m : polymat, v : polylvec) : polykvec = 
   PolyKVec.insubd (col (ntt_mmul (val m) (colmx (val v))) 0).
  

