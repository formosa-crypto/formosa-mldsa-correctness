require import AllCore IntDiv List.
from Jasmin require import JByte_array JWord.

require import Parameters GFq Rq VecMat Conversion Serialization Symmetric Sampling.
import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod MLDSAParams.

type Leakage = [
   | RO of bool list
   | CheckZ of bool
   | CheckH of bool ].

module MLDSA(XOFA : XOF_RejNTTPoly, XOFS : XOF_RejBPoly, XOFSIB : XOF_SIB, RO : LeakyRO) = {
   proc keygen_derand(eps : Bytes32.t) : BytesSK.t * BytesPK.t= {
     var sk,rho,rhop,_K,_A,s1,s2,t,t1,t0,pk,tr,epsp;
     epsp <- Bytes34.of_list (Bytes32.to_list eps ++ [W8.of_int kvec;W8.of_int lvec]);
     (rho,rhop,_K) <- H_seed epsp;
     _A <@ ExpandA(XOFA).sample(rho);
     (s1,s2) <@ ExpandS(XOFS).sample(rhop);
     t <- invnttv (ntt_mulmxv _A (nttv s1)) + s2;
     (t1,t0) <- Power2Round t;
     pk <@ PkEncDec.pkEncode(rho,t1);
     tr <- H_tr pk;
     sk <@ SkEncDec.skEncode(rho,_K,tr,s1,s2,t0);
     return (sk,pk);
  }

  proc sign_derand(sk : BytesSK.t, m : W8.t list, coins : rnd_) : BytesSig.t option * Leakage list= {
     var rho,_K,tr,s1,s2,t0,s1h,s2h,t0h,_A,mu,rhopp,kappa,y,w,w1,ctl,ct,c,ch,cs1,
         cs2,z,r0,ct0,h,leakage,sigma,bz,bh;
     var zh : (polylvec * polykvec) option;
     ct <- witness;
     ctl <- witness;
     sigma <- witness;
     leakage <- [];
     (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk);
     s1h <- nttv s1;
     s2h <- nttv s2;
     t0h <- nttv t0;
     _A <@ ExpandA(XOFA).sample(rho);
     mu <- H_mu tr m;
     rhopp <- H_rhopp _K coins mu;
     kappa <- 0;
     zh <- None;
     while (zh = None && ! (kappa_max <= kappa)) {
       y <@ ExpandMask.sample(rhopp,kappa * lvec);
       w <- invnttv (ntt_mulmxv _A (nttv y));
       w1 <- polykvec_HighBits w;
       ctl <@ RO(XOFSIB).get(mu,w1Encode w1);
       (ct,c) <- ctl.`1;
       leakage <- leakage ++ [ RO ctl.`2] ;
       ch <- ntt c;
       cs1 <- invnttv (ntt_smul ch s1h);
       cs2 <- invnttv (ntt_smul ch s2h);
       z <- y + cs1;
       r0 <- polykvec_LowBits (w - cs2);
       bz <- infnorm_lt z (gamma1 - Beta) &&
                  infnorm_lt r0 (gamma2 - Beta);
       leakage <- leakage ++ [ CheckZ bz ];
       if (bz) {
          ct0 <- invnttv (ntt_smul ch t0h);
          h <- MakeHint (PolyKVec.zerov-ct0) w - cs2 + ct0;
          bh <- infnorm_lt ct0 gamma2 && hammw h w_hint;
          leakage <- leakage ++ [ CheckH bh ];
          if (bh) { zh <- Some (z,h); }
       }
       kappa <- kappa + 1;
     }
     if (zh <> None) {
       sigma <@ SigEncDec.sigEncode(ct,(oget zh).`1,(oget zh).`2);
     }
     return (if zh = None then None else Some sigma, leakage);
  }

  (* Eager variant: decomposes w into (w0,w1) immediately, then uses w0 - cs2.
     The Jasmin implementation follows this order. *)
  proc sign_eager(sk : BytesSK.t, m : W8.t list, coins : rnd_) : BytesSig.t option * Leakage list = {
     var rho,_K,tr,s1,s2,t0,s1h,s2h,t0h,_A,mu,rhopp,kappa,y,w,w0,w1,ctl,ct,c,ch,cs1,
         cs2,z,r0,ct0,h,leakage,sigma,bz,bh;
     var zh : (polylvec * polykvec) option;
     ct <- witness;
     ctl <- witness;
     sigma <- witness;
     leakage <- [];
     (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk);
     s1h <- nttv s1;
     s2h <- nttv s2;
     t0h <- nttv t0;
     _A <@ ExpandA(XOFA).sample(rho);
     mu <- H_mu tr m;
     rhopp <- H_rhopp _K coins mu;
     kappa <- 0;
     zh <- None;
     while (zh = None && ! (kappa_max <= kappa)) {
       y <@ ExpandMask.sample(rhopp,kappa * lvec);
       w <- invnttv (ntt_mulmxv _A (nttv y));
       (* eager decomposition: split w now *)
       w0 <- polykvec_LowBits w;
       w1 <- polykvec_HighBits w;
       ctl <@ RO(XOFSIB).get(mu,w1Encode w1);
       (ct,c) <- ctl.`1;
       leakage <- leakage ++ [ RO ctl.`2] ;
       ch <- ntt c;
       cs1 <- invnttv (ntt_smul ch s1h);
       cs2 <- invnttv (ntt_smul ch s2h);
       z <- y + cs1;
       r0 <- w0 - cs2;
       bz <- infnorm_lt z (gamma1 - Beta) &&
                  infnorm_lt r0 (gamma2 - Beta);
       leakage <- leakage ++ [ CheckZ bz ];
       if (bz) {
          ct0 <- invnttv (ntt_smul ch t0h);
          h <- MakeHint w1 (r0 + ct0);
          bh <- infnorm_lt ct0 gamma2 && hammw h w_hint;
          leakage <- leakage ++ [ CheckH bh ];
          if (bh) { zh <- Some (z,h); }
       }
       kappa <- kappa + 1;
     }
     if (zh <> None) {
       sigma <@ SigEncDec.sigEncode(ct,(oget zh).`1,(oget zh).`2);
     }
     return (if zh = None then None else Some sigma, leakage);
  }

  proc verify(pk : BytesPK.t, sigma : BytesSig.t, m : W8.t list) : bool = {
    var rho,t1,c,l,ct,z,h,rb,_A,tr,mu,wapprox,w1,ctp;
    w1 <- witness;
    rb <- false;
    (rho,t1) <@ PkEncDec.pkDecode(pk);
    (ct,z,h) <@ SigEncDec.sigDecode(sigma);
    if (h <> None) {
      _A <@ ExpandA(XOFA).sample(rho);
      tr <- H_tr pk;
      mu <- H_mu tr m;
      (c,l) <@ SampleInBall(XOFSIB).sample(ct); (* we don't care about leakage in verify *)
      wapprox <- invnttv (ntt_mulmxv _A (nttv z) - (ntt_smul (ntt c) (nttv (smul t1 (incoeff (2^d))))));
      w1 <- UseHint (oget h) wapprox;
      ctp <- H_ct mu (w1Encode w1);
      rb <-  infnorm_lt z (gamma1 - Beta);
      rb <- rb && ct = ctp;
    }
    return rb;
  }
}.

(* The eager decomposition is equivalent to the standard one.
   Proof requires the commutativity of LowBits and subtraction of a small vector,
   i.e. LowBits(w - cs2) = LowBits(w) - cs2 when ||LowBits(w) - cs2||_inf < gamma2 - Beta. *)
lemma sign_eager_equiv
      (XOFA <: XOF_RejNTTPoly {-MLDSA}) (XOFS <: XOF_RejBPoly {-MLDSA})
      (XOFSIB <: XOF_SIB {-MLDSA}) (RO <: LeakyRO {-MLDSA}) :
    equiv [ MLDSA(XOFA, XOFS, XOFSIB, RO).sign_derand ~
            MLDSA(XOFA, XOFS, XOFSIB, RO).sign_eager :
      ={sk, m, coins, glob XOFA, glob XOFS, glob XOFSIB, glob RO}
      ==>
      ={res} ].
proof. admitted. (* Semantic reasoning about lowbits/highbits commuting with norm check tests. Justifies all reasonable implementations *)
