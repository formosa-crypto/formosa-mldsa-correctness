require import AllCore BitEncoding List RealExp IntDiv.
from Jasmin require import JWord JByte_array.


require import Parameters GFq Rq VecMat Conversion.
import PolyLVec PolyKVec PolyMat.
import CDR Round Zq BigZMod MLDSAParams.

abbrev q_bits = 23.
lemma q_bitlenl : 2^(q_bits-1) < q-1 <= 2^(q_bits) by auto.

abbrev noise_bits = if Eta = 4 then 4 else 3.
lemma noise_bitlen :  2^(noise_bits-1) < 2*Eta+1 (* signed range + 1 *) <= 2^(noise_bits)
  by  have/= H := param_sets; elim H => /> ??????-> /=.

abbrev gamma1_bits = 20.
lemma gamma1_bitlen :  2^(gamma1_bits-1) < 2*gamma1 (* signed range *) <= 2^(gamma1_bits)
  by  have/= H := param_sets; elim H => /> ??->???? /=.

abbrev w1_bits = 4.
lemma w1_bitlen : 2^(w1_bits-1) < (q-1) %/ (2*gamma2) - 1 <= 2^(w1_bits)
  by  have/= H := param_sets; elim H => /> ???->???? /=.


abbrev s1_bytes = (n * noise_bits * lvec) %/ 8.

abbrev t_bytes = (n * (q_bits-d) * kvec) %/ 8.

abbrev s2_bytes = (n * noise_bits * kvec) %/ 8.

abbrev t0_bytes = (n * d * kvec) %/ 8.

abbrev hint_bytes = w_hint + kvec.

abbrev z_bytes = (n * gamma1_bits * lvec) %/ 8.

abbrev sk_bytes = 32 + 32 + 64 + s1_bytes + s2_bytes + t0_bytes.
abbrev pk_bytes = 32 + t_bytes.
abbrev sig_bytes = lambda %/ 4 + z_bytes + hint_bytes.

abbrev w1_bytes = (n * w1_bits * kvec) %/ 8.


(*
ML-DSA-44 2560 1312 2420
ML-DSA-65 4032 1952 3309
ML-DSA-87 4896 2592 4627
*)

lemma key_sizes : (sk_bytes, pk_bytes, sig_bytes) \in [ (* (2560,1312,2420); *)
                                                           (4032,1952,3309);
                                                           (4896,2592,4627)]
  by  have /= H:= param_sets;elim H =>  [#] ?->??-> ->->-> /=. 


clone import ByteArray as Bytes32 with op size <= 32.
clone import ByteArray as Bytes64 with op size <= 64.
clone import ByteArray as BytesSK with op size <= sk_bytes.
clone import ByteArray as BytesPK with op size <= pk_bytes.
clone import ByteArray as BytesSig with op size <= sig_bytes.
clone import ByteArray as BytesCT with op size <= lambda %/ 4.
clone import ByteArray as BytesW1 with op size <= w1_bytes.

module PkEncDec = {
  proc pkEncode(rho : Bytes32.t, t1 : polykvec) : BytesPK.t = {
    var i, ti, pkbytes, pk;
    pkbytes <- to_list rho;
    i <- 0;
    while (i < kvec) {
      ti <- SimpleBitPack t1.[i] 10;
      pkbytes <- pkbytes ++ ti; 
    }
    pk <- BytesPK.of_list pkbytes;
    return pk;
  }

  proc pkDecode(pk :  BytesPK.t) :  Bytes32.t * polykvec = {
    var i, rho, ti;
    var t : polykvec;
    t <- witness;
    rho <- Bytes32.of_list (take 32 (to_list pk));
    i <- 0;
    while (i < kvec) {
      ti <- SimpleBitUnpack (take ((n * (q_bits-d)) %/ 8) (drop 32 (to_list pk))) (2^(q_bits - d)-1);
      t <- t.[i <- ti];
    }
    return (rho,t);
  }

}.

module SkEncDec = {
  proc skEncode(rho k : Bytes32.t, tr : Bytes64.t, s1 : polylvec, s2 t0 : polykvec)
    : BytesSK.t = {
    var i, skbytes, ski,sk; 
    skbytes <- to_list rho ++ to_list tr;
    i <- 0;
    while (i < lvec) {
      ski <- BitPack s1.[i] Eta Eta;
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitPack s2.[i] Eta Eta;
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitPack t0.[i] (2^(d-1)) (2^(d-1));
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    sk <- BytesSK.of_list skbytes;
    return sk;
  }

  proc skDecode(sk : BytesSK.t) : Bytes32.t * Bytes32.t * Bytes64.t * polylvec * polykvec * polykvec = {
    var rho, k, tr,ski, i;
    var s1 : polylvec;
    var  s2,t0 : polykvec;  
    s1 <- witness;
    s2 <- witness;
    t0 <- witness;
    rho <- Bytes32.of_list (take 32 (to_list sk)); 
    k <- Bytes32.of_list (take 32 (drop 32 (to_list sk)));
    tr <- Bytes64.of_list (take 64 (drop 64 (to_list sk)));
    i <- 0;
    while (i < lvec) {
      ski <- BitUnpack (take ((n * noise_bits) %/ 8) (drop 128 (to_list sk))) Eta Eta;
      s1 <- s1.[i <- ski];
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitUnpack (take ((n * noise_bits) %/ 8) (drop (128 + s1_bytes) (to_list sk))) Eta Eta;
      s2 <- s2.[i <- ski];
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitUnpack (take ((n * d) %/ 8) (drop (128 + s1_bytes + s2_bytes) (to_list sk))) (2^(d-1)-1) (2^(d-1));
      t0 <- t0.[i <- ski];
      i <- i + 1;
    }
    return (rho,k,tr,s1,s2,t0);  
  }
}.

module SigEncDec = {
  proc sigEncode(ct : BytesCT.t, z : polylvec, h : polykvec) : BytesSig.t = {
    var sigma, sigbytes, zi, hb, i;
    sigbytes <- to_list ct;
    i <- 0;
    while (i < lvec) {
       zi <- BitPack z.[i] (gamma1 - 1) (gamma1);
       sigbytes <- sigbytes ++ zi;
       i <- i + 1;
    }
    hb <@ HintPackUnpack.hintBitPack(h);
    sigbytes <- sigbytes ++ hb;
    sigma <- BytesSig.of_list sigbytes;
    return sigma;
  }

  proc sigDecode(sigma : BytesSig.t) : 
    BytesCT.t * polylvec * polykvec option = {
     var ct,zi,h,i;
     var z : polylvec;
     z <- witness;
     ct <- BytesCT.init(fun ii => sigma.[ii]);
     i <- 0;
     while (i < lvec) {
       zi <- BitUnpack (mkseq (fun ii => sigma.[lambda %/ 4 + (n * gamma1_bits) %/ 8 * i + ii]) n) (gamma1 - 1) gamma1;
       z <- z.[i <- zi];
       i <- i + 1;
    }
    h <@ HintPackUnpack.hintBitUnpack (take (kvec + w_hint) (drop (lambda %/4 + z_bytes) (to_list sigma)));

    return (ct,z,h);
  }
}.

op w1Encode(w1 : polykvec) : BytesW1.t = 
  BytesW1.of_list (flatten (map
    (fun wi => SimpleBitPack wi ((q-1)%/(2*gamma2) - 1)) 
       (mkseq (fun ii => w1.[ii]) kvec))).
