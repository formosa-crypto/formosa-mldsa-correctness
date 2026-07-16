(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array128.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array128.Array128.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 128,
  theory A    <- Array128.Array128.

(* -------------------------------------------------------------------- *)
clone BSA as BSA128 with
      op size <- 128,
  theory A    <- Array128.Array128

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_128u8 with
      op asize <- 128,
      op bsize <- 8,
  theory A     <- Array128.Array128,
  theory BSA   <- BSA128,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_128u8_256 with
      op asize   <- 128,
      op bsize   <- 8,
      op ssize   <- 256,
  theory A       <- Array128.Array128,
  theory BSA     <- BSA128,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W256  { rename "_XX" as "_256" },
  theory WES     <- WE256,
  theory BSWS    <- BSW256,
  theory BSWA    <- BSWA_128u8

  proof le_size by done.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_128u8_128 with
      op asize   <- 128,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array128.Array128,
  theory BSA     <- BSA128,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_128u8

  proof le_size by done.

require import WArray128 BitEncoding.
require import ArrayAccessCastW256_128W8 ArrayAccessCastW128_128W8 ArrayWords128W8.
require import XArrayAccessCastByte.
import Array128 BitChunking.

(* generic byte bridge instantiated for u8/256 (W256 into a W8 Array128) *)
clone import XArrayAccessCastByte as X128u8_256 with
      op sizeWS <- 32,
      op sizeB  <- 128,
  theory WS     <- W256 { rename "_XX" as "_256" },
  theory A      <- Array128,
  theory AW     <- ArrayWords128W8,
  theory AC     <- ArrayAccessCastW256_128W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

(* generic byte bridge instantiated for u8/128 (W128 read from a W8 Array128) *)
clone XArrayAccessCastByte as X128u8_128 with
      op sizeWS <- 16,
      op sizeB  <- 128,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array128,
  theory AW     <- ArrayWords128W8,
  theory AC     <- ArrayAccessCastW128_128W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma BSWAS_128u8_256_slicesetE (t : W8.t Array128.t) o (s : W256.t) :
  0 <= (o*8) <= 8 * 128 - 256 =>
   BSWAS_128u8_256.sliceset t (o*8) s =
      Array128.init (get8 (set256_direct (WArray128.init8 (fun (i_0 : int) => t.[i_0])) o s)).
proof.
move => Ho.
rewrite tP => k kb.
rewrite wordP => i ib;rewrite initiE 1:/# /=.
have //= := BSWAS_128u8_256.BVA_asliceset_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicesetP t (o*8) s _ (k*8+i) _;1,2:by smt().
rewrite (nth_flatten false 8).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
rewrite get_to_list get_w2bits (: (k * 8 + i) %/ 8 = k) 1:/# (: (k * 8 + i) %% 8 = i) 1:/# => -> .
rewrite (nth_flatten false 8).
+ rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
rewrite get_w2bits get_to_list /get8 /set256_direct initiE 1:/# /= /(\bits8) initiE 1:/# /=.
by smt(W8.initiE).
qed.

lemma BSWAS_128u8_128_slicegetE o (p : W8.t Array128.t):
    0 <= o*8 <= 128*8-128 =>
     get128_direct (WArray128.init8 (fun (i_0 : int) => p.[i_0])) o = BSWAS_128u8_128.sliceget p (o * 8).
  proof.
  move => Ho.
  rewrite /get128_direct /pack16_t;apply W128.wordP => k kb.
  have //= := BSWAS_128u8_128.BVA_asliceget_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicegetP p (o * 8) _; 1: by smt().
  move => -> //; rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
  rewrite nth_take 1,2:/# nth_drop 1,2:/#  (nth_flatten false 8).
  + rewrite allP /= => x; rewrite mapP => He; elim He;smt(W8.size_w2bits).
  rewrite (nth_map witness); 1: by rewrite size_to_list; smt().
  by rewrite get_to_list get_w2bits /#.
 qed.

(* -------------------------------------------------------------------- *)
(* element lemma as a thin wrapper over the generic byte bridge X128u8_256. *)
(* -------------------------------------------------------------------- *)
lemma set_cast256_128W8_slicesetE (t : W8.t Array128.t) o (s : W256.t) :
  0 <= o*8 <= 8*128-256 =>
   ArrayAccessCastW256_128W8.set_cast_direct t o s = BSWAS_128u8_256.sliceset t (o*8) s.
proof. by move => H; rewrite X128u8_256.set_castE 1:/#. qed.

(* \bits8 element/byte lemmas for W256 <-> W8 Array128 copies (hashing block). *)
lemma get_cast256_128W8E (t : W8.t Array128.t) (o j : int) :
  0 <= o => o + 32 <= 128 => 0 <= j < 32 =>
   (ArrayAccessCastW256_128W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X128u8_256.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW256_128W8.WSu8.bits'SiE 1:/# /#.
qed.

lemma set_cast256_128W8E (t : W8.t Array128.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 128 => 0 <= k < 128 =>
   (ArrayAccessCastW256_128W8.set_cast_direct t o s).[k]
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X128u8_256.set_cast_directE 1,2,3:/#.
case (o <= k < o + 32) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW256_128W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

lemma get_cast128_128W8_slicegetE o (p : W8.t Array128.t) :
  0 <= o*8 <= 8*128-128 =>
   ArrayAccessCastW128_128W8.get_cast_direct p o = BSWAS_128u8_128.sliceget p (o*8).
proof. by move => H; rewrite X128u8_128.get_castE 1:/#. qed.
