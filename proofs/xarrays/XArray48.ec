(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array48.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 48,
  theory A    <- Array48.Array48.

(* -------------------------------------------------------------------- *)
clone BSA as BSA48 with
      op size <- 48,
  theory A    <- Array48.Array48

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_48u8 with
      op asize <- 48,
      op bsize <- 8,
  theory A     <- Array48.Array48,
  theory BSA   <- BSA48,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_48u8_128 with
      op asize   <- 48,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array48.Array48,
  theory BSA     <- BSA48,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_48u8

  proof le_size by done.

require import WArray48 BitEncoding.
require import ArrayAccessCastW128_48W8 ArrayWords48W8.
require import XArrayAccessCastByte.
import Array48 BitChunking.

(* generic byte bridge instantiated for u8/128 (W128 read from a W8 Array48) *)
clone import XArrayAccessCastByte as X48u8_128 with
      op sizeWS <- 16,
      op sizeB  <- 48,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array48,
  theory AW     <- ArrayWords48W8,
  theory AC     <- ArrayAccessCastW128_48W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast128_48W8_slicegetE o (p : W8.t Array48.t) :
  0 <= o*8 <= 48*8-128 =>
   ArrayAccessCastW128_48W8.get_cast_direct p o = BSWAS_48u8_128.sliceget p (o*8).
proof. by move => H; rewrite X48u8_128.get_castE 1:/#. qed.

lemma get_cast128_48W8E (t : W8.t Array48.t) (o j : int) :
  0 <= o => o + 16 <= 48 => 0 <= j < 16 =>
   (ArrayAccessCastW128_48W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X48u8_128.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW128_48W8.WSu8.bits'SiE 1:/# /#.
qed.
