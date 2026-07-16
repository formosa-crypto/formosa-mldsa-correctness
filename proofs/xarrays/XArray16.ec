(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array16.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array16.Array16.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 16,
  theory A    <- Array16.Array16.

(* -------------------------------------------------------------------- *)
clone BSA as BSA16 with
      op size <- 16,
  theory A    <- Array16.Array16

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_16u8 with
      op asize <- 16,
      op bsize <- 8,
  theory A     <- Array16.Array16,
  theory BSA   <- BSA16,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_16u8_128 with
      op asize   <- 16,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array16.Array16,
  theory BSA     <- BSA16,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_16u8

  proof le_size by done.


require import WArray16 BitEncoding.
require import ArrayAccessCastW128_16W8 ArrayWords16W8.
require import XArrayAccessCastByte.
import Array16 BitChunking.

(* generic byte bridge instantiated for u8/128 (W128 <-> a W8 Array16;
   here the slice is the whole array, so only offset 0 is valid) *)
clone import XArrayAccessCastByte as X16u8_128 with
      op sizeWS <- 16,
      op sizeB  <- 16,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array16,
  theory AW     <- ArrayWords16W8,
  theory AC     <- ArrayAccessCastW128_16W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma set_cast128_16W8_slicesetE (t : W8.t Array16.t) o (s : W128.t) :
  0 <= o*8 <= 8*16-128 =>
   ArrayAccessCastW128_16W8.set_cast_direct t o s = BSWAS_16u8_128.sliceset t (o*8) s.
proof. by move => H; rewrite X16u8_128.set_castE 1:/#. qed.
