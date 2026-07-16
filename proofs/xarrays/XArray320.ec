(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array320.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array320.Array320.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 320,
  theory A    <- Array320.Array320.

(* -------------------------------------------------------------------- *)
clone BSA as BSA320 with
      op size <- 320,
  theory A    <- Array320.Array320

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_320u8 with
      op asize <- 320,
      op bsize <- 8,
  theory A     <- Array320.Array320,
  theory BSA   <- BSA320,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_320u8_128 with
      op asize   <- 320,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array320.Array320,
  theory BSA     <- BSA320,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_320u8

  proof le_size by done.

require import WArray320 BitEncoding.
require import ArrayAccessCastW128_320W8 ArrayWords320W8.
require import XArrayAccessCastByte.
import Array320 BitChunking.

(* generic byte bridge instantiated for u8/128 (W128 <-> a W8 Array320) *)
clone import XArrayAccessCastByte as X320u8_128 with
      op sizeWS <- 16,
      op sizeB  <- 320,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array320,
  theory AW     <- ArrayWords320W8,
  theory AC     <- ArrayAccessCastW128_320W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast128_320W8_slicegetE o (p : W8.t Array320.t) :
  0 <= o*8 <= 320*8-128 =>
   ArrayAccessCastW128_320W8.get_cast_direct p o = BSWAS_320u8_128.sliceget p (o*8).
proof. by move => H; rewrite X320u8_128.get_castE 1:/#. qed.

lemma set_cast128_320W8_slicesetE (t : W8.t Array320.t) o (s : W128.t) :
  0 <= o*8 <= 8*320-128 =>
   ArrayAccessCastW128_320W8.set_cast_direct t o s = BSWAS_320u8_128.sliceset t (o*8) s.
proof. by move => H; rewrite X320u8_128.set_castE 1:/#. qed.
