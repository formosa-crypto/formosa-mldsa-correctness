(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array640.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array640.Array640.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 640,
  theory A    <- Array640.Array640.

(* -------------------------------------------------------------------- *)
clone BSA as BSA640 with
      op size <- 640,
  theory A    <- Array640.Array640

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_640u8 with
      op asize <- 640,
      op bsize <- 8,
  theory A     <- Array640.Array640,
  theory BSA   <- BSA640,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_640u8_128 with
      op asize   <- 640,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array640.Array640,
  theory BSA     <- BSA640,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_640u8

  proof le_size by done.

require import WArray640 BitEncoding.
require import ArrayAccessCastW128_640W8 ArrayWords640W8.
require import XArrayAccessCastByte.
import Array640 BitChunking.

(* generic byte bridge instantiated for u8/128 (W128 <-> a W8 Array640) *)
clone import XArrayAccessCastByte as X640u8_128 with
      op sizeWS <- 16,
      op sizeB  <- 640,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array640,
  theory AW     <- ArrayWords640W8,
  theory AC     <- ArrayAccessCastW128_640W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast128_640W8_slicegetE o (p : W8.t Array640.t) :
  0 <= o*8 <= 640*8-128 =>
   ArrayAccessCastW128_640W8.get_cast_direct p o = BSWAS_640u8_128.sliceget p (o*8).
proof. by move => H; rewrite X640u8_128.get_castE 1:/#. qed.

lemma set_cast128_640W8_slicesetE (t : W8.t Array640.t) o (s : W128.t) :
  0 <= o*8 <= 8*640-128 =>
   ArrayAccessCastW128_640W8.set_cast_direct t o s = BSWAS_640u8_128.sliceset t (o*8) s.
proof. by move => H; rewrite X640u8_128.set_castE 1:/#. qed.
