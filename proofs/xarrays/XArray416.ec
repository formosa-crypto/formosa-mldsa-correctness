(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array416.
require import XWord13 JWordExtra.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 416,
  theory A    <- Array416.Array416.

(* -------------------------------------------------------------------- *)
clone BSA as BSA416 with
      op size <- 416,
  theory A    <- Array416.Array416

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_416u8 with
      op asize <- 416,
      op bsize <- 8,
  theory A     <- Array416.Array416,
  theory BSA   <- BSA416,
  theory W     <- W8 { rename "_XX" as "_8" },
  theory WE    <- WE8,
  theory BSW   <- BSW8
  proof *.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_416u8_13 with
      op asize   <- 416,
      op bsize   <- 8,
      op ssize   <- 13,
  theory A       <- Array416.Array416,
  theory BSA     <- BSA416,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W13  { rename "_XX" as "_13" },
  theory WES     <- WE13,
  theory BSWS    <- BSW13,
  theory BSWA    <- BSWA_416u8

  proof le_size by done.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_416u8_128 with
      op asize   <- 416,
      op bsize   <- 8,
      op ssize   <- 128,
  theory A       <- Array416.Array416,
  theory BSA     <- BSA416,
  theory WB      <- W8  { rename "_XX" as "_8" },
  theory WEB     <- WE8,
  theory BSWB    <- BSW8,
  theory WS      <- W128  { rename "_XX" as "_128" },
  theory WES     <- WE128,
  theory BSWS    <- BSW128,
  theory BSWA    <- BSWA_416u8

  proof le_size by done.

require import WArray416 BitEncoding.
require import ArrayAccessCastW128_416W8 ArrayWords416W8.
require import XArrayAccessCastByte.
import Array416 BitChunking.

(* generic byte bridge instantiated for u8/128 (W128 <-> a W8 Array416) *)
clone import XArrayAccessCastByte as X416u8_128 with
      op sizeWS <- 16,
      op sizeB  <- 416,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array416,
  theory AW     <- ArrayWords416W8,
  theory AC     <- ArrayAccessCastW128_416W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast128_416W8_slicegetE o (p : W8.t Array416.t) :
  0 <= o*8 <= 416*8-128 =>
   ArrayAccessCastW128_416W8.get_cast_direct p o = BSWAS_416u8_128.sliceget p (o*8).
proof. by move => H; rewrite X416u8_128.get_castE 1:/#. qed.

lemma set_cast128_416W8_slicesetE (t : W8.t Array416.t) o (s : W128.t) :
  0 <= o*8 <= 8*416-128 =>
   ArrayAccessCastW128_416W8.set_cast_direct t o s = BSWAS_416u8_128.sliceset t (o*8) s.
proof. by move => H; rewrite X416u8_128.set_castE 1:/#. qed.
