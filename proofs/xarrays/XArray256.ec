(* -------------------------------------------------------------------- *)
require import AllCore JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array256.
require import XWords.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
export Array256.Array256.

(* -------------------------------------------------------------------- *)
clone export PAE with
      op size <- 256,
  theory A    <- Array256.Array256.

(* -------------------------------------------------------------------- *)
clone BSA as BSA256 with
      op size <- 256,
  theory A    <- Array256.Array256

  proof gt0_size by done.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u32 with
      op asize <- 256,
      op bsize <- 32,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W32 { rename "_XX" as "_32" },
  theory WE    <- WE32,
  theory BSW   <- BSW32.

(* -------------------------------------------------------------------- *)
clone BSWA as BSWA_256u13 with
      op asize <- 256,
      op bsize <- 13,
  theory A     <- Array256.Array256,
  theory BSA   <- BSA256,
  theory W     <- W13 { rename "_XX" as "_13" },
  theory WE    <- WE13,
  theory BSW   <- BSW13.

(* -------------------------------------------------------------------- *)
clone BSWAS as BSWAS_256u32_256 with
      op asize   <- 256,
      op bsize   <- 32,
      op ssize   <- 256,
  theory A       <- Array256.Array256,
  theory BSA     <- BSA256,
  theory WB      <- W32  { rename "_XX" as "_32" },
  theory WEB     <- WE32,
  theory BSWB    <- BSW32,
  theory WS      <- W256  { rename "_XX" as "_256" },
  theory WES     <- WE256,
  theory BSWS    <- BSW256,
  theory BSWA    <- BSWA_256u32

  proof le_size by done.
  