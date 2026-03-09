(* -------------------------------------------------------------------- *)
require import AllCore JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array256.

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
