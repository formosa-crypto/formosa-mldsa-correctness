(* -------------------------------------------------------------------- *)
require import AllCore JWordExtra JArrayExtra CircuitBindings.
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
