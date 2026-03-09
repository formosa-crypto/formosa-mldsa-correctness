(* -------------------------------------------------------------------- *)
require import AllCore JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array416.
require import XWords JWordExtra.

from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
require Array416.

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
  
