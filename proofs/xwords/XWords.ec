from Jasmin require import JWord.
require import JWordExtra CircuitBindings.

(* -------------------------------------------------------------------- *)

clone BitWordSH as W13 with
    op size <- 13
    rename "_XX" as "_13"
    proof gt0_size by done,
          size_le_256 by done. export W13. export ALU.

clone WE as WE13 with
  op     size <- 13,
  theory W    <- W13 { rename "_XX" as "_13" }.
print WE13.
  
clone BSW as BSW13 with
  op     size <- 13,
  theory W    <- W13  { rename "_XX" as "_13" },
  theory WE   <- WE13 { rename "_XX" as "_13" }.

clone BS_WB_WS_U as BS_W32_W13_U with
        op sizeS <- 13,
        op sizeB <- 32,
    theory WS    <- W13  { rename "_XX" as "_13"
                           "'S" as "13"
                           "'B" as "32"},
    theory WSE   <- WE13 { rename "_XX" as "_13"
                           "'S" as "13"
                           "'B" as "32"},
    theory WB    <- W32  { rename "_XX" as "_32"
                           "'S" as "13"
                           "'B" as "32"},
    theory WBE   <- WE32 { rename "_XX" as "_32"
                           "'S" as "13"
                           "'B" as "32"},
    theory BSWS  <- BSW13  { rename "_XX" as "_13"
                                    "'S" as "13"
                                    "'B" as "32" },
    theory BSWB  <- BSW32  { rename "_XX" as "_32"
                                    "'S" as "13"
                                    "'B" as "32"}
          rename "'S" as "13"
          rename "'B" as "32"
    proof *.

    realize le_size by auto. 

