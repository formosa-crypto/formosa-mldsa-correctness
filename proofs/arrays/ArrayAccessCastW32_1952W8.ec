from Jasmin require import JWord JWord_array.

require import ArrayWords1952W8.

clone export ArrayAccessCast as ArrayAccessCastW32_1952W8  with op sizeWS <- 4,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 1952,
                                                                theory WordS <- W32,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords1952W8.
