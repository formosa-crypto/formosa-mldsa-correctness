from Jasmin require import JWord JWord_array.

require import ArrayWords128W8.

clone export ArrayAccessCast as ArrayAccessCastW256_128W8  with op sizeWS <- 32,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 128,
                                                                theory WordS <- W256,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords128W8.
