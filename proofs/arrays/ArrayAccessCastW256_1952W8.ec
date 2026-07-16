from Jasmin require import JWord JWord_array.

require import ArrayWords1952W8.

clone export ArrayAccessCast as ArrayAccessCastW256_1952W8  with op sizeWS <- 32,
                                                                 op sizeWB <- 1,
                                                                 op sizeB <- 1952,
                                                                 theory WordS <- W256,
                                                                 theory WordB <- W8,
                                                                 theory ArrayWordsB <= ArrayWords1952W8.
