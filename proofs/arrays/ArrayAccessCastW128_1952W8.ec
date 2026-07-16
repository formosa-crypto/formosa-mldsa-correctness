from Jasmin require import JWord JWord_array.

require import ArrayWords1952W8.

clone export ArrayAccessCast as ArrayAccessCastW128_1952W8  with op sizeWS <- 16,
                                                                 op sizeWB <- 1,
                                                                 op sizeB <- 1952,
                                                                 theory WordS <- W128,
                                                                 theory WordB <- W8,
                                                                 theory ArrayWordsB <= ArrayWords1952W8.
