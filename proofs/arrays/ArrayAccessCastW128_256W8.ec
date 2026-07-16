from Jasmin require import JWord JWord_array.

require import ArrayWords256W8.

clone export ArrayAccessCast as ArrayAccessCastW128_256W8  with op sizeWS <- 16,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 256,
                                                                theory WordS <- W128,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords256W8.
