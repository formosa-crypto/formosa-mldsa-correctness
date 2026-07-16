from Jasmin require import JWord JWord_array.

require import ArrayWords320W8.

clone export ArrayAccessCast as ArrayAccessCastW128_320W8  with op sizeWS <- 16,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 320,
                                                                theory WordS <- W128,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords320W8.
