from Jasmin require import JWord JWord_array.

require import ArrayWords640W8.

clone export ArrayAccessCast as ArrayAccessCastW128_640W8  with op sizeWS <- 16,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 640,
                                                                theory WordS <- W128,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords640W8.
