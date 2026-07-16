from Jasmin require import JWord JWord_array.

require import ArrayWords32W8.

clone export ArrayAccessCast as ArrayAccessCastW128_32W8  with op sizeWS <- 16,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 32,
                                                               theory WordS <- W128,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords32W8.
