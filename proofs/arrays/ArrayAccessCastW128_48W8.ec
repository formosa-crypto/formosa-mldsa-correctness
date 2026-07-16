from Jasmin require import JWord JWord_array.

require import ArrayWords48W8.

clone export ArrayAccessCast as ArrayAccessCastW128_48W8  with op sizeWS <- 16,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 48,
                                                               theory WordS <- W128,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords48W8.
