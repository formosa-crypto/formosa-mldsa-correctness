from Jasmin require import JWord JWord_array.

require import ArrayWords64W8.

clone export ArrayAccessCast as ArrayAccessCastW256_64W8  with op sizeWS <- 32,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 64,
                                                               theory WordS <- W256,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords64W8.
