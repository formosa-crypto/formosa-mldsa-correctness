from Jasmin require import JWord JWord_array.

require import ArrayWords128W8.

clone export ArrayAccessCast as ArrayAccessCastW64_128W8  with op sizeWS <- 8,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 128,
                                                               theory WordS <- W64,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords128W8.
