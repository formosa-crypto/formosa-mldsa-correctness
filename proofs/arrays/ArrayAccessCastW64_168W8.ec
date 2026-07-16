from Jasmin require import JWord JWord_array.

require import ArrayWords168W8.

clone export ArrayAccessCast as ArrayAccessCastW64_168W8  with op sizeWS <- 8,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 168,
                                                               theory WordS <- W64,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords168W8.
