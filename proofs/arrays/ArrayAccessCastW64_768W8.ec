from Jasmin require import JWord JWord_array.

require import ArrayWords768W8.

clone export ArrayAccessCast as ArrayAccessCastW64_768W8  with op sizeWS <- 8,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 768,
                                                               theory WordS <- W64,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords768W8.
