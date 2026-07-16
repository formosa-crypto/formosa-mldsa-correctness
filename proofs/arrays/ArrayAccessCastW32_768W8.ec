from Jasmin require import JWord JWord_array.

require import ArrayWords768W8.

clone export ArrayAccessCast as ArrayAccessCastW32_768W8  with op sizeWS <- 4,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 768,
                                                               theory WordS <- W32,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords768W8.
