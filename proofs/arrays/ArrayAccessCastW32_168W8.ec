from Jasmin require import JWord JWord_array.

require import ArrayWords168W8.

clone export ArrayAccessCast as ArrayAccessCastW32_168W8  with op sizeWS <- 4,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 168,
                                                               theory WordS <- W32,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords168W8.
