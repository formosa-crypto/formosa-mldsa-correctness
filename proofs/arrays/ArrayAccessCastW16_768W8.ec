from Jasmin require import JWord JWord_array.

require import ArrayWords768W8.

clone export ArrayAccessCast as ArrayAccessCastW16_768W8  with op sizeWS <- 2,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 768,
                                                               theory WordS <- W16,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords768W8.
