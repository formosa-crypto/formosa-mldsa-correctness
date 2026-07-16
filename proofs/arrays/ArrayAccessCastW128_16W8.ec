from Jasmin require import JWord JWord_array.

require import ArrayWords16W8.

clone export ArrayAccessCast as ArrayAccessCastW128_16W8  with op sizeWS <- 16,
                                                               op sizeWB <- 1,
                                                               op sizeB <- 16,
                                                               theory WordS <- W128,
                                                               theory WordB <- W8,
                                                               theory ArrayWordsB <= ArrayWords16W8.
