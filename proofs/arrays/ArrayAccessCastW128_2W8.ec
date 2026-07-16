from Jasmin require import JWord JWord_array.

require import ArrayWords2W8.

clone export ArrayAccessCast as ArrayAccessCastW128_2W8  with op sizeWS <- 16,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 2,
                                                              theory WordS <- W128,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords2W8.
