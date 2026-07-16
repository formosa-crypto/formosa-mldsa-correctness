from Jasmin require import JWord JWord_array.

require import ArrayWords48W8.

clone export ArrayAccessCast as ArrayAccessCastW64_48W8  with op sizeWS <- 8,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 48,
                                                              theory WordS <- W64,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords48W8.
