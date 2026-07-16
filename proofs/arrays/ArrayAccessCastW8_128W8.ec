from Jasmin require import JWord JWord_array.

require import ArrayWords128W8.

clone export ArrayAccessCast as ArrayAccessCastW8_128W8  with op sizeWS <- 1,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 128,
                                                              theory WordS <- W8,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords128W8.
