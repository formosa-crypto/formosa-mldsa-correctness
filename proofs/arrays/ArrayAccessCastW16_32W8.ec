from Jasmin require import JWord JWord_array.

require import ArrayWords32W8.

clone export ArrayAccessCast as ArrayAccessCastW16_32W8  with op sizeWS <- 2,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 32,
                                                              theory WordS <- W16,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords32W8.
