from Jasmin require import JWord JWord_array.

require import ArrayWords768W8.

clone export ArrayAccessCast as ArrayAccessCastW8_768W8  with op sizeWS <- 1,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 768,
                                                              theory WordS <- W8,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords768W8.
