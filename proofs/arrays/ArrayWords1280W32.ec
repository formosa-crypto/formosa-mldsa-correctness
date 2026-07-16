from Jasmin require import JWord JWord_array.

require import Array1280 WArray5120.

clone export ArrayWords as ArrayWords1280W32  with op sizeW <- 4,
                                                   op sizeA <- 1280,
                                                   theory Word <= W32,
                                                   theory ArrayN <= Array1280,
                                                   theory WArrayN <= WArray5120.
