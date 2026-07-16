from Jasmin require import JWord JWord_array.

require import Array128 WArray128.

clone export ArrayWords as ArrayWords128W8  with op sizeW <- 1,
                                                 op sizeA <- 128,
                                                 theory Word <= W8,
                                                 theory ArrayN <= Array128,
                                                 theory WArrayN <= WArray128.
