from Jasmin require import JWord JWord_array.

require import Array256 WArray256.

clone export ArrayWords as ArrayWords256W8  with op sizeW <- 1,
                                                 op sizeA <- 256,
                                                 theory Word <= W8,
                                                 theory ArrayN <= Array256,
                                                 theory WArrayN <= WArray256.
