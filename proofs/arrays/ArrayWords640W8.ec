from Jasmin require import JWord JWord_array.

require import Array640 WArray640.

clone export ArrayWords as ArrayWords640W8  with op sizeW <- 1,
                                                 op sizeA <- 640,
                                                 theory Word <= W8,
                                                 theory ArrayN <= Array640,
                                                 theory WArrayN <= WArray640.
