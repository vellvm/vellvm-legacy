define i32 @onintr() nounwind {
entry:
  %retval = alloca i32                            ; <i32*> [#uses=1]
  unreachable

return:                                           ; No predecessors!
  %retval1 = load i32* %retval                    ; <i32> [#uses=1]
  ret i32 %retval1
}


define i32 @main() nounwind {
entry:
  ret i32 0
}

