
%struct.tree = type { i32, double, double, %struct.tree*, %struct.tree*, %struct.tree*, %struct.tree* }

define i32 @tsp(%struct.tree* %t, i32 %sz, i32 %nproc) nounwind {
entry:
  %sz_addr = alloca i32                           ; <i32*> [#uses=4]
  %nproc_addr = alloca i32                        ; <i32*> [#uses=3]
  store i32 %sz, i32* %sz_addr
  store i32 %nproc, i32* %nproc_addr
  %t1 = load i32* %nproc_addr, align 4             ; <i32> [#uses=1]
  %t2 = sdiv i32 %t1, 2                             ; <i32> [#uses=1]
  br label %end
end:
  ret i32 0
}

define i32 @main() nounwind {
entry:
  ret i32 0
}
