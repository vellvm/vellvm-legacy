; not move %1/%0 because they are effectful
define i32 @main() nounwind {
entry:
  %p = alloca i32
  br i1 1, label %bb1, label %bb2  
bb1:
  %0 = load i32* %p
  br label %end
bb2:
  br label %end
end:
  %1 = phi i32 [ %0, %bb1 ], [ 1, %bb2 ]  
  %2 = load i32* %p
  %3 = add i32 %2, %1
  ret i32 %3
}

