@g = global i32 16

define i32 @main() nounwind {
entry:
  %0 = load i32* @g
  br i1 1, label %bb1, label %bb2
bb1:
  store i32 0, i32* @g
  br label %bb2
bb2:
  br i1 1, label %bb3, label %end
bb3:
  %1 = load i32* @g
  br label %end
end:
  %2 = phi i32 [%1, %bb3], [undef, %bb2]
  ret i32 %2
}


