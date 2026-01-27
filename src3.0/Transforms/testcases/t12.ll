; not elim 0% because the store in bb kill the store in entry
define i32 @main() nounwind {
entry:
  %p = alloca i32
  store i32 0, i32* %p
  br label %bb
bb:
  %0 = load i32* %p
  store i32 1, i32* %p
  br i1 1, label %end, label %bb
end:
  ret i32 %0
}
