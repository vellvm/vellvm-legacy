define void @foo() nounwind {
entry:
  ret void
}

; not elim %0, %p and @foo may be aliased
define i32 @main() nounwind {
entry:
  %p = alloca i32
  %0 = load i32* %p
  call void @foo()
  br label %bb
bb:
  %1 = load i32* %p
  br label %end
end:
  ret i32 %1
}
