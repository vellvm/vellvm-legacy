define void @foo() nounwind {
entry:
  ret void
}

; not elim %0, %p and @foo may be aliased
define i32 @main() nounwind {
entry:
  %p = alloca i32
  store i32 0, i32* %p
  call void @foo()
  br label %bb
bb:
  %0 = load i32* %p
  br label %end
end:
  ret i32 %0
}

