; cannot remove %0 because foo may affect it

define void @foo() nounwind {
entry:
  ret void
}

; not elim %0, %p and @foo may be aliased
define i32 @main() nounwind {
entry:
  %p = alloca i32
  store i32 0, i32* %p
  br i1 1, label %bb1, label %bb2
bb1:
  call void @foo()
  br label %end
bb2:
  br label %end
end:
  %0 = load i32* %p
  ret i32 %0
}

