; not elim %0, %p and %q may be aliased
; can remove %0 with AA
define i32 @main() nounwind {
entry:
  %p = alloca i32
  %q = alloca i32
  store i32 0, i32* %p
  store i32 0, i32* %q
  br label %bb
bb:
  %0 = load i32* %p
  br label %end
end:
  ret i32 %0
}

