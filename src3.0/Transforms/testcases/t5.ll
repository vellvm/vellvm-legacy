; not remove %1 because of %q may be aliased with %p 
; we can remove %1 with AA
define i32 @main() nounwind {
entry:
  %p = alloca i32
  %q = alloca i32
  %0 = load i32* %p
  store i32 0, i32* %q
  br label %bb
bb:
  %1 = load i32* %p
  %2 = add i32 %0, %1
  br label %end
end:
  ret i32 %2
}


; expected
;
;define i32 @main() nounwind {
;entry:
;  %p = alloca i32
;  %q = alloca i32
;  %0 = load i32* %p
;  store i32 0, i32* %q
;  br label %bb
;bb:
;  %1 = load i32* %p
;  %2 = add i32 %0, %1
;  br label %end
;end:
;  ret i32 %2
;}
