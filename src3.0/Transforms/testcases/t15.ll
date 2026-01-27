; remove %1 
define i32 @main() nounwind {
entry:
  %p = alloca i32
  %0 = load i32* %p
  %q = alloca i32
  br label %bb
bb:
  %1 = load i32* %p
  %2 = add i32 %0, %1
  br label %end
end:
  ret i32 %2
}

; expected
;define     i32 @main () nounwind{
;entry:
;  %p = alloca i32, i32 1
;  %0 = load i32* %p
;  %q = alloca i32, i32 1
;  br label %bb
;bb:
;  %1 = add i32 %0, %0
;  br label %end
;end:
;  ret i32 %1
;}

