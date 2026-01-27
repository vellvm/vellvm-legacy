; replace all uses of %3 by %2, then delete %3
define i32 @main() nounwind {
entry:
  %p = alloca i32
  %q = alloca i32
  %0 = load i32* %p
  %1 = load i32* %q
  %2 = add i32 %0, %1
  br label %bb
bb:
  %3 = add i32 %0, %1
  %4 = add i32 %2, %3
  br label %end
end:
  ret i32 %4
}

; expected:
;
; define     i32 @main () nounwind{
; entry:
;   %p = alloca i32, i32 1
;   %q = alloca i32, i32 1
;   %0 = load i32* %p
;   %1 = load i32* %q
;   %2 = add i32 %0, %1
;   br label %bb
; bb:
;   %3 = add i32 %2, %2
;   br label %end
; end:
;   ret i32 %3
; }

