; elim %0, it is redundant after the store
define i32 @main() nounwind {
entry:
  %p = alloca i32
  store i32 0, i32* %p
  br label %bb
bb:
  %0 = load i32* %p
  br label %end
end:
  ret i32 %0
}

; expected:
;
; define     i32 @main () nounwind{
; entry:
;   %p = alloca i32, i32 1
;   store i32 0, i32* %p
;   br label %bb
; bb:
;   br label %end
; end:
;   ret i32 0
; }
