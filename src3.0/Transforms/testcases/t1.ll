; const prop %0, then remove %0
define i32 @main() nounwind {
entry:
  %0 = add i32 4, 5
  br label %bb
bb:
  br label %end
end:
  ret i32 %0
}

; expected:

; define     i32 @main () nounwind{
; entry:
;   br label %bb
; bb:
;   br label %end
; end:
;   ret i32 add (4 to 5)
; }
