define i32 @main() nounwind {
entry:
  %p = alloca i32
  %q = alloca i32
  %0 = load i32* %p
  %1 = load i32* %q
  %c = trunc i32 %0 to i1
  %a1 = add i32 %0, %1
  %a2 = add i32 %0, %1
  %a3 = add i32 %1, %0
  %a4 = add i32 %1, %0
  br label %loop
loop:
  br i1 %c, label %bb1, label %bb2  
bb1:
  %2 = add i32 %a1, %a3
  %3 = add i32 %a2, %a4
  br label %end
bb2:
  %4 = add i32 %a1, %a3
  %5 = add i32 %a2, %a4
  br i1 1, label %end, label %loop
end:
  %6 = phi i32 [ %2, %bb1 ], [ %4, %bb2 ]  
  %7 = phi i32 [ %3, %bb1 ], [ %5, %bb2 ]  
  %8 = add i32 %6, %7
  ret i32 %8
}

; expected:
;
; define     i32 @main () nounwind{
; entry:
;   %p = alloca i32, i32 1
;   %q = alloca i32, i32 1
;   %0 = load i32* %p
;   %1 = load i32* %q
;   %c = trunc i32 %0 to i1
;   %a1 = add i32 %0, %1
;   %a3 = add i32 %1, %0
;   br label %loop
; loop:
;   %2 = add i32 %a1, %a3
;   br i1 %c, label %bb1, label %bb2
; bb1:
;   br label %end
; bb2:
;   br i1 %c, label %end, label %loop
; end:
;   %3 = phi i32 [%2, %bb1],[%2, %bb2]
;   %4 = phi i32 [%2, %bb1],[%2, %bb2]
;   %5 = add i32 %3, %4
;   ret i32 %5
; }
