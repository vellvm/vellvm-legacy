; remove partial redundant %1 and %2 
define i32 @main() nounwind {
entry:
  %p = alloca i32
  %0 = load i32* %p
  br i1 1, label %bb1, label %bb2  
bb1:
  %1 = add i32 %0, %0
  br label %end
bb2:
  %2 = add i32 %0, %0
  br label %end
end:
  %3 = phi i32 [ %1, %bb1 ], [ %2, %bb2 ]  
  ret i32 %3
}

; expected
;
; define     i32 @main () nounwind{
; entry:
;   %p = alloca i32, i32 1
;   %0 = load i32* %p
;   %1 = add i32 %0, %0
;   br i1 -1, label %bb1, label %bb2
; bb1:
;   br label %end
; bb2:
;   br label %end
; end:
;   %2 = phi i32 [%1, %bb1],[%1, %bb2]
;   ret i32 %2
; }
