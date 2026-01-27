define i32 @main() nounwind {
entry:
  %p = alloca i32
  %q = alloca i32
  %0 = load i32* %p
  %1 = load i32* %q
  %2 = add i32 %0, %1
  br i1 1, label %bb1, label %bb2  
bb1:
  %3 = add i32 %0, %1
  br label %merge1
bb2:
  %4 = add i32 %0, %1
  br label %merge1
merge1:
  %5 = phi i32 [ %3, %bb1 ], [ %4, %bb2 ]  
  br i1 1, label %bb3, label %bb4  
bb3:
  %6 = add i32 %0, %1
  br label %merge2
bb4:
  %7 = add i32 %0, %1
  br label %merge2
merge2:
  %8 = phi i32 [ %6, %bb3 ], [ %7, %bb4 ]  
  br i1 1, label %bb5, label %bb6  
bb5:
  %9 = add i32 %0, %1
  br label %end
bb6:
  %10 = add i32 %0, %1
  br label %end
end:
  %11 = phi i32 [ %9, %bb5 ], [ %10, %bb6 ]  
  ret i32 %11
}


; expected
;
; define     i32 @main () nounwind{
; entry:
;   %p = alloca i32, i32 1
;   %q = alloca i32, i32 1
;   %0 = load i32* %p
;   %1 = load i32* %q
;   %2 = add i32 %0, %1
;   br i1 -1, label %bb1, label %bb2
; bb1:
;   br label %merge1
; bb2:
;   br label %merge1
; merge1:
;   br i1 -1, label %bb3, label %bb4
; bb3:
;   br label %merge2
; bb4:
;   br label %merge2
; merge2:
;   br i1 -1, label %bb5, label %bb6
; bb5:
;   br label %end
; bb6:
;   br label %end
; end:
;   %3 = phi i32 [%2, %bb5],[%2, %bb6]
;   ret i32 %3
; }
