; pull is correct
; 7 <<8
; 3 <<8
; 5 <<8
; 1 <<4 7 8
; 6 <<8
; 2 <<8
; 4 <<7 8
; 8 <<

; push is incorret
; 7 <<8
; 3 <<7 8
; 5 <<8
; 1 <<4 7 8
; 6 <<8
; 2 <<7 8
; 4 <<7 8
; 8 <<

define void @foo(i1 %b) {
n8: br i1 %b, label %n7, label %n5

n7: br i1 %b, label %n4, label %n6
n4: br i1 %b, label %n1, label %n3

n6: br i1 %b, label %n5, label %n2
n3: br label %n2

n5: br label %n6
n2: br label %n3

n1:
 ret void
}
