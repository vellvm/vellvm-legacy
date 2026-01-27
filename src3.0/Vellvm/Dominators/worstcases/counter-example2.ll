; both push and pull are incorrect
; 3 <<4 5 6
; 5 <<6
; 1 <<6
; 6 <<
; 2 <<6
; 4 <<6
; Here, it looks like by taking one more pass to get the minimal ancesters of 
; 4 can fix the error. counter-example3.ll shows there exists a case that we 
; cannot fix in such a way.

define void @foo(i1 %b) {
n6: br i1 %b, label %n5, label %n2

n5: br label %n4

n4: br i1 %b, label %n2, label %n3

n3: br label %n1

n2: br i1 %b, label %n4, label %n1

n1:
 ret void
}
