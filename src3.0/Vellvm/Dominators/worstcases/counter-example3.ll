; both push and pull are incorrect
; this example generates a DFS that mirrors counter-example1's
; which makes both of them wrong.

define void @foo(i1 %b) {
n8: br i1 %b, label %n7, label %n2

n7: br i1 %b, label %n5, label %n6

n6: br label %n3

n5: br i1 %b, label %n2, label %n4

n4: br label %n3

n3: br label %n1

n2: br i1 %b, label %n1, label %n5

n1: ret void
}
