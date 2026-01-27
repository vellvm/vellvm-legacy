define void @foo(i32 %i, i1 %b) {
r:
  br i1 %b, label %w, label %y1

w: 
  switch i32 %i, label %x5 [ i32 1, label %x1
                             i32 2, label %x2
                             i32 3, label %x3
                             i32 4, label %x4 ]

x5: br label %x4
x4: br label %x3
x3: br label %x2
x2: br label %x1
x1: br label %exit

y1: br label %y2

y2: br label %x5

exit:
  ret void
}

