define void @foo(i32 %i) {
r:
  switch i32 %i, label %y5 [ i32 0, label %x1
                             i32 1, label %y1
                             i32 2, label %y2
                             i32 3, label %y3
                             i32 4, label %y4 ]

x1: br label %x2
x2: br label %x3
x3: br label %x4
x4: br label %x5

x5: 
  switch i32 %i, label %y5 [ i32 0, label %x1
                             i32 1, label %y1
                             i32 2, label %y2
                             i32 3, label %y3
                             i32 4, label %y4 ]
y1: br label %exit
y2: br label %exit
y3: br label %exit
y4: br label %exit
y5: br label %exit

exit:
  ret void
}

