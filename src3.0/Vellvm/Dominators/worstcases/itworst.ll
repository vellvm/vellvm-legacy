define void @foo(i32 %i, i1 %b) {
r:
  switch i32 %i, label %w1 [ i32 1, label %x1
                             i32 2, label %z3]

x1: br label %x2
x2: br label %x3

x3: br label %y1

y1: 
  switch i32 %i, label %w1 [ i32 1, label %w2
                             i32 2, label %w3
                             i32 3, label %y2]
y2: 
  switch i32 %i, label %w1 [ i32 1, label %w2
                             i32 2, label %w3
                             i32 3, label %y3]
y3: 
  switch i32 %i, label %w1 [ i32 1, label %w2
                             i32 2, label %w3
                             i32 3, label %z1]

z1: br label %z2
z2: br i1 %b, label %z1, label %z3
z3: br i1 %b, label %z2, label %exit

w1: br label %w2
w2: br label %w3
w3: br label %exit

exit:
  ret void
}

