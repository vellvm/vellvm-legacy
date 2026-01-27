define void @foo(i32 %i, i1 %b) {
r: br i1 %b, label %y1, label %x12

y1: br i1 %b, label %y2, label %x11
y2: br i1 %b, label %y3, label %x21
y3: br i1 %b, label %y4, label %x31
y4: br i1 %b, label %y5, label %x41
y5: br i1 %b, label %exit, label %x51

x11: br i1 %b, label %x12, label %x22
x21: br i1 %b, label %x22, label %x32
x31: br i1 %b, label %x32, label %x42
x41: br i1 %b, label %x42, label %x52
x51: br label %x52

x12: br label %x11
x22: br label %x21
x32: br label %x31
x42: br label %x41
x52: br label %x51

exit:
  ret void
}
