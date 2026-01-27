
 define void @f({i32, i32*} %t) {
   %t19 = extractvalue { i32, i32* } %t, 0
   ret void
 }
