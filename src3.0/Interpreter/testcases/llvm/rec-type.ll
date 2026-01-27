; ModuleID = 'rec-type.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"

%rt = type { %rt* }
%rt1 = type { %rt* }
%rt2 = type { %rt2*, i32, i32, i32, %rt2* }
%rt3 = type { %rt2* }
%rt4 = type { %rt2* }
%rt5 = type { %rt* }
%rt6 = type { %rt* }

define i32 @main() nounwind {
entry:
  %0 = alloca %rt                                 ; <%rt*> [#uses=1]
  %1 = alloca %rt                                 ; <%rt*> [#uses=1]
  %2 = icmp eq %rt* %0, %1                        ; <i1> [#uses=0]
  %3 = alloca %rt2                                ; <%rt2*> [#uses=1]
  %4 = ptrtoint %rt2* %3 to i32                   ; <i32> [#uses=1]
  %5 = alloca %rt2                                ; <%rt2*> [#uses=0]
  %6 = alloca %rt2                                ; <%rt2*> [#uses=0]
  %7 = alloca %rt                                 ; <%rt*> [#uses=0]
  %8 = alloca %rt                                 ; <%rt*> [#uses=0]
  ret i32 %4
}
