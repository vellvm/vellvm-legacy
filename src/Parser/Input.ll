; ModuleID = 'Input.bc'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128"
target triple = "x86_64-unknown-linux-gnu"

%0 = type { i32, i32 }

@G = global i32 0                                 ; <i32*> [#uses=0]
@Garr = global [2 x i32] [i32 42, i32 11]         ; <[2 x i32]*> [#uses=0]
@Gstruct = global %0 { i32 89, i32 78 }           ; <%0*> [#uses=0]

declare i44* @test(i32, i54)

define i99 @ttt(i32* %c) {
entry:
  ret i99 0
}

define i32 @main() nounwind {
entry:
  %retval = alloca i32                            ; <i32*> [#uses=2]
  %i = alloca i32                                 ; <i32*> [#uses=3]
  %0 = alloca i32                                 ; <i32*> [#uses=3]
  %"alloca point" = bitcast i32 0 to i32          ; <i32> [#uses=0]
  store i32 2, i32* %i, align 4
  %1 = load i32* %i, align 4                      ; <i32> [#uses=0]
  %2 = load i32* %i, align 4                      ; <i32> [#uses=0]
  %3 = add i32 1, 0                               ; <i32> [#uses=1]
  store i32 %3, i32* %0, align 4
  %4 = load i32* %0, align 4                      ; <i32> [#uses=1]
  store i32 %4, i32* %retval, align 4
  br label %Loop

Loop:                                             ; preds = %Loop, %entry
  %indvar = phi i32 [ 0, %entry ], [ %nextindvar, %Loop ] ; <i32> [#uses=1]
  %nextindvar = add i32 %indvar, 1                ; <i32> [#uses=1]
  %5 = call i99 @ttt(i32* %0)                     ; <i99> [#uses=0]
  %6 = icmp eq i32 4, 5                           ; <i1> [#uses=0]
  br i1 false, label %Loop, label %return

return:                                           ; preds = %Loop
  %retval1 = load i32* %retval                    ; <i32> [#uses=1]
  ret i32 %retval1
}
