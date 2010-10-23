; ModuleID = 'Output.bc'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128"
target triple = "x86_64-unknown-linux-gnu"

%0 = type { i32, i32 }

@G = global i32 0                                 ; <i32*> [#uses=0]
@Garr = global [2 x i32] [i32 42, i32 11]         ; <[2 x i32]*> [#uses=0]
@Gstruct = global %0 { i32 89, i32 78 }           ; <%0*> [#uses=0]

declare i44* @test(i32, i54)

define i99 @ttt(i32* %c) {
entry:
  %retval = alloca i32                            ; <i32*> [#uses=2]
  %i = alloca i32                                 ; <i32*> [#uses=3]
  store i32 7, i32* %c, align 4
  %0 = load i32* %c, align 4                      ; <i32> [#uses=0]
  %1 = load i32* @G, align 4                      ; <i32> [#uses=0]
  %q = load i32* @G, align 4                      ; <i32> [#uses=0]
  %j = malloc i32                                 ; <i32*> [#uses=3]
  free i32* %j
  ret i99 0
}

define i32 @main() nounwind {
entry:
  %q = load i32* @G, align 4                      ; <i32> [#uses=0]
  %retval = alloca i32                            ; <i32*> [#uses=2]
  %i = alloca i32                                 ; <i32*> [#uses=3]
  %0 = alloca i32                                 ; <i32*> [#uses=4]
  %"alloca point" = bitcast i32 0 to i32          ; <i32> [#uses=0]
  store i32 7, i32* %i, align 4
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
  %X = ptrtoint i32* %0 to i8           ; yields truncation on 32-bit architecture
  %Y = ptrtoint i32* %i to i64          ; yields zero extension on 32-bit architecture
  %X1 = inttoptr i32 255 to i32*          ; yields zero extension on 64-bit architecture
  %Y1 = inttoptr i32 255 to i32*          ; yields no-op on 32-bit architecture
  %Z1 = inttoptr i64 0 to i32*
  %X2 = bitcast i8 255 to i8              ; yields i8 :-1
  %Y2 = bitcast i32* %i to i100*          ; yields sint*:%x
  %5 = call i99 @ttt(i32* %0)                     ; <i99> [#uses=0]
  %6 = icmp eq i32 4, 5                           ; <i1> [#uses=0]
  %7 = icmp ult i32 %indvar, 5                           ; <i1> [#uses=0]
  %8 = zext i32 257 to i64
  %9 = sext i32 %indvar to i999
  %x1 = load i32* %0, align 4                     ; <i32> [#uses=0]
  %x2 = add i13 7, 8                              ; <i13> [#uses=0]
  br i1 %7, label %Loop, label %return

return:                                           ; preds = %Loop
  %retval1 = load i32* %retval                    ; <i32> [#uses=1]
  ret i32 %retval1
}
