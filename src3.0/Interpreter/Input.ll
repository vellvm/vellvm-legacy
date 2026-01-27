; ModuleID = 'Input.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }
%struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }
%struct.tree = type { i32, %struct.tree*, %struct.tree* }
%struct.tree.0 = type { i32, %struct.tree.0*, %struct.tree.0* }

@iters = common global i32 0, align 4
@level = common global i32 0, align 4
@.str = private unnamed_addr constant [24 x i8] c"Treeadd with %d levels\0A\00", align 1
@.str1 = private unnamed_addr constant [26 x i8] c"About to enter TreeAlloc\0A\00", align 1
@.str2 = private unnamed_addr constant [24 x i8] c"About to enter TreeAdd\0A\00", align 1
@stderr = external global %struct._IO_FILE*
@.str3 = private unnamed_addr constant [16 x i8] c"Iteration %d...\00", align 1
@.str4 = private unnamed_addr constant [6 x i8] c"done\0A\00", align 1
@.str5 = private unnamed_addr constant [23 x i8] c"Received result of %d\0A\00", align 1
@allocations = internal global i32 0, align 4
@bytes_allocated = internal global i32 0, align 4
@.str6 = private unnamed_addr constant [17 x i8] c"Cannot allocate\0A\00", align 1
@.str17 = private unnamed_addr constant [56 x i8] c"Allocation stats: %d bytes allocated in %d allocations\0A\00", align 1

define void @filestuff() nounwind {
  ret void
}

define i32 @dealwithargs(i32 %argc, i8** %argv) nounwind {
  %1 = alloca i32, align 4
  %2 = alloca i8**, align 4
  store i32 %argc, i32* %1, align 4
  store i8** %argv, i8*** %2, align 4
  %3 = load i32* %1, align 4
  %4 = icmp sgt i32 %3, 2
  br i1 %4, label %5, label %10

; <label>:5                                       ; preds = %0
  %6 = load i8*** %2, align 4
  %7 = getelementptr inbounds i8** %6, i32 2
  %8 = load i8** %7
  %9 = call i32 @atoi(i8* %8) nounwind readonly
  store i32 %9, i32* @iters, align 4
  br label %11

; <label>:10                                      ; preds = %0
  store i32 1, i32* @iters, align 4
  br label %11

; <label>:11                                      ; preds = %10, %5
  %12 = load i32* %1, align 4
  %13 = icmp sgt i32 %12, 1
  br i1 %13, label %14, label %19

; <label>:14                                      ; preds = %11
  %15 = load i8*** %2, align 4
  %16 = getelementptr inbounds i8** %15, i32 1
  %17 = load i8** %16
  %18 = call i32 @atoi(i8* %17) nounwind readonly
  store i32 %18, i32* @level, align 4
  br label %20

; <label>:19                                      ; preds = %11
  store i32 5, i32* @level, align 4
  br label %20

; <label>:20                                      ; preds = %19, %14
  %21 = load i32* @level, align 4
  ret i32 %21
}

declare i32 @atoi(i8*) nounwind readonly

define i32 @main(i32 %argc, i8** %argv) nounwind {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i8**, align 4
  %root = alloca %struct.tree*, align 4
  %i = alloca i32, align 4
  %result = alloca i32, align 4
  store i32 0, i32* %1
  store i32 %argc, i32* %2, align 4
  store i8** %argv, i8*** %3, align 4
  store i32 0, i32* %result, align 4
  %4 = call i32 bitcast (void ()* @filestuff to i32 ()*)()
  %5 = load i32* %2, align 4
  %6 = load i8*** %3, align 4
  %7 = call i32 @dealwithargs(i32 %5, i8** %6)
  %8 = load i32* @level, align 4
  call void (i8*, ...)* @chatting(i8* getelementptr inbounds ([24 x i8]* @.str, i32 0, i32 0), i32 %8)
  call void (i8*, ...)* @chatting(i8* getelementptr inbounds ([26 x i8]* @.str1, i32 0, i32 0))
  %9 = load i32* @level, align 4
  %10 = call %struct.tree* bitcast (%struct.tree.0* (i32)* @TreeAlloc to %struct.tree* (i32)*)(i32 %9)
  store %struct.tree* %10, %struct.tree** %root, align 4
  call void (i8*, ...)* @chatting(i8* getelementptr inbounds ([24 x i8]* @.str2, i32 0, i32 0))
  store i32 0, i32* %i, align 4
  br label %11

; <label>:11                                      ; preds = %23, %0
  %12 = load i32* %i, align 4
  %13 = load i32* @iters, align 4
  %14 = icmp slt i32 %12, %13
  br i1 %14, label %15, label %26

; <label>:15                                      ; preds = %11
  %16 = load %struct._IO_FILE** @stderr, align 4
  %17 = load i32* %i, align 4
  %18 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %16, i8* getelementptr inbounds ([16 x i8]* @.str3, i32 0, i32 0), i32 %17)
  %19 = load %struct.tree** %root, align 4
  %20 = call i32 @TreeAdd(%struct.tree* %19)
  store i32 %20, i32* %result, align 4
  %21 = load %struct._IO_FILE** @stderr, align 4
  %22 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %21, i8* getelementptr inbounds ([6 x i8]* @.str4, i32 0, i32 0))
  br label %23

; <label>:23                                      ; preds = %15
  %24 = load i32* %i, align 4
  %25 = add nsw i32 %24, 1
  store i32 %25, i32* %i, align 4
  br label %11

; <label>:26                                      ; preds = %11
  %27 = load i32* %result, align 4
  call void (i8*, ...)* @chatting(i8* getelementptr inbounds ([23 x i8]* @.str5, i32 0, i32 0), i32 %27)
  ret i32 0
}

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...)

define i32 @TreeAdd(%struct.tree* %t) nounwind {
  %1 = alloca i32, align 4
  %2 = alloca %struct.tree*, align 4
  %leftval = alloca i32, align 4
  %rightval = alloca i32, align 4
  %tleft = alloca %struct.tree*, align 4
  %tright = alloca %struct.tree*, align 4
  %value = alloca i32, align 4
  store %struct.tree* %t, %struct.tree** %2, align 4
  %3 = load %struct.tree** %2, align 4
  %4 = icmp eq %struct.tree* %3, null
  br i1 %4, label %5, label %6

; <label>:5                                       ; preds = %0
  store i32 0, i32* %1
  br label %25

; <label>:6                                       ; preds = %0
  %7 = load %struct.tree** %2, align 4
  %8 = getelementptr inbounds %struct.tree* %7, i32 0, i32 1
  %9 = load %struct.tree** %8, align 4
  store %struct.tree* %9, %struct.tree** %tleft, align 4
  %10 = load %struct.tree** %tleft, align 4
  %11 = call i32 @TreeAdd(%struct.tree* %10)
  store i32 %11, i32* %leftval, align 4
  %12 = load %struct.tree** %2, align 4
  %13 = getelementptr inbounds %struct.tree* %12, i32 0, i32 2
  %14 = load %struct.tree** %13, align 4
  store %struct.tree* %14, %struct.tree** %tright, align 4
  %15 = load %struct.tree** %tright, align 4
  %16 = call i32 @TreeAdd(%struct.tree* %15)
  store i32 %16, i32* %rightval, align 4
  %17 = load %struct.tree** %2, align 4
  %18 = getelementptr inbounds %struct.tree* %17, i32 0, i32 0
  %19 = load i32* %18, align 4
  store i32 %19, i32* %value, align 4
  %20 = load i32* %leftval, align 4
  %21 = load i32* %rightval, align 4
  %22 = add nsw i32 %20, %21
  %23 = load i32* %value, align 4
  %24 = add nsw i32 %22, %23
  store i32 %24, i32* %1
  br label %25

; <label>:25                                      ; preds = %6, %5
  %26 = load i32* %1
  ret i32 %26
}

define %struct.tree.0* @TreeAlloc(i32 %level) nounwind {
  %1 = alloca %struct.tree.0*, align 4
  %2 = alloca i32, align 4
  %new = alloca %struct.tree.0*, align 4
  %right = alloca %struct.tree.0*, align 4
  %left = alloca %struct.tree.0*, align 4
  store i32 %level, i32* %2, align 4
  %3 = load i32* %2, align 4
  %4 = icmp eq i32 %3, 0
  br i1 %4, label %5, label %6

; <label>:5                                       ; preds = %0
  store %struct.tree.0* null, %struct.tree.0** %1
  br label %24

; <label>:6                                       ; preds = %0
  %7 = call noalias i8* @malloc(i32 12) nounwind
  %8 = bitcast i8* %7 to %struct.tree.0*
  store %struct.tree.0* %8, %struct.tree.0** %new, align 4
  %9 = load i32* %2, align 4
  %10 = sub nsw i32 %9, 1
  %11 = call %struct.tree.0* @TreeAlloc(i32 %10)
  store %struct.tree.0* %11, %struct.tree.0** %left, align 4
  %12 = load i32* %2, align 4
  %13 = sub nsw i32 %12, 1
  %14 = call %struct.tree.0* @TreeAlloc(i32 %13)
  store %struct.tree.0* %14, %struct.tree.0** %right, align 4
  %15 = load %struct.tree.0** %new, align 4
  %16 = getelementptr inbounds %struct.tree.0* %15, i32 0, i32 0
  store i32 1, i32* %16, align 4
  %17 = load %struct.tree.0** %left, align 4
  %18 = load %struct.tree.0** %new, align 4
  %19 = getelementptr inbounds %struct.tree.0* %18, i32 0, i32 1
  store %struct.tree.0* %17, %struct.tree.0** %19, align 4
  %20 = load %struct.tree.0** %right, align 4
  %21 = load %struct.tree.0** %new, align 4
  %22 = getelementptr inbounds %struct.tree.0* %21, i32 0, i32 2
  store %struct.tree.0* %20, %struct.tree.0** %22, align 4
  %23 = load %struct.tree.0** %new, align 4
  store %struct.tree.0* %23, %struct.tree.0** %1
  br label %24

; <label>:24                                      ; preds = %6, %5
  %25 = load %struct.tree.0** %1
  ret %struct.tree.0* %25
}

declare noalias i8* @malloc(i32) nounwind

define void @chatting(i8* %s, ...) nounwind {
  %1 = alloca i8*, align 4
  %ap = alloca i8*, align 4
  store i8* %s, i8** %1, align 4
  %2 = bitcast i8** %ap to i8*
  call void @llvm.va_start(i8* %2)
  %3 = load %struct._IO_FILE** @stderr, align 4
  %4 = load i8** %1, align 4
  %5 = load i8** %ap, align 4
  %6 = call i32 @vfprintf(%struct._IO_FILE* %3, i8* %4, i8* %5)
  %7 = bitcast i8** %ap to i8*
  call void @llvm.va_end(i8* %7)
  ret void
}

declare void @llvm.va_start(i8*) nounwind

declare i32 @vfprintf(%struct._IO_FILE*, i8*, i8*)

declare void @llvm.va_end(i8*) nounwind

define i8* @ssplain_malloc(i32 %size) nounwind {
  %1 = alloca i32, align 4
  store i32 %size, i32* %1, align 4
  %2 = load i32* @allocations, align 4
  %3 = add i32 %2, 1
  store i32 %3, i32* @allocations, align 4
  %4 = load i32* %1, align 4
  %5 = load i32* @bytes_allocated, align 4
  %6 = add i32 %5, %4
  store i32 %6, i32* @bytes_allocated, align 4
  %7 = load i32* %1, align 4
  %8 = call noalias i8* @malloc(i32 %7) nounwind
  ret i8* %8
}

define i8* @ssplain_calloc(i32 %nelems, i32 %size) nounwind {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %p = alloca i8*, align 4
  store i32 %nelems, i32* %1, align 4
  store i32 %size, i32* %2, align 4
  %3 = load i32* @allocations, align 4
  %4 = add i32 %3, 1
  store i32 %4, i32* @allocations, align 4
  %5 = load i32* %1, align 4
  %6 = load i32* %2, align 4
  %7 = mul nsw i32 %5, %6
  %8 = load i32* @bytes_allocated, align 4
  %9 = add i32 %8, %7
  store i32 %9, i32* @bytes_allocated, align 4
  %10 = load i32* %1, align 4
  %11 = load i32* %2, align 4
  %12 = call noalias i8* @calloc(i32 %10, i32 %11) nounwind
  store i8* %12, i8** %p, align 4
  %13 = load i8** %p, align 4
  %14 = icmp ne i8* %13, null
  br i1 %14, label %17, label %15

; <label>:15                                      ; preds = %0
  %16 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([17 x i8]* @.str6, i32 0, i32 0))
  call void @exit(i32 3) noreturn nounwind
  unreachable

; <label>:17                                      ; preds = %0
  %18 = load i8** %p, align 4
  ret i8* %18
}

declare noalias i8* @calloc(i32, i32) nounwind

declare i32 @printf(i8*, ...)

declare void @exit(i32) noreturn nounwind

define void @ssplain_alloc_stats() nounwind {
  %1 = load i32* @bytes_allocated, align 4
  %2 = load i32* @allocations, align 4
  call void (i8*, ...)* @chatting(i8* getelementptr inbounds ([56 x i8]* @.str17, i32 0, i32 0), i32 %1, i32 %2)
  ret void
}
