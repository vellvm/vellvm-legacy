; ModuleID = 'test-softbound.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
	%struct.DIR = type opaque
	%struct.FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct.FILE*, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }
	%struct.PtrBaseBound = type { i8*, i8*, i8* }
	%struct._IO_marker = type { %struct._IO_marker*, %struct.FILE*, i32 }
	%struct.__softbound_hash_table_entry_t = type { i8*, i8*, i8* }
	%struct.__softbound_shadow_space_entry_t = type { i8*, i8* }
	%struct.addrinfo = type { i32, i32, i32, i32, i32, %struct.sockaddr*, i8*, %struct.addrinfo* }
	%struct.dirent = type { i32, i32, i16, i8, [256 x i8] }
	%struct.fd_set = type { [32 x i32] }
	%struct.glob_t = type { i32, i8**, i32, i32, void (i8*)*, i8* (i8*)*, i8* (i8*)*, i32 (i8*, i8*)*, i32 (i8*, i8*)* }
	%struct.group = type { i8*, i8*, i32, i8** }
	%struct.hostent = type { i8*, i8**, i32, i32, i8** }
	%struct.in_addr = type { i32 }
	%struct.option = type { i8*, i32, i32*, i32 }
	%struct.passwd = type { i8*, i8*, i32, i32, i8*, i8*, i8* }
	%struct.rlimit = type { i32, i32 }
	%struct.rusage = type { %struct.rlimit, %struct.rlimit, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32 }
	%struct.servent = type { i8*, i8**, i32, i8* }
	%struct.sockaddr = type { i16, [14 x i8] }
	%struct.stat = type { i64, i16, i32, i32, i32, i32, i32, i64, i16, i32, i32, i32, %struct.rlimit, %struct.rlimit, %struct.rlimit, i32, i32 }
	%struct.tm = type { i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i8* }
	%struct.tms = type { i32, i32, i32, i32 }
	%struct.ttyent = type { i8*, i8*, i8*, i32, i8*, i8* }
@.str = internal constant [17 x i8] c"Hash table full\0A\00"		; <[17 x i8]*> [#uses=1]
@value = global i32 0		; <i32*> [#uses=12]
@.str1 = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]
@__softbound_hash_table_begin = global %struct.PtrBaseBound* null		; <%struct.PtrBaseBound**> [#uses=54]
@stderr = external global %struct.FILE*		; <%struct.FILE**> [#uses=4]
@.str2 = internal constant [60 x i8] c"SoftBound: Inconsistent specification of metadata encoding\0A\00"		; <[60 x i8]*> [#uses=1]
@softbound_initialized.b = internal global i1 false		; <i1*> [#uses=4]
@.str13 = internal constant [43 x i8] c"__softbound_hash_table_begin != (void *)-1\00"		; <[43 x i8]*> [#uses=1]
@.str24 = internal constant [15 x i8] c"../softbound.c\00"		; <[15 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.3087 = internal constant [17 x i8] c"__softbound_init\00"		; <[17 x i8]*> [#uses=1]
@.str3 = internal constant [51 x i8] c"\0ASoftBound: Bounds violation detected\0A\0ABacktrace:\0A\00"		; <[51 x i8]*> [#uses=1]
@.str4 = internal constant [3 x i8] c"\0A\0A\00"		; <[3 x i8]*> [#uses=1]
@.str5 = internal constant [17 x i8] c"Hash table full\0A\00"		; <[17 x i8]*> [#uses=1]
@__softbound_shadow_space_begin = global %struct.__softbound_shadow_space_entry_t* null		; <%struct.__softbound_shadow_space_entry_t**> [#uses=0]
@__softbound_deref_check_count = global i32 0		; <i32*> [#uses=0]
@llvm.global_dtors = appending global [1 x { i32, void ()* }] [ { i32, void ()* } { i32 65535, void ()* @softbound_process_memory_total } ]		; <[1 x { i32, void ()* }]*> [#uses=0]
@.str9 = internal constant [50 x i8] c"[ctype_toupper_loc] pts->ptr = %p, *ptrs->ptr=%p\0A\00"		; <[50 x i8]*> [#uses=1]
@.str110 = internal constant [53 x i8] c"This case not handled, requesting memory from system\00"		; <[53 x i8]*> [#uses=1]
@.str211 = internal constant [17 x i8] c"Hash table full\0A\00"		; <[17 x i8]*> [#uses=1]
@llvm.global_ctors = appending global [3 x { i32, void ()* }] [ { i32, void ()* } { i32 65535, void ()* @__softbound_global_init }, { i32, void ()* } { i32 65535, void ()* @__softbound_global_init7 }, { i32, void ()* } { i32 65535, void ()* @__softbound_global_init13 } ]		; <[3 x { i32, void ()* }]*> [#uses=0]

define weak void @__shrinkBounds(i8* %new_base, i8* %new_bound, i8* %old_base, i8* %old_bound, i8** %base_alloca, i8** %bound_alloca) nounwind alwaysinline {
entry:
	%0 = icmp uge i8* %new_base, %old_base		; <i1> [#uses=1]
	%max = select i1 %0, i8* %new_base, i8* %old_base		; <i8*> [#uses=1]
	store i8* %max, i8** %base_alloca, align 4
	%1 = icmp ule i8* %new_bound, %old_bound		; <i1> [#uses=1]
	%min = select i1 %1, i8* %new_bound, i8* %old_bound		; <i8*> [#uses=1]
	store i8* %min, i8** %bound_alloca, align 4
	ret void
}

define weak void @__callDereferenceCheck(i8* %base, i8* %bound, i8* %ptr) nounwind alwaysinline {
entry:
	%0 = icmp ne i8* %base, %bound		; <i1> [#uses=1]
	%1 = icmp ne i8* %ptr, %base		; <i1> [#uses=1]
	%2 = and i1 %1, %0		; <i1> [#uses=1]
	br i1 %2, label %bb, label %return

bb:		; preds = %entry
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %entry
	ret void
}

define weak void @__loadDereferenceCheck(i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = icmp ult i8* %ptr, %base		; <i1> [#uses=1]
	br i1 %0, label %bb1, label %bb

bb:		; preds = %entry
	%1 = getelementptr i8* %ptr, i32 %size_of_type		; <i8*> [#uses=1]
	%2 = icmp ugt i8* %1, %bound		; <i1> [#uses=1]
	br i1 %2, label %bb1, label %return

bb1:		; preds = %bb, %entry
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %bb
	ret void
}

define weak void @__storeDereferenceCheck(i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = icmp ult i8* %ptr, %base		; <i1> [#uses=1]
	br i1 %0, label %bb1, label %bb

bb:		; preds = %entry
	%1 = getelementptr i8* %ptr, i32 %size_of_type		; <i8*> [#uses=1]
	%2 = icmp ugt i8* %1, %bound		; <i1> [#uses=1]
	br i1 %2, label %bb1, label %return

bb1:		; preds = %bb, %entry
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %bb
	ret void
}

define weak void @__memcopyCheck_i64(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
	%0 = icmp ugt i32 %size, -2147483648		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%1 = icmp ult i8* %ptr, %ptr_base		; <i1> [#uses=1]
	br i1 %1, label %bb6, label %bb2

bb2:		; preds = %bb1
	%2 = getelementptr i8* %ptr, i32 %size		; <i8*> [#uses=2]
	%3 = icmp ult i8* %2, %ptr_base		; <i1> [#uses=1]
	br i1 %3, label %bb6, label %bb3

bb3:		; preds = %bb2
	%4 = icmp ugt i8* %2, %ptr_bound		; <i1> [#uses=1]
	%5 = inttoptr i32 %size to i8*		; <i8*> [#uses=1]
	%6 = icmp ugt i8* %5, %ptr_bound		; <i1> [#uses=1]
	%7 = or i1 %4, %6		; <i1> [#uses=1]
	br i1 %7, label %bb6, label %return

bb6:		; preds = %bb3, %bb2, %bb1
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %bb3
	ret void
}

define weak void @__memcopyCheck(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
	%0 = icmp ugt i32 %size, -2147483648		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%1 = icmp ult i8* %ptr, %ptr_base		; <i1> [#uses=1]
	br i1 %1, label %bb6, label %bb2

bb2:		; preds = %bb1
	%2 = getelementptr i8* %ptr, i32 %size		; <i8*> [#uses=2]
	%3 = icmp ult i8* %2, %ptr_base		; <i1> [#uses=1]
	br i1 %3, label %bb6, label %bb3

bb3:		; preds = %bb2
	%4 = icmp ugt i8* %2, %ptr_bound		; <i1> [#uses=1]
	%5 = inttoptr i32 %size to i8*		; <i8*> [#uses=1]
	%6 = icmp ugt i8* %5, %ptr_bound		; <i1> [#uses=1]
	%7 = or i1 %4, %6		; <i1> [#uses=1]
	br i1 %7, label %bb6, label %return

bb6:		; preds = %bb3, %bb2, %bb1
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %bb3
	ret void
}

define weak void @__hashStoreBaseBound(i8* %addr_of_ptr, i8* %base, i8* %bound, i8* %actual_ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb

bb:		; preds = %bb8, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %indvar.next19, %bb8 ]		; <i32> [#uses=3]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 2		; <i8**> [#uses=2]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	%8 = icmp eq i8* %6, null		; <i1> [#uses=1]
	%9 = or i1 %7, %8		; <i1> [#uses=1]
	br i1 %9, label %bb3, label %bb6

bb3:		; preds = %bb
	%10 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	store i8* %base, i8** %10, align 4
	%11 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	store i8* %bound, i8** %11, align 4
	store i8* %addr_of_ptr, i8** %5, align 4
	ret void

bb6:		; preds = %bb
	%12 = icmp ugt i32 %counter.0, 134217727		; <i1> [#uses=1]
	br i1 %12, label %bb7, label %bb8

bb7:		; preds = %bb6
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8:		; preds = %bb6
	%indvar.next19 = add i32 %counter.0, 1		; <i32> [#uses=1]
	br label %bb
}

define weak i32 @__hashProbeAddrOfPtr(i8* %addr_of_ptr, i8** %base, i8** %bound) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb

bb:		; preds = %bb6, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %indvar.next15, %bb6 ]		; <i32> [#uses=2]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 2		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	br i1 %7, label %bb1, label %bb4

bb1:		; preds = %bb
	%8 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	%9 = load i8** %8, align 4		; <i8*> [#uses=2]
	%10 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	%11 = load i8** %10, align 4		; <i8*> [#uses=2]
	store i8* %9, i8** %base, align 4
	store i8* %11, i8** %bound, align 4
	%12 = ptrtoint i8* %9 to i32		; <i32> [#uses=1]
	%13 = ptrtoint i8* %11 to i32		; <i32> [#uses=1]
	%14 = or i32 %13, %12		; <i32> [#uses=1]
	%15 = inttoptr i32 %14 to i8*		; <i8*> [#uses=1]
	%not. = icmp ne i8* %15, null		; <i1> [#uses=1]
	%retval = zext i1 %not. to i32		; <i32> [#uses=1]
	ret i32 %retval

bb4:		; preds = %bb
	%16 = icmp eq i8* %6, null		; <i1> [#uses=1]
	br i1 %16, label %bb7, label %bb6

bb6:		; preds = %bb4
	%indvar.next15 = add i32 %counter.0, 1		; <i32> [#uses=1]
	br label %bb

bb7:		; preds = %bb4
	ret i32 0
}

define weak void @__hashLoadBaseBound(i8* %addr_of_ptr, i8** %base, i8** %bound, i8* %actual_ptr, i32 %size_of_type, i32* %ptr_safe) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb

bb:		; preds = %bb2, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %7, %bb2 ]		; <i32> [#uses=2]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 2		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = add i32 %counter.0, 1		; <i32> [#uses=2]
	%8 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	br i1 %8, label %bb1, label %bb2

bb1:		; preds = %bb
	%9 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	%10 = load i8** %9, align 4		; <i8*> [#uses=1]
	%11 = getelementptr %struct.PtrBaseBound* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	%12 = load i8** %11, align 4		; <i8*> [#uses=1]
	br label %bb4

bb2:		; preds = %bb
	%13 = icmp eq i8* %6, null		; <i1> [#uses=1]
	br i1 %13, label %bb4, label %bb

bb4:		; preds = %bb2, %bb1
	%final_bound.0 = phi i8* [ %12, %bb1 ], [ null, %bb2 ]		; <i8*> [#uses=1]
	%final_base.0 = phi i8* [ %10, %bb1 ], [ null, %bb2 ]		; <i8*> [#uses=1]
	store i8* %final_base.0, i8** %base, align 4
	store i8* %final_bound.0, i8** %bound, align 4
	%14 = icmp ugt i32 %7, 134217727		; <i1> [#uses=1]
	br i1 %14, label %bb5, label %return

bb5:		; preds = %bb4
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %bb4
	ret void
}

define internal void @__softbound_global_init() nounwind {
entry:
	tail call void @__softbound_init(i32 1, i32 0) nounwind
	ret void
}

define i32 @softbound_pseudo_main(i32 %argc, i8** %argv, i8* %argv_base, i8* %argv_bound) {
entry:
	%argv_bound2 = bitcast i8* %argv_bound to i8*		; <i8*> [#uses=1]
	%argv_base1 = bitcast i8* %argv_base to i8*		; <i8*> [#uses=1]
	%base.alloca = alloca i8*		; <i8**> [#uses=2]
	%bound.alloca = alloca i8*		; <i8**> [#uses=2]
	%safe.ptr = alloca i32		; <i32*> [#uses=2]
	%0 = getelementptr i8** %argv, i32 1		; <i8**> [#uses=3]
	%bcast_ld_dref_base = bitcast i8* %argv_base1 to i8*		; <i8*> [#uses=1]
	%bcast_arg_bound3 = bitcast i8* %argv_bound2 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound = bitcast i8** %0 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base, i8* %bcast_arg_bound3, i8* %bcast_ld_dref_bound, i32 ptrtoint (i8** getelementptr (i8** null, i32 1) to i32), i32 1)
	%1 = load i8** %0, align 4		; <i8*> [#uses=2]
	%.ptr = bitcast i8** %0 to i8*		; <i8*> [#uses=1]
	%.ptrcast = bitcast i8* %1 to i8*		; <i8*> [#uses=1]
	call void @__hashLoadBaseBound(i8* %.ptr, i8** %base.alloca, i8** %bound.alloca, i8* %.ptrcast, i32 ptrtoint (i8* getelementptr (i8* null, i32 1) to i32), i32* %safe.ptr)
	%base.load = load i8** %base.alloca		; <i8*> [#uses=1]
	%bound.load = load i8** %bound.alloca		; <i8*> [#uses=1]
	%safe.ptr.load = load i32* %safe.ptr		; <i32> [#uses=0]
	%base.load1 = bitcast i8* %base.load to i8*		; <i8*> [#uses=1]
	%bound.load2 = bitcast i8* %bound.load to i8*		; <i8*> [#uses=1]
	%2 = call i32 @softbound_atoi(i8* %1, i8* %base.load1, i8* %bound.load2)		; <i32> [#uses=1]
	tail call void @softbound_test(i32 %2) nounwind
	ret i32 0
}

declare i32 @pseudo_main(i32, i8** nocapture)

declare i32 @atoi(i8*) nounwind readonly

define void @softbound_test(i32 %mm) {
entry:
	%0 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.03 = phi i32 [ 0, %entry ], [ %6, %bb ]		; <i32> [#uses=2]
	%ptr.04.rec = phi i32 [ 0, %entry ], [ %.rec, %bb ]		; <i32> [#uses=2]
	%ptr.04.sum = add i32 %ptr.04.rec, %i.03		; <i32> [#uses=1]
	%bitcast = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	%bitcast1 = bitcast i32* getelementptr (i32* @value, i32 1) to i8*		; <i8*> [#uses=1]
	%1 = getelementptr i32* @value, i32 %ptr.04.sum		; <i32*> [#uses=2]
	%bcast_ld_dref_base = bitcast i8* %bitcast to i8*		; <i8*> [#uses=1]
	%bitcast12 = bitcast i8* %bitcast1 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound = bitcast i32* %1 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base, i8* %bitcast12, i8* %bcast_ld_dref_bound, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%2 = load i32* %1, align 4		; <i32> [#uses=1]
	%bcast_ld_dref_base3 = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	%3 = bitcast i32* getelementptr (i32* @value, i32 1) to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound4 = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base3, i8* %3, i8* %bcast_ld_dref_bound4, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%4 = load i32* @value, align 4		; <i32> [#uses=1]
	%5 = add i32 %4, %2		; <i32> [#uses=1]
	%bcast_st_dref_base = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_bound = bitcast i32* getelementptr (i32* @value, i32 1) to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_ptr = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	call void @__storeDereferenceCheck(i8* %bcast_st_dref_base, i8* %bcast_st_dref_bound, i8* %bcast_st_dref_ptr, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	store i32 %5, i32* @value, align 4
	%6 = add i32 %i.03, 1		; <i32> [#uses=3]
	%.rec = add i32 %ptr.04.rec, %6		; <i32> [#uses=1]
	%exitcond5 = icmp eq i32 %6, %mm		; <i1> [#uses=1]
	br i1 %exitcond5, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%bcast_ld_dref_base5 = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	%7 = bitcast i32* getelementptr (i32* @value, i32 1) to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound6 = bitcast i32* @value to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base5, i8* %7, i8* %bcast_ld_dref_bound6, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%8 = load i32* @value, align 4		; <i32> [#uses=1]
	%9 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str1, i32 0, i32 0), i32 %8) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind

define internal void @softbound_process_memory_total() nounwind readnone {
entry:
	ret void
}

define void @__softbound_printf(i8* %str, ...) nounwind {
entry:
	%args = alloca i8*, align 4		; <i8**> [#uses=2]
	%args1 = bitcast i8** %args to i8*		; <i8*> [#uses=2]
	call void @llvm.va_start(i8* %args1)
	%0 = load i8** %args, align 4		; <i8*> [#uses=1]
	%1 = load %struct.FILE** @stderr, align 4		; <%struct.FILE*> [#uses=1]
	%2 = call i32 @vfprintf(%struct.FILE* noalias %1, i8* noalias %str, i8* %0) nounwind		; <i32> [#uses=0]
	call void @llvm.va_end(i8* %args1)
	ret void
}

declare void @llvm.va_start(i8*) nounwind

declare i32 @vfprintf(%struct.FILE* noalias, i8* noalias, i8*) nounwind

declare void @llvm.va_end(i8*) nounwind

define void @__softbound_init(i32 %is_hash_table, i32 %is_shadow_space) nounwind {
entry:
	%0 = icmp eq i32 %is_hash_table, 1		; <i1> [#uses=1]
	br i1 %0, label %bb1, label %bb

bb:		; preds = %entry
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([60 x i8]* @.str2, i32 0, i32 0)) nounwind
	tail call void @abort() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%1 = icmp eq i32 %is_shadow_space, 0		; <i1> [#uses=1]
	br i1 %1, label %bb3, label %bb2

bb2:		; preds = %bb1
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([60 x i8]* @.str2, i32 0, i32 0)) nounwind
	tail call void @abort() noreturn nounwind
	unreachable

bb3:		; preds = %bb1
	%.b = load i1* @softbound_initialized.b		; <i1> [#uses=1]
	br i1 %.b, label %return, label %bb4

bb4:		; preds = %bb3
	store i1 true, i1* @softbound_initialized.b
	%2 = tail call i8* @mmap(i8* null, i32 1610612736, i32 3, i32 16418, i32 -1, i32 0) nounwind		; <i8*> [#uses=2]
	%3 = bitcast i8* %2 to %struct.PtrBaseBound*		; <%struct.PtrBaseBound*> [#uses=1]
	store %struct.PtrBaseBound* %3, %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4
	%4 = icmp eq i8* %2, inttoptr (i64 4294967295 to i8*)		; <i1> [#uses=1]
	br i1 %4, label %bb5, label %return

bb5:		; preds = %bb4
	tail call void @__assert_fail(i8* getelementptr ([43 x i8]* @.str13, i32 0, i32 0), i8* getelementptr ([15 x i8]* @.str24, i32 0, i32 0), i32 106, i8* getelementptr ([17 x i8]* @__PRETTY_FUNCTION__.3087, i32 0, i32 0)) noreturn nounwind
	unreachable

return:		; preds = %bb4, %bb3
	ret void
}

declare void @abort() noreturn nounwind

declare i8* @mmap(i8*, i32, i32, i32, i32, i32) nounwind

declare void @__assert_fail(i8*, i8*, i32, i8*) noreturn nounwind

define internal void @__softbound_global_init7() nounwind {
entry:
	%.b.i = load i1* @softbound_initialized.b		; <i1> [#uses=1]
	br i1 %.b.i, label %__softbound_init.exit, label %bb4.i

bb4.i:		; preds = %entry
	store i1 true, i1* @softbound_initialized.b
	%0 = tail call i8* @mmap(i8* null, i32 1610612736, i32 3, i32 16418, i32 -1, i32 0) nounwind		; <i8*> [#uses=2]
	%1 = bitcast i8* %0 to %struct.PtrBaseBound*		; <%struct.PtrBaseBound*> [#uses=1]
	store %struct.PtrBaseBound* %1, %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4
	%2 = icmp eq i8* %0, inttoptr (i64 4294967295 to i8*)		; <i1> [#uses=1]
	br i1 %2, label %bb5.i, label %__softbound_init.exit

bb5.i:		; preds = %bb4.i
	tail call void @__assert_fail(i8* getelementptr ([43 x i8]* @.str13, i32 0, i32 0), i8* getelementptr ([15 x i8]* @.str24, i32 0, i32 0), i32 106, i8* getelementptr ([17 x i8]* @__PRETTY_FUNCTION__.3087, i32 0, i32 0)) noreturn nounwind
	unreachable

__softbound_init.exit:		; preds = %bb4.i, %entry
	ret void
}

define void @__softbound_abort() nounwind {
entry:
	%array = alloca [100 x i8*], align 4		; <[100 x i8*]*> [#uses=1]
	%0 = load %struct.FILE** @stderr, align 4		; <%struct.FILE*> [#uses=1]
	%1 = bitcast %struct.FILE* %0 to i8*		; <i8*> [#uses=1]
	%2 = call i32 @fwrite(i8* getelementptr ([51 x i8]* @.str3, i32 0, i32 0), i32 1, i32 50, i8* %1) nounwind		; <i32> [#uses=0]
	%array1 = getelementptr [100 x i8*]* %array, i32 0, i32 0		; <i8**> [#uses=2]
	%3 = call i32 @backtrace(i8** %array1, i32 100) nounwind		; <i32> [#uses=1]
	%4 = load %struct.FILE** @stderr, align 4		; <%struct.FILE*> [#uses=1]
	%5 = call i32 @fileno(%struct.FILE* %4) nounwind		; <i32> [#uses=1]
	call void @backtrace_symbols_fd(i8** %array1, i32 %3, i32 %5) nounwind
	%6 = load %struct.FILE** @stderr, align 4		; <%struct.FILE*> [#uses=1]
	%7 = bitcast %struct.FILE* %6 to i8*		; <i8*> [#uses=1]
	%8 = call i32 @fwrite(i8* getelementptr ([3 x i8]* @.str4, i32 0, i32 0), i32 1, i32 2, i8* %7) nounwind		; <i32> [#uses=0]
	call void @abort() noreturn nounwind
	unreachable
}

declare i32 @fwrite(i8*, i32, i32, i8*)

declare i32 @backtrace(i8**, i32)

declare i32 @fileno(%struct.FILE*) nounwind

declare void @backtrace_symbols_fd(i8**, i32, i32) nounwind

declare i16** @__ctype_b_loc() nounwind readnone

define i32 @main(i32 %argc, i8** nocapture %argv) nounwind {
entry:
	%0 = alloca i8*, i32 %argc, align 4		; <i8**> [#uses=4]
	%tmpcast = bitcast i8** %0 to i8*		; <i8*> [#uses=1]
	%1 = call i32 @mallopt(i32 -4, i32 0) nounwind		; <i32> [#uses=0]
	br label %bb14

bb:		; preds = %bb14
	%2 = getelementptr i8** %argv, i32 %i.0		; <i8**> [#uses=1]
	%3 = load i8** %2, align 4		; <i8*> [#uses=4]
	%4 = getelementptr i8** %0, i32 %i.0		; <i8**> [#uses=3]
	store i8* %3, i8** %4, align 4
	%5 = call i32 @strlen(i8* %3) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %5, 1		; <i32> [#uses=1]
	%6 = getelementptr i8* %3, i32 %.sum		; <i8*> [#uses=1]
	%7 = bitcast i8** %4 to i8*		; <i8*> [#uses=2]
	%8 = ptrtoint i8** %4 to i32		; <i32> [#uses=1]
	%9 = lshr i32 %8, 2		; <i32> [#uses=1]
	%10 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb
	%counter.0.i = phi i32 [ 0, %bb ], [ %indvar.next, %bb8.i ]		; <i32> [#uses=3]
	%11 = add i32 %counter.0.i, %9		; <i32> [#uses=1]
	%12 = and i32 %11, 134217727		; <i32> [#uses=3]
	%13 = getelementptr %struct.PtrBaseBound* %10, i32 %12, i32 2		; <i8**> [#uses=2]
	%14 = load i8** %13, align 4		; <i8*> [#uses=2]
	%15 = icmp eq i8* %14, %7		; <i1> [#uses=1]
	%16 = icmp eq i8* %14, null		; <i1> [#uses=1]
	%17 = or i1 %15, %16		; <i1> [#uses=1]
	br i1 %17, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%18 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %18, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str5, i32 0, i32 0)) nounwind
	call void @__softbound_abort() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%19 = getelementptr %struct.PtrBaseBound* %10, i32 %12, i32 0		; <i8**> [#uses=1]
	store i8* %3, i8** %19, align 4
	%20 = getelementptr %struct.PtrBaseBound* %10, i32 %12, i32 1		; <i8**> [#uses=1]
	store i8* %6, i8** %20, align 4
	store i8* %7, i8** %13, align 4
	%indvar.next49 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb14

bb14:		; preds = %__hashStoreBaseBound.exit, %entry
	%i.0 = phi i32 [ 0, %entry ], [ %indvar.next49, %__hashStoreBaseBound.exit ]		; <i32> [#uses=4]
	%21 = icmp slt i32 %i.0, %argc		; <i1> [#uses=1]
	br i1 %21, label %bb, label %bb15

bb15:		; preds = %bb14
	%22 = call i16** @__ctype_b_loc() nounwind readnone		; <i16**> [#uses=3]
	%23 = bitcast i16** %22 to i8*		; <i8*> [#uses=2]
	%24 = load i16** %22, align 4		; <i16*> [#uses=1]
	%25 = bitcast i16* %24 to i8*		; <i8*> [#uses=2]
	%26 = getelementptr i8* %25, i32 256		; <i8*> [#uses=1]
	%27 = getelementptr i8* %25, i32 -129		; <i8*> [#uses=1]
	%28 = ptrtoint i16** %22 to i32		; <i32> [#uses=1]
	%29 = lshr i32 %28, 2		; <i32> [#uses=1]
	%30 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i.i

bb.i.i:		; preds = %bb8.i.i, %bb15
	%counter.0.i.i = phi i32 [ 0, %bb15 ], [ %indvar.next44, %bb8.i.i ]		; <i32> [#uses=3]
	%31 = add i32 %counter.0.i.i, %29		; <i32> [#uses=1]
	%32 = and i32 %31, 134217727		; <i32> [#uses=3]
	%33 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 2		; <i8**> [#uses=2]
	%34 = load i8** %33, align 4		; <i8*> [#uses=2]
	%35 = icmp eq i8* %34, %23		; <i1> [#uses=1]
	%36 = icmp eq i8* %34, null		; <i1> [#uses=1]
	%37 = or i1 %35, %36		; <i1> [#uses=1]
	br i1 %37, label %softbound_init_ctype.exit, label %bb6.i.i

bb6.i.i:		; preds = %bb.i.i
	%38 = icmp ugt i32 %counter.0.i.i, 134217727		; <i1> [#uses=1]
	br i1 %38, label %bb7.i.i, label %bb8.i.i

bb7.i.i:		; preds = %bb6.i.i
	call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str5, i32 0, i32 0)) nounwind
	call void @__softbound_abort() noreturn nounwind
	unreachable

bb8.i.i:		; preds = %bb6.i.i
	%indvar.next44 = add i32 %counter.0.i.i, 1		; <i32> [#uses=1]
	br label %bb.i.i

softbound_init_ctype.exit:		; preds = %bb.i.i
	%39 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 0		; <i8**> [#uses=1]
	store i8* %27, i8** %39, align 4
	%40 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 1		; <i8**> [#uses=1]
	store i8* %26, i8** %40, align 4
	store i8* %23, i8** %33, align 4
	%41 = getelementptr i8** %0, i32 %argc		; <i8**> [#uses=2]
	%42 = bitcast i8** %41 to i8*		; <i8*> [#uses=1]
	%43 = getelementptr i8* %42, i32 8		; <i8*> [#uses=1]
	store i8* null, i8** %41, align 4
	%44 = call i32 @softbound_pseudo_main(i32 %argc, i8** %0, i8* %tmpcast, i8* %43) nounwind		; <i32> [#uses=1]
	ret i32 %44
}

declare i32 @mallopt(i32, i32) nounwind

declare i32 @strlen(i8*) nounwind readonly

define weak i32 @softbound_system(i8* %ptr, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @system(i8* %ptr) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_setreuid(i32 %ruid, i32 %euid) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setreuid(i32 %ruid, i32 %euid) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_mkstemp(i8* %template, i8* %template_base, i8* %template_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @mkstemp(i8* %template) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_getuid() nounwind alwaysinline {
entry:
	%0 = tail call i32 @getuid() nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_getrlimit(i32 %resource, %struct.rlimit* %rlim, i8* %rlim_base, i8* %rlim_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getrlimit(i32 %resource, %struct.rlimit* %rlim) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_setrlimit(i32 %resource, %struct.rlimit* %rlim, i8* %rlim_base, i8* %rlim_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setrlimit(i32 %resource, %struct.rlimit* %rlim) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak void @softbound_qsort(i8* %base, i32 %nmemb, i32 %size, i32 (i8*, i8*)* %compar, i8* %base_base, i8* %base_bound, i8* %compar_base, i8* %compar_bound) nounwind alwaysinline {
entry:
	tail call void @qsort(i8* %base, i32 %nmemb, i32 %size, i32 (i8*, i8*)* %compar) nounwind
	ret void
}

define weak i32 @softbound_fread(i8* %ptr, i32 %size, i32 %nmemb, %struct.FILE* %stream, i8* %ptr_base, i8* %ptr_bound, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fread(i8* noalias %ptr, i32 %size, i32 %nmemb, %struct.FILE* noalias %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_umask(i32 %mask) nounwind alwaysinline {
entry:
	%0 = tail call i32 @umask(i32 %mask) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_mkdir(i8* %pathname, i32 %mode, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @mkdir(i8* %pathname, i32 %mode) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_chroot(i8* %path, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @chroot(i8* %path) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_rmdir(i8* %pathname, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @rmdir(i8* %pathname) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_stat(i8* %path, %struct.stat* %buf, i8* %path_base, i8* %path_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @stat(i8* %path, %struct.stat* %buf) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_fputc(i32 %c, %struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fputc(i32 %c, %struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_fileno(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fileno(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_fgetc(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fgetc(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

define weak i32 @softbound_strncmp(i8* %s1, i8* %s2, i32 %n, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strncmp(i8* %s1, i8* %s2, i32 %n) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

define weak double @softbound_log(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @llvm.log.f64(double %x)		; <double> [#uses=1]
	ret double %0
}

define i64 @softbound_fwrite(i8* %ptr, i32 %size, i32 %nmemb, %struct.FILE* %stream, i8* nocapture %ptr_base, i8* nocapture %ptr_bound, i8* nocapture %stream_base, i8* nocapture %stream_bound) nounwind {
entry:
	%0 = tail call i32 bitcast (i32 (i8*, i32, i32, i8*)* @fwrite to i32 (i8*, i32, i32, %struct.FILE*)*)(i8* noalias %ptr, i32 %size, i32 %nmemb, %struct.FILE* noalias %stream) nounwind		; <i32> [#uses=1]
	%1 = zext i32 %0 to i64		; <i64> [#uses=1]
	ret i64 %1
}

declare i32 @stat(i8*, %struct.stat*) nounwind

define weak double @softbound_atof(i8* %ptr, i8* %base, i8* %bound) nounwind alwaysinline {
entry:
	%0 = tail call double @atof(i8* %ptr) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @atof(i8*) nounwind readonly

define weak double @softbound_fabs(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @fabs(double %x) nounwind readnone		; <double> [#uses=1]
	ret double %0
}

declare double @fabs(double) nounwind readnone

define weak float @softbound_fabsf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @fabsf(float %x) nounwind readnone		; <float> [#uses=1]
	ret float %0
}

declare float @fabsf(float) nounwind readnone

define weak i32 @softbound_fstat(i32 %filedes, %struct.stat* %buff, i8* %buff_base, i8* %buff_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fstat(i32 %filedes, %struct.stat* %buff) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @fstat(i32, %struct.stat*) nounwind

define weak i32 @softbound_atol(i8* %nptr, i8* %base, i8* %bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @atol(i8* %nptr) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @atol(i8*) nounwind readonly

define weak i32 @softbound_putchar(i32 %c) nounwind alwaysinline {
entry:
	%0 = tail call i32 @putchar(i32 %c) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @putchar(i32)

define weak i32 @softbound_lstat(i8* %path, %struct.stat* %buf, i8* %path_base, i8* %path_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @lstat(i8* %path, %struct.stat* %buf) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @lstat(i8*, %struct.stat*) nounwind

define weak i32 @softbound_vprintf(i8* %format, i8* %ap, i8* %format_base, i8* %format_bound, i8* %ap_base, i8* %ap_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @vprintf(i8* noalias %format, i8* %ap) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @vprintf(i8* noalias, i8*) nounwind

define weak void @softbound_bcopy(i8* %src, i8* %dest, i32 %n, i8* %src_base, i8* %src_bound, i8* %dest_base, i8* %dest_bound) nounwind alwaysinline {
entry:
	tail call void @bcopy(i8* %src, i8* %dest, i32 %n) nounwind
	ret void
}

declare void @bcopy(i8*, i8*, i32) nounwind

define weak i32 @softbound_strlen(i8* %s, i8* %base, i8* %bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strlen(i8* %s) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

define void @softbound_globfree(%struct.glob_t* %pglob, i8* nocapture %pglob_base, i8* nocapture %pglob_bound) nounwind {
entry:
	tail call void @globfree(%struct.glob_t* %pglob) nounwind
	ret void
}

declare void @globfree(%struct.glob_t*) nounwind

define weak void @softbound_my_mmap(%struct.PtrBaseBound* %ptrs, i8* %start, i32 %length, i32 %prot, i32 %flags, i32 %fd, i32 %offset, i8* %start_base, i8* %start_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @mmap(i8* %start, i32 %length, i32 %prot, i32 %flags, i32 %fd, i32 %offset) nounwind		; <i8*> [#uses=4]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = icmp eq i8* %0, null		; <i1> [#uses=1]
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %2, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %0, i8** %3, align 4
	%4 = getelementptr i8* %0, i32 %length		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %3, align 4
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %6, align 4
	ret void
}

define weak void @softbound_crypt(%struct.PtrBaseBound* %ptrs, i8* %key, i8* %salt, i8* %key_base, i8* %key_bound, i8* %salt_base, i8* %salt_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @crypt(i8* %key, i8* %salt) nounwind		; <i8*> [#uses=4]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = tail call i32 @strlen(i8* %0) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %3, 1		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i8* @crypt(i8*, i8*)

define weak i32 @softbound_usleep(i32 %usec) nounwind alwaysinline {
entry:
	%0 = tail call i32 @usleep(i32 %usec) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @usleep(i32)

define weak i32 @softbound_strftime(i8* %s, i32 %max, i8* %format, %struct.tm* %tm, i8* %s_base, i8* %s_bound, i8* %format_base, i8* %format_bound, i8* %tm_base, i8* %tm_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strftime(i8* noalias %s, i32 %max, i8* noalias %format, %struct.tm* noalias %tm) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @strftime(i8* noalias, i32, i8* noalias, %struct.tm* noalias) nounwind

define weak i32 @softbound_select(i32 %nfds, %struct.fd_set* %readfds, %struct.fd_set* %writefds, %struct.fd_set* %exceptfds, %struct.rlimit* %timeout, i8* %readfds_base, i8* %readfds_bound, i8* %writefds_base, i8* %writefds_bound, i8* %exceptfds_base, i8* %exceptfds_bound, i8* %timeout_base, i8* %timeout_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @select(i32 %nfds, %struct.fd_set* noalias %readfds, %struct.fd_set* noalias %writefds, %struct.fd_set* noalias %exceptfds, %struct.rlimit* noalias %timeout) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @select(i32, %struct.fd_set* noalias, %struct.fd_set* noalias, %struct.fd_set* noalias, %struct.rlimit* noalias)

define weak i32 @softbound_alphasort(i8* %a, i8* %b, i8* %a_base, i8* %a_bound, i8* %b_base, i8* %b_bound) nounwind alwaysinline {
entry:
	%0 = bitcast i8* %b to %struct.dirent**		; <%struct.dirent**> [#uses=1]
	%1 = bitcast i8* %a to %struct.dirent**		; <%struct.dirent**> [#uses=1]
	%2 = tail call i32 @alphasort(%struct.dirent** %1, %struct.dirent** %0) nounwind readonly		; <i32> [#uses=1]
	ret i32 %2
}

declare i32 @alphasort(%struct.dirent**, %struct.dirent**) nounwind readonly

define weak i32 @softbound_getnameinfo(%struct.sockaddr* %sa, i32 %salen, i8* %host, i32 %hostlen, i8* %serv, i32 %servlen, i32 %flags, i8* %sa_base, i8* %sa_bound, i8* %host_base, i8* %host_bound, i8* %serv_base, i8* %serv_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getnameinfo(%struct.sockaddr* noalias %sa, i32 %salen, i8* noalias %host, i32 %hostlen, i8* noalias %serv, i32 %servlen, i32 %flags) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getnameinfo(%struct.sockaddr* noalias, i32, i8* noalias, i32, i8* noalias, i32, i32)

define weak i32 @softbound_fchmod(i32 %fildes, i32 %mode) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fchmod(i32 %fildes, i32 %mode) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @fchmod(i32, i32) nounwind

define weak i32 @softbound_setsockopt(i32 %s, i32 %level, i32 %optname, i8* %optval, i32 %optlen, i8* %optval_base, i8* %optval_bound, i8* %optlen_base, i8* %optlen_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setsockopt(i32 %s, i32 %level, i32 %optname, i8* %optval, i32 %optlen) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @setsockopt(i32, i32, i32, i8*, i32) nounwind

define weak i32 @softbound_munmap(i8* %start, i32 %length, i8* %start_base, i8* %start_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @munmap(i8* %start, i32 %length) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @munmap(i8*, i32) nounwind

define weak i32 @softbound_alarm(i32 %seconds) nounwind alwaysinline {
entry:
	%0 = tail call i32 @alarm(i32 %seconds) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @alarm(i32) nounwind

define weak void @softbound_realpath(%struct.PtrBaseBound* %ptrs, i8* %path, i8* %resolved_path, i8* %path_base, i8* %path_bound, i8* %resolved_path_base, i8* %resolved_path_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @realpath(i8* noalias %path, i8* noalias %resolved_path) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %resolved_path_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %resolved_path_bound, i8** %3, align 4
	ret void
}

declare i8* @realpath(i8* noalias, i8* noalias) nounwind

define weak i32 @softbound_getdtablesize() nounwind alwaysinline {
entry:
	%0 = tail call i32 @getdtablesize() nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getdtablesize() nounwind

define weak void @softbound_getusershell(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call i8* @getusershell() nounwind		; <i8*> [#uses=5]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = icmp eq i8* %0, null		; <i1> [#uses=1]
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %2, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %0, i8** %3, align 4
	%4 = tail call i32 @strlen(i8* %0) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %4, 1		; <i32> [#uses=1]
	%5 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %5, i8** %6, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %3, align 4
	%7 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %7, align 4
	ret void
}

declare i8* @getusershell() nounwind

define weak void @softbound_endusershell() nounwind alwaysinline {
entry:
	tail call void @endusershell() nounwind
	ret void
}

declare void @endusershell() nounwind

define weak void @softbound__exit(i32 %status) nounwind alwaysinline {
entry:
	tail call void @_exit(i32 %status) noreturn nounwind
	unreachable
}

declare void @_exit(i32) noreturn nounwind

define weak i32 @softbound_wait3(i32* %status, i32 %options, %struct.rusage* %rusage, i8* %status_base, i8* %status_bound, i8* %rusage_base, i8* %rusage_bound) nounwind alwaysinline {
entry:
	%val3 = bitcast i32* %status to %struct.in_addr*		; <%struct.in_addr*> [#uses=1]
	%0 = tail call i32 @wait3(%struct.in_addr* %val3, i32 %options, %struct.rusage* %rusage) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @wait3(%struct.in_addr*, i32, %struct.rusage*) nounwind

define weak i32 @softbound_recv(i32 %s, i8* %buf, i32 %len, i32 %flags, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @recv(i32 %s, i8* %buf, i32 %len, i32 %flags) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @recv(i32, i8*, i32, i32)

define weak i32 @softbound_htonl(i32 %hostlong) nounwind alwaysinline {
entry:
	%asmtmp = tail call i32 asm "rorw $$8, ${0:w};rorl $$16, $0;rorw $$8, ${0:w}", "=r,0,~{dirflag},~{fpsr},~{flags},~{cc}"(i32 %hostlong) nounwind		; <i32> [#uses=1]
	ret i32 %asmtmp
}

define weak zeroext i16 @softbound_htons(i16 zeroext %hostshort) nounwind alwaysinline {
entry:
	%asmtmp2 = tail call i16 @llvm.bswap.i16(i16 %hostshort)		; <i16> [#uses=1]
	ret i16 %asmtmp2
}

declare i16 @llvm.bswap.i16(i16) nounwind readnone

define weak zeroext i16 @softbound_ntohs(i16 zeroext %netshort) nounwind alwaysinline {
entry:
	%asmtmp2 = tail call i16 @llvm.bswap.i16(i16 %netshort)		; <i16> [#uses=1]
	ret i16 %asmtmp2
}

define weak i32 @softbound_accept(i32 %sockfd, %struct.sockaddr* %addr, i32* %addrlen, i8* %addr_base, i8* %addr_bound, i8* %addrlen_base, i8* %addrlen_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @accept(i32 %sockfd, %struct.sockaddr* noalias %addr, i32* noalias %addrlen) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @accept(i32, %struct.sockaddr* noalias, i32* noalias)

define weak i32 @softbound_waitpid(i32 %pid, i32* %status, i32 %options, i8* %status_base, i8* %status_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @waitpid(i32 %pid, i32* %status, i32 %options) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @waitpid(i32, i32*, i32)

define weak i32 @softbound_getpid() nounwind alwaysinline {
entry:
	%0 = tail call i32 @getpid() nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getpid() nounwind

define weak i32 @softbound_listen(i32 %sockfd, i32 %backlog) nounwind alwaysinline {
entry:
	%0 = tail call i32 @listen(i32 %sockfd, i32 %backlog) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @listen(i32, i32) nounwind

define weak void @softbound_closelog() nounwind alwaysinline {
entry:
	tail call void @closelog() nounwind
	ret void
}

declare void @closelog()

define weak i32 @softbound_setenv(i8* %name, i8* %value, i32 %overwrite, i8* %name_base, i8* %name_bound, i8* %value_base, i8* %value_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setenv(i8* %name, i8* %value, i32 %overwrite) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @setenv(i8*, i8*, i32) nounwind

define weak i32 @softbound_setuid(i32 %uid) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setuid(i32 %uid) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @setuid(i32) nounwind

define weak i32 @softbound_setgid(i32 %gid) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setgid(i32 %gid) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @setgid(i32) nounwind

define weak i32 @softbound_send(i32 %s, i8* %buf, i32 %len, i32 %flags, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @send(i32 %s, i8* %buf, i32 %len, i32 %flags) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @send(i32, i8*, i32, i32)

define weak void @softbound_openlog(i8* %ident, i32 %option, i32 %facility, i8* %ident_base, i8* %ident_bound) nounwind alwaysinline {
entry:
	tail call void @openlog(i8* %ident, i32 %option, i32 %facility) nounwind
	ret void
}

declare void @openlog(i8*, i32, i32)

define weak i32 @softbound_lseek(i32 %fildes, i32 %offset, i32 %whence) nounwind alwaysinline {
entry:
	%0 = tail call i32 @lseek(i32 %fildes, i32 %offset, i32 %whence) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @lseek(i32, i32, i32) nounwind

define weak i32 @softbound_write(i32 %fd, i8* %buf, i32 %count, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @write(i32 %fd, i8* %buf, i32 %count) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @write(i32, i8*, i32)

define weak i32 @softbound_read(i32 %fd, i8* %buf, i32 %count, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @read(i32 %fd, i8* %buf, i32 %count) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @read(i32, i8*, i32)

define weak i32 @softbound_open(i8* %pathname, i32 %flags, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 (i8*, i32, ...)* @open(i8* %pathname, i32 %flags) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @open(i8*, i32, ...)

define weak i32 @softbound_close(i32 %fd) nounwind alwaysinline {
entry:
	%0 = tail call i32 @close(i32 %fd) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @close(i32)

define weak i32 @softbound_unlink(i8* %pathname, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @unlink(i8* %pathname) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @unlink(i8*) nounwind

define weak i32 @softbound_connect(i32 %sockfd, %struct.sockaddr* %serv_addr, i32 %addrlen, i8* %serv_addr_base, i8* %serv_addr_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @connect(i32 %sockfd, %struct.sockaddr* %serv_addr, i32 %addrlen) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @connect(i32, %struct.sockaddr*, i32)

define weak i32 @softbound_bind(i32 %sockfd, %struct.sockaddr* %my_addr, i32 %addrlen, i8* %my_addr_base, i8* %my_addr_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @bind(i32 %sockfd, %struct.sockaddr* %my_addr, i32 %addrlen) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @bind(i32, %struct.sockaddr*, i32) nounwind

define weak i32 @softbound_socket(i32 %domain, i32 %type, i32 %protocol) nounwind alwaysinline {
entry:
	%0 = tail call i32 @socket(i32 %domain, i32 %type, i32 %protocol) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @socket(i32, i32, i32) nounwind

define weak void @softbound_inet_ntoa(%struct.PtrBaseBound* %ptrs, i32 %in.0) nounwind alwaysinline {
entry:
	%0 = tail call i8* @inet_ntoa(i32 %in.0) nounwind		; <i8*> [#uses=4]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = tail call i32 @strlen(i8* %0) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %3, 1		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i8* @inet_ntoa(i32) nounwind

define weak i32 @softbound_getsockname(i32 %s, %struct.sockaddr* %name, i32* %namelen, i8* %name_base, i8* %name_bound, i8* %namelen_base, i8* %namelen_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getsockname(i32 %s, %struct.sockaddr* noalias %name, i32* noalias %namelen) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getsockname(i32, %struct.sockaddr* noalias, i32* noalias) nounwind

define weak i32 @softbound_getpeername(i32 %s, %struct.sockaddr* %name, i32* %namelen, i8* %name_base, i8* %name_bound, i8* %namelen_base, i8* %namelen_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getpeername(i32 %s, %struct.sockaddr* noalias %name, i32* noalias %namelen) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getpeername(i32, %struct.sockaddr* noalias, i32* noalias) nounwind

define weak i32 @softbound_inet_addr(i8* %cp, i8* %cp_base, i8* %cp_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @inet_addr(i8* %cp) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @inet_addr(i8*) nounwind

define weak void @softbound_strerror(%struct.PtrBaseBound* %ptrs, i32 %errnum) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strerror(i32 %errnum) nounwind		; <i8*> [#uses=4]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = tail call i32 @strlen(i8* %0) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %3, 1		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i8* @strerror(i32) nounwind

define weak void @softbound___ctype_tolower_loc(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call i32** @__ctype_tolower_loc() nounwind readnone		; <i32**> [#uses=1]
	%1 = bitcast i32** %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 4		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i32** @__ctype_tolower_loc() nounwind readnone

define weak i32 @softbound_tolower(i32 %c) nounwind alwaysinline {
entry:
	%0 = tail call i32 @tolower(i32 %c) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @tolower(i32) nounwind readonly

define weak i32 @softbound_toupper(i32 %c) nounwind alwaysinline {
entry:
	%0 = tail call i32 @toupper(i32 %c) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32** @__ctype_toupper_loc() nounwind readnone

declare i32 @toupper(i32) nounwind readonly

define weak void @softbound___ctype_toupper_loc(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call i32** @__ctype_toupper_loc() nounwind readnone		; <i32**> [#uses=3]
	%1 = bitcast i32** %0 to i8*		; <i8*> [#uses=1]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=2]
	store i8* %1, i8** %2, align 4
	%3 = load i32** %0		; <i32*> [#uses=1]
	%4 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([50 x i8]* @.str9, i32 0, i32 0), i32** %0, i32* %3) nounwind		; <i32> [#uses=0]
	%5 = load i8** %2, align 4		; <i8*> [#uses=2]
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %5, i8** %6, align 4
	%7 = getelementptr i8* %5, i32 4		; <i8*> [#uses=1]
	%8 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %7, i8** %8, align 4
	ret void
}

define weak void @softbound___ctype_b_loc(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call i16** @__ctype_b_loc() nounwind readnone		; <i16**> [#uses=1]
	%1 = bitcast i16** %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 4		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

define weak void @softbound___errno_location(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call i32* @__errno_location() nounwind readnone		; <i32*> [#uses=1]
	%1 = bitcast i32* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 4		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i32* @__errno_location() nounwind readnone

define weak i32 @softbound_atexit(void ()* %function, i8* %function_base, i8* %function_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @atexit(void ()* %function) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @atexit(void ()*) nounwind

define weak i32 @softbound_chmod(i8* %path, i32 %mode, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @chmod(i8* %path, i32 %mode) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @chmod(i8*, i32) nounwind

define weak i32 @softbound_getopt_long(i32 %argc, i8** %argv, i8* %optstring, %struct.option* %longopts, i32* %longindex, i8* %argv_base, i8* %argv_bound, i8* %optstring_base, i8* %optstring_bound, i8* %longopts_base, i8* %longopts_bound, i8* %longindex_base, i8* %longindex_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getopt_long(i32 %argc, i8** %argv, i8* %optstring, %struct.option* %longopts, i32* %longindex) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getopt_long(i32, i8**, i8*, %struct.option*, i32*) nounwind

define weak i32 @softbound_getopt(i32 %argc, i8** %argv, i8* %optstring, i8* %argv_base, i8* %argv_bound, i8* %optstring_base, i8* %optstring_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getopt(i32 %argc, i8** %argv, i8* %optstring) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @getopt(i32, i8**, i8*) nounwind

define weak void @softbound_getenv(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @getenv(i8* %name) nounwind		; <i8*> [#uses=5]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = icmp eq i8* %0, null		; <i1> [#uses=1]
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %2, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %0, i8** %3, align 4
	%4 = tail call i32 @strlen(i8* %0) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %4, 1		; <i32> [#uses=1]
	%5 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %5, i8** %6, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %3, align 4
	%7 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %7, align 4
	ret void
}

declare i8* @getenv(i8*) nounwind

define weak void @softbound_setbuf(%struct.FILE* %stream, i8* %buf, i8* %stream_base, i8* %stream_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	tail call void @setbuf(%struct.FILE* noalias %stream, i8* noalias %buf) nounwind
	ret void
}

declare void @setbuf(%struct.FILE* noalias, i8* noalias) nounwind

define weak double @softbound_difftime(i32 %time1, i32 %time0) nounwind alwaysinline {
entry:
	%0 = tail call double @difftime(i32 %time1, i32 %time0) nounwind readnone		; <double> [#uses=1]
	ret double %0
}

declare double @difftime(i32, i32) nounwind readnone

define weak void @softbound_ctime(%struct.PtrBaseBound* %ptrs, i32* %timep, i8* %timep_base, i8* %timep_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @ctime(i32* %timep) nounwind		; <i8*> [#uses=4]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = tail call i32 @strlen(i8* %0) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %3, 1		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i8* @ctime(i32*) nounwind

define weak i32 @softbound_utime(i8* %filename, %struct.rlimit* %buf, i8* %filename_base, i8* %filename_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @utime(i8* %filename, %struct.rlimit* %buf) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @utime(i8*, %struct.rlimit*) nounwind

define weak i32 @softbound_lrand48() nounwind alwaysinline {
entry:
	%0 = tail call i32 @lrand48() nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @lrand48() nounwind

define weak void @softbound_free(i8* %ptr, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
	free i8* %ptr
	ret void
}

define weak double @softbound_drand48() nounwind alwaysinline {
entry:
	%0 = tail call double @drand48() nounwind		; <double> [#uses=1]
	ret double %0
}

declare double @drand48() nounwind

define weak i32 @softbound_time(i32* %t, i8* %t_base, i8* %t_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @time(i32* %t) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @time(i32*) nounwind

define weak void @softbound_localtime(%struct.PtrBaseBound* %ptrs, i32* %timep, i8* %timep_base, i8* %timep_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.tm* @localtime(i32* %timep) nounwind		; <%struct.tm*> [#uses=1]
	%1 = bitcast %struct.tm* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 44		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.tm* @localtime(i32*) nounwind

define weak void @softbound_gmtime(%struct.PtrBaseBound* %ptrs, i32* %timep, i8* %timep_base, i8* %timep_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.tm* @gmtime(i32* %timep) nounwind		; <%struct.tm*> [#uses=1]
	%1 = bitcast %struct.tm* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 44		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.tm* @gmtime(i32*) nounwind

define weak i32 @softbound_times(%struct.tms* %buf, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @times(%struct.tms* %buf) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @times(%struct.tms*) nounwind

define weak i32 @softbound_strcmp(i8* %s1, i8* %s2, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strcmp(i8* %s1, i8* %s2) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @strcmp(i8*, i8*) nounwind readonly

define weak i32 @softbound_atoi(i8* %ptr, i8* %base_ptr, i8* %bound_ptr) nounwind alwaysinline {
entry:
	%0 = icmp eq i8* %ptr, null		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%1 = tail call i32 @atoi(i8* %ptr) nounwind readonly		; <i32> [#uses=1]
	ret i32 %1
}

define weak void @softbound_puts(i8* %ptr, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @puts(i8* %ptr) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @puts(i8*)

define weak i32 @softbound_rand() nounwind alwaysinline {
entry:
	%0 = tail call i32 @rand() nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @rand() nounwind

define weak void @softbound_abort() nounwind alwaysinline {
entry:
	tail call void @abort() noreturn nounwind
	unreachable
}

define weak void @softbound_malloc(%struct.PtrBaseBound* %ptrs, i32 %size) nounwind alwaysinline {
entry:
	%0 = malloc i8, i32 %size		; <i8*> [#uses=3]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = getelementptr i8* %0, i32 %size		; <i8*> [#uses=1]
	%4 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %3, i8** %4, align 4
	ret void
}

define weak void @softbound_realloc(%struct.PtrBaseBound* %ptrs, i8* %ptr, i32 %size, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
	%0 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=2]
	store i8* %ptr, i8** %0, align 4
	%1 = tail call i8* @realloc(i8* %ptr, i32 %size) nounwind		; <i8*> [#uses=3]
	store i8* %1, i8** %0, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr i8* %1, i32 %size		; <i8*> [#uses=1]
	%4 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %3, i8** %4, align 4
	ret void
}

declare i8* @realloc(i8*, i32) nounwind

define weak void @softbound_calloc(%struct.PtrBaseBound* %ptrs, i32 %nmemb, i32 %size) nounwind alwaysinline {
entry:
	%0 = tail call i8* @calloc(i32 %nmemb, i32 %size) nounwind		; <i8*> [#uses=3]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = mul i32 %size, %nmemb		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %3		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i8* @calloc(i32, i32) nounwind

define weak void @softbound_exit(i32 %status) nounwind alwaysinline {
entry:
	tail call void @exit(i32 %status) noreturn nounwind
	unreachable
}

declare void @exit(i32) noreturn nounwind

define weak i32 @softbound_clock() nounwind alwaysinline {
entry:
	%0 = tail call i32 @clock() nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @clock() nounwind

define weak i32 @softbound_fclose(%struct.FILE* %fp, i8* %fp_base, i8* %fp_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fclose(%struct.FILE* %fp) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @fclose(%struct.FILE*)

define weak void @softbound_signal(%struct.PtrBaseBound* %ptrs, i32 %signum, void (i32)* %handler, void (i32)* %handler_base, void (i32)* %handler_bound) nounwind alwaysinline {
entry:
	%0 = tail call void (i32)* (i32, void (i32)*)* @signal(i32 %signum, void (i32)* %handler) nounwind		; <void (i32)*> [#uses=1]
	%1 = bitcast void (i32)* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %1, i8** %4, align 4
	ret void
}

declare void (i32)* @signal(i32, void (i32)*) nounwind

define weak i32 @softbound_gethostname(i8* %name, i32 %len, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @gethostname(i8* %name, i32 %len) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @gethostname(i8*, i32) nounwind

define weak i32 @softbound_sigaddset(%struct.fd_set* %set, i32 %signum, i8* %set_base, i8* %set_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @sigaddset(%struct.fd_set* %set, i32 %signum) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @sigaddset(%struct.fd_set*, i32) nounwind

define weak void @softbound_tzset() nounwind alwaysinline {
entry:
	tail call void @tzset() nounwind
	ret void
}

declare void @tzset() nounwind

define weak i32 @softbound_sigprocmask(i32 %how, %struct.fd_set* %set, %struct.fd_set* %oldset, i8* %set_base, i8* %set_bound, i8* %oldset_base, i8* %oldset_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @sigprocmask(i32 %how, %struct.fd_set* noalias %set, %struct.fd_set* noalias %oldset) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @sigprocmask(i32, %struct.fd_set* noalias, %struct.fd_set* noalias) nounwind

define weak i32 @softbound_sigfillset(%struct.fd_set* %set, i8* %set_base, i8* %set_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @sigfillset(%struct.fd_set* %set) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @sigfillset(%struct.fd_set*) nounwind

define weak i32 @softbound_daemon(i32 %nochdir, i32 %noclose) nounwind alwaysinline {
entry:
	%0 = tail call i32 @daemon(i32 %nochdir, i32 %noclose) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @daemon(i32, i32) nounwind

define weak i32 @softbound_seteuid(i32 %euid) nounwind alwaysinline {
entry:
	%0 = tail call i32 @seteuid(i32 %euid) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @seteuid(i32) nounwind

define weak i32 @softbound_initgroups(i8* %user, i32 %group, i8* %user_base, i8* %user_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @initgroups(i8* %user, i32 %group) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @initgroups(i8*, i32)

define weak i32 @softbound_setegid(i32 %egid) nounwind alwaysinline {
entry:
	%0 = tail call i32 @setegid(i32 %egid) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @setegid(i32) nounwind

define weak i32 @softbound_sigemptyset(%struct.fd_set* %set, i8* %set_base, i8* %set_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @sigemptyset(%struct.fd_set* %set) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @sigemptyset(%struct.fd_set*) nounwind

define weak i32 @softbound_memcmp(i8* %s1, i8* %s2, i32 %n, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @memcmp(i8* %s1, i8* %s2, i32 %n) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @memcmp(i8*, i8*, i32) nounwind readonly

define weak void @softbound_strstr(%struct.PtrBaseBound* %ptrs, i8* %haystack, i8* %needle, i8* %haystack_base, i8* %haystack_bound, i8* %needle_base, i8* %needle_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strstr(i8* %haystack, i8* %needle) nounwind readonly		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %haystack_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %haystack_bound, i8** %3, align 4
	ret void
}

declare i8* @strstr(i8*, i8*) nounwind readonly

define weak void @softbound_strncpy(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i32 %n, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strncpy(i8* %dest, i8* %src, i32 %n) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %dest_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %dest_bound, i8** %3, align 4
	ret void
}

declare i8* @strncpy(i8*, i8*, i32) nounwind

define weak void @softbound_strrchr(%struct.PtrBaseBound* %ptrs, i8* %s, i32 %c, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strrchr(i8* %s, i32 %c) nounwind readonly		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %s_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %s_bound, i8** %3, align 4
	ret void
}

declare i8* @strrchr(i8*, i32) nounwind readonly

define weak void @softbound_strcpy(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strlen(i8* %src) nounwind readonly		; <i32> [#uses=1]
	%1 = getelementptr i8* %dest, i32 %0		; <i8*> [#uses=2]
	%2 = icmp ult i8* %1, %dest_base		; <i1> [#uses=1]
	%3 = icmp ugt i8* %1, %dest_bound		; <i1> [#uses=1]
	%or.cond = or i1 %2, %3		; <i1> [#uses=1]
	br i1 %or.cond, label %bb1, label %bb2

bb1:		; preds = %entry
	tail call void @abort() noreturn nounwind
	unreachable

bb2:		; preds = %entry
	%4 = tail call i8* @strcpy(i8* noalias %dest, i8* noalias %src) nounwind		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %dest_base, i8** %6, align 4
	%7 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %dest_bound, i8** %7, align 4
	ret void
}

declare i8* @strcpy(i8*, i8*) nounwind

define weak void @softbound_strchr(%struct.PtrBaseBound* %ptrs, i8* %s, i32 %c, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strchr(i8* %s, i32 %c) nounwind readonly		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %s_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %s_bound, i8** %3, align 4
	ret void
}

declare i8* @strchr(i8*, i32) nounwind readonly

define weak void @softbound_strncat(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i32 %n, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strncat(i8* %dest, i8* %src, i32 %n) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %dest_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %dest_bound, i8** %3, align 4
	ret void
}

declare i8* @strncat(i8*, i8*, i32) nounwind

define weak void @softbound_strcat(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strcat(i8* noalias %dest, i8* noalias %src) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %dest_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %dest_bound, i8** %3, align 4
	ret void
}

declare i8* @strcat(i8*, i8*) nounwind

define weak i32 @softbound_strcspn(i8* %s, i8* %reject, i8* %s_base, i8* %s_bound, i8* %reject_base, i8* %reject_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strcspn(i8* %s, i8* %reject) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @strcspn(i8*, i8*) nounwind readonly

define weak i32 @softbound_strspn(i8* %s, i8* %accept, i8* %s_base, i8* %s_bound, i8* %accept_base, i8* %accept_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strspn(i8* %s, i8* %accept) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @strspn(i8*, i8*) nounwind readonly

define weak void @softbound_strdup(%struct.PtrBaseBound* %ptrs, i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @__strdup(i8* %s) nounwind		; <i8*> [#uses=3]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = tail call i32 @strlen(i8* %s) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %3, 1		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare i8* @__strdup(i8*) nounwind

define weak void @softbound___strdup(%struct.PtrBaseBound* %ptrs, i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @__strdup(i8* %s) nounwind		; <i8*> [#uses=3]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %2, align 4
	%3 = tail call i32 @strlen(i8* %s) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %3, 1		; <i32> [#uses=1]
	%4 = getelementptr i8* %0, i32 %.sum		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

define weak void @softbound_strtok(%struct.PtrBaseBound* %ptrs, i8* %str, i8* %delim, i8* %str_base, i8* %str_bound, i8* %delim_base, i8* %delim_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strtok(i8* noalias %str, i8* noalias %delim) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* null, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* inttoptr (i64 2147483647 to i8*), i8** %3, align 4
	ret void
}

declare i8* @strtok(i8* noalias, i8* noalias) nounwind

define weak void @softbound_perror(i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	tail call void @perror(i8* %s) nounwind
	ret void
}

declare void @perror(i8*)

define weak void @softbound_fgets(%struct.PtrBaseBound* %return_ptr, i8* %s, i32 %size, %struct.FILE* %stream, i8* %s_base, i8* %s_bound, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @fgets(i8* noalias %s, i32 %size, %struct.FILE* noalias %stream) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %s_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %s_bound, i8** %3, align 4
	ret void
}

declare i8* @fgets(i8* noalias, i32, %struct.FILE* noalias)

define weak void @softbound_gets(%struct.PtrBaseBound* %return_ptr, i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @gets(i8* %s) nounwind		; <i8*> [#uses=1]
	%1 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %s_base, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %s_bound, i8** %3, align 4
	ret void
}

declare i8* @gets(i8*)

define weak void @softbound_strpbrk(%struct.PtrBaseBound* %return_ptr, i8* %s, i8* %accept, i8* %s_base, i8* %s_bound, i8* %accept_base, i8* %accept_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strpbrk(i8* %s, i8* %accept) nounwind readonly		; <i8*> [#uses=2]
	%1 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = icmp eq i8* %0, null		; <i1> [#uses=1]
	%3 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %2, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %s_base, i8** %3, align 4
	%4 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %s_bound, i8** %4, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %3, align 4
	%5 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %5, align 4
	ret void
}

declare i8* @strpbrk(i8*, i8*) nounwind readonly

define weak void @softbound___strpbrk_c3(%struct.PtrBaseBound* %return_ptr, i8* %s, i8* %accept, i8* %s_base, i8* %s_bound, i8* %accept_base, i8* %accept_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @strpbrk(i8* %s, i8* %accept) nounwind readonly		; <i8*> [#uses=2]
	%1 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = icmp eq i8* %0, null		; <i1> [#uses=1]
	%3 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %2, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %s_base, i8** %3, align 4
	%4 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %s_bound, i8** %4, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %3, align 4
	%5 = getelementptr %struct.PtrBaseBound* %return_ptr, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %5, align 4
	ret void
}

define weak i32 @softbound_strncasecmp(i8* %s1, i8* %s2, i32 %n, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strncasecmp(i8* %s1, i8* %s2, i32 %n) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @strncasecmp(i8*, i8*, i32) nounwind readonly

define weak i32 @softbound_strcasecmp(i8* %s1, i8* %s2, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strcasecmp(i8* %s1, i8* %s2) nounwind readonly		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @strcasecmp(i8*, i8*) nounwind readonly

define weak void @softbound_memchr(%struct.PtrBaseBound* %ptrs, i8* %s, i32 %c, i32 %n, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
	%0 = tail call i8* @memchr(i8* %s, i32 %c, i32 %n) nounwind readonly		; <i8*> [#uses=2]
	%1 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %1, align 4
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=2]
	store i8* null, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=2]
	store i8* null, i8** %3, align 4
	%4 = icmp eq i8* %0, null		; <i1> [#uses=1]
	br i1 %4, label %return, label %bb

bb:		; preds = %entry
	store i8* %s_base, i8** %2, align 4
	store i8* %s_bound, i8** %3, align 4
	ret void

return:		; preds = %entry
	ret void
}

declare i8* @memchr(i8*, i32, i32) nounwind readonly

define weak i32 @softbound_chdir(i8* %path, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @chdir(i8* %path) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @chdir(i8*) nounwind

define weak i32 @softbound_isatty(i32 %desc) nounwind alwaysinline {
entry:
	%0 = tail call i32 @isatty(i32 %desc) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @isatty(i32) nounwind

define weak i32 @softbound_chown(i8* %path, i32 %owner, i32 %group, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @chown(i8* %path, i32 %owner, i32 %group) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @chown(i8*, i32, i32) nounwind

define weak void @softbound_getcwd(%struct.PtrBaseBound* %ptrs, i8* %buf, i32 %size, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
	%0 = icmp eq i8* %buf, null		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	%1 = tail call i32 @puts(i8* getelementptr ([53 x i8]* @.str110, i32 0, i32 0)) nounwind		; <i32> [#uses=0]
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%2 = tail call i8* @getcwd(i8* %buf, i32 %size) nounwind		; <i8*> [#uses=1]
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %2, i8** %3, align 4
	%4 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %buf_base, i8** %4, align 4
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %buf_bound, i8** %5, align 4
	ret void
}

declare i8* @getcwd(i8*, i32) nounwind

define weak i32 @softbound_sleep(i32 %seconds) nounwind alwaysinline {
entry:
	%0 = tail call i32 @sleep(i32 %seconds) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @sleep(i32)

define weak i32 @softbound_rename(i8* %old_path, i8* %new_path, i8* %oldpath_base, i8* %oldpath_bound, i8* %new_path_base, i8* %new_path_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @rename(i8* %old_path, i8* %new_path) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @rename(i8*, i8*) nounwind

define weak i32 @softbound_closedir(%struct.DIR* %dir, i8* %dir_base, i8* %dir_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @closedir(%struct.DIR* %dir) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @closedir(%struct.DIR*)

define weak void @softbound_opendir(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.DIR* @opendir(i8* %name) nounwind		; <%struct.DIR*> [#uses=1]
	%1 = bitcast %struct.DIR* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 1048576		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.DIR* @opendir(i8*)

define weak void @softbound_readdir(%struct.PtrBaseBound* %ptrs, %struct.DIR* %dir, i8* %dir_base, i8* %dir_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.dirent* @readdir(%struct.DIR* %dir) nounwind		; <%struct.dirent*> [#uses=1]
	%1 = bitcast %struct.dirent* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 268		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.dirent* @readdir(%struct.DIR*)

define weak void @softbound_rewind(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	tail call void @rewind(%struct.FILE* %stream) nounwind
	ret void
}

declare void @rewind(%struct.FILE*)

define weak i32 @softbound_pclose(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @pclose(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @pclose(%struct.FILE*)

define weak void @softbound_popen(%struct.PtrBaseBound* %ptrs, i8* %command, i8* %type, i8* %command_base, i8* %command_bound, i8* %type_base, i8* %type_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.FILE* @popen(i8* %command, i8* %type) nounwind		; <%struct.FILE*> [#uses=1]
	%1 = bitcast %struct.FILE* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 148		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.FILE* @popen(i8*, i8*)

define weak i32 @softbound_ftruncate(i32 %fd, i32 %length) nounwind alwaysinline {
entry:
	%0 = tail call i32 @ftruncate(i32 %fd, i32 %length) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @ftruncate(i32, i32) nounwind

define weak i32 @softbound_fseek(%struct.FILE* %stream, i32 %offset, i32 %whence, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fseek(%struct.FILE* %stream, i32 %offset, i32 %whence) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @fseek(%struct.FILE*, i32, i32)

define weak void @softbound_fdopen(%struct.PtrBaseBound* %ptrs, i32 %fildes, i8* %mode, i8* %mode_base, i8* %mode_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.FILE* @fdopen(i32 %fildes, i8* %mode) nounwind		; <%struct.FILE*> [#uses=1]
	%1 = bitcast %struct.FILE* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 148		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.FILE* @fdopen(i32, i8*) nounwind

define weak void @softbound_fopen(%struct.PtrBaseBound* %ptrs, i8* %path, i8* %mode, i8* %path_base, i8* %path_bound, i8* %mode_base, i8* %mode_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.FILE* @fopen(i8* noalias %path, i8* noalias %mode) nounwind		; <%struct.FILE*> [#uses=1]
	%1 = bitcast %struct.FILE* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 148		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.FILE* @fopen(i8* noalias, i8* noalias)

define weak i32 @softbound_fputs(i8* %s, %struct.FILE* %stream, i8* %s_base, i8* %s_bound, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fputs(i8* noalias %s, %struct.FILE* noalias %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @fputs(i8* noalias, %struct.FILE* noalias)

define weak i32 @softbound_fflush(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @fflush(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @fflush(%struct.FILE*)

define weak i32 @softbound_ftell(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @ftell(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @ftell(%struct.FILE*)

define weak i32 @softbound_ferror(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @ferror(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @ferror(%struct.FILE*) nounwind

define weak void @softbound_tmpfile(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call %struct.FILE* @tmpfile() nounwind		; <%struct.FILE*> [#uses=1]
	%1 = bitcast %struct.FILE* %0 to i8*		; <i8*> [#uses=3]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 148		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	ret void
}

declare %struct.FILE* @tmpfile()

define weak double @softbound_ldexp(double %x, i32 %exp) nounwind alwaysinline {
entry:
	%0 = tail call double @ldexp(double %x, i32 %exp) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @ldexp(double, i32) nounwind readonly

define weak double @softbound_exp(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @llvm.exp.f64(double %x)		; <double> [#uses=1]
	ret double %0
}

declare double @llvm.exp.f64(double) nounwind readonly

define weak x86_fp80 @softbound_cosl(x86_fp80 %x) nounwind alwaysinline {
entry:
	%0 = tail call x86_fp80 @cosl(x86_fp80 %x) nounwind readonly		; <x86_fp80> [#uses=1]
	ret x86_fp80 %0
}

declare x86_fp80 @cosl(x86_fp80) nounwind readonly

define weak float @softbound_cosf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @cosf(float %x) nounwind readonly		; <float> [#uses=1]
	ret float %0
}

declare float @cosf(float) nounwind readonly

define weak double @softbound_cos(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @cos(double %x) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @cos(double) nounwind readonly

define weak x86_fp80 @softbound_sinl(x86_fp80 %x) nounwind alwaysinline {
entry:
	%0 = tail call x86_fp80 @sinl(x86_fp80 %x) nounwind readonly		; <x86_fp80> [#uses=1]
	ret x86_fp80 %0
}

declare x86_fp80 @sinl(x86_fp80) nounwind readonly

define weak float @softbound_sinf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @sinf(float %x) nounwind readonly		; <float> [#uses=1]
	ret float %0
}

declare float @sinf(float) nounwind readonly

define weak double @softbound_sin(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @sin(double %x) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @sin(double) nounwind readonly

define weak double @softbound_log10(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @llvm.log10.f64(double %x)		; <double> [#uses=1]
	ret double %0
}

declare double @llvm.log10.f64(double) nounwind readonly

define weak x86_fp80 @softbound_tanl(x86_fp80 %x) nounwind alwaysinline {
entry:
	%0 = tail call x86_fp80 @tanl(x86_fp80 %x) nounwind readonly		; <x86_fp80> [#uses=1]
	ret x86_fp80 %0
}

declare x86_fp80 @tanl(x86_fp80) nounwind readonly

define weak float @softbound_tanf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @tanf(float %x) nounwind readonly		; <float> [#uses=1]
	ret float %0
}

declare float @tanf(float) nounwind readonly

define weak double @softbound_tan(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @tan(double %x) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @tan(double) nounwind readonly

define weak double @softbound_pow(double %x, double %y) nounwind alwaysinline {
entry:
	%0 = tail call double @llvm.pow.f64(double %x, double %y)		; <double> [#uses=1]
	ret double %0
}

declare double @llvm.pow.f64(double, double) nounwind readonly

define weak void @softbound_srand48(i32 %seed) nounwind alwaysinline {
entry:
	tail call void @srand48(i32 %seed) nounwind
	ret void
}

declare void @srand48(i32) nounwind

define weak void @softbound_srand(i32 %seed) nounwind alwaysinline {
entry:
	tail call void @srand(i32 %seed) nounwind
	ret void
}

declare void @srand(i32) nounwind

define weak double @softbound_sqrt(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @llvm.sqrt.f64(double %x)		; <double> [#uses=1]
	ret double %0
}

declare double @llvm.sqrt.f64(double) nounwind readonly

define weak double @softbound_floor(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @floor(double %x) nounwind readnone		; <double> [#uses=1]
	ret double %0
}

declare double @floor(double) nounwind readnone

define weak float @softbound_ceilf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @ceilf(float %x) nounwind readnone		; <float> [#uses=1]
	ret float %0
}

declare float @ceilf(float) nounwind readnone

define weak double @softbound_ceil(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @ceil(double %x) nounwind readnone		; <double> [#uses=1]
	ret double %0
}

declare double @ceil(double) nounwind readnone

define weak float @softbound_floorf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @floorf(float %x) nounwind readnone		; <float> [#uses=1]
	ret float %0
}

declare float @floorf(float) nounwind readnone

define weak double @softbound_exp2(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @llvm.exp2.f64(double %x)		; <double> [#uses=1]
	ret double %0
}

declare double @llvm.exp2.f64(double) nounwind readonly

define weak float @softbound_expf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @llvm.exp.f32(float %x)		; <float> [#uses=1]
	ret float %0
}

declare float @llvm.exp.f32(float) nounwind readonly

define weak float @softbound_sqrtf(float %x) nounwind alwaysinline {
entry:
	%0 = tail call float @llvm.sqrt.f32(float %x)		; <float> [#uses=1]
	ret float %0
}

declare float @llvm.sqrt.f32(float) nounwind readonly

define weak double @softbound_atan2(double %y, double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @atan2(double %y, double %x) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @atan2(double, double) nounwind readonly

define weak double @softbound_acos(double %x) nounwind alwaysinline {
entry:
	%0 = tail call double @acos(double %x) nounwind readonly		; <double> [#uses=1]
	ret double %0
}

declare double @acos(double) nounwind readonly

define weak i32 @softbound_remove(i8* %pathname, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @remove(i8* %pathname) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @remove(i8*) nounwind

define weak i32 @softbound_feof(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @feof(%struct.FILE* %stream) nounwind		; <i32> [#uses=1]
	ret i32 %0
}

declare i32 @feof(%struct.FILE*) nounwind

declare double @llvm.log.f64(double) nounwind readonly

declare i32 @strncmp(i8*, i8*, i32) nounwind readonly

declare i32 @fgetc(%struct.FILE*)

declare i32 @fputc(i32, %struct.FILE*)

declare i32 @rmdir(i8*) nounwind

declare i32 @chroot(i8*) nounwind

declare i32 @mkdir(i8*, i32) nounwind

declare i32 @umask(i32) nounwind

declare i32 @fread(i8* noalias, i32, i32, %struct.FILE* noalias)

declare void @qsort(i8*, i32, i32, i32 (i8*, i8*)*)

declare i32 @setrlimit(i32, %struct.rlimit*) nounwind

declare i32 @getrlimit(i32, %struct.rlimit*) nounwind

declare i32 @getuid() nounwind

declare i32 @mkstemp(i8*)

declare i32 @setreuid(i32, i32) nounwind

declare i32 @system(i8*)

define weak void @softbound_getttyent(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
	%0 = tail call %struct.ttyent* @getttyent() nounwind		; <%struct.ttyent*> [#uses=7]
	%1 = bitcast %struct.ttyent* %0 to i8*		; <i8*> [#uses=9]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 24		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	%6 = getelementptr %struct.ttyent* %0, i32 0, i32 0		; <i8**> [#uses=1]
	%7 = load i8** %6, align 4		; <i8*> [#uses=3]
	%8 = tail call i32 @strlen(i8* %7) nounwind readonly		; <i32> [#uses=1]
	%.sum4 = add i32 %8, 1		; <i32> [#uses=1]
	%9 = getelementptr i8* %7, i32 %.sum4		; <i8*> [#uses=1]
	%10 = ptrtoint %struct.ttyent* %0 to i32		; <i32> [#uses=1]
	%11 = lshr i32 %10, 2		; <i32> [#uses=1]
	%12 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next116, %bb8.i ]		; <i32> [#uses=3]
	%13 = add i32 %counter.0.i, %11		; <i32> [#uses=1]
	%14 = and i32 %13, 134217727		; <i32> [#uses=3]
	%15 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 2		; <i8**> [#uses=2]
	%16 = load i8** %15, align 4		; <i8*> [#uses=2]
	%17 = icmp eq i8* %16, %1		; <i1> [#uses=1]
	%18 = icmp eq i8* %16, null		; <i1> [#uses=1]
	%19 = or i1 %17, %18		; <i1> [#uses=1]
	br i1 %19, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%20 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %20, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next116 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%21 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 0		; <i8**> [#uses=1]
	store i8* %7, i8** %21, align 4
	%22 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 1		; <i8**> [#uses=1]
	store i8* %9, i8** %22, align 4
	store i8* %1, i8** %15, align 4
	%23 = getelementptr %struct.ttyent* %0, i32 0, i32 1		; <i8**> [#uses=1]
	%24 = load i8** %23, align 4		; <i8*> [#uses=3]
	%25 = tail call i32 @strlen(i8* %24) nounwind readonly		; <i32> [#uses=1]
	%.sum3 = add i32 %25, 1		; <i32> [#uses=1]
	%26 = getelementptr i8* %24, i32 %.sum3		; <i8*> [#uses=1]
	%27 = getelementptr i8* %1, i32 4		; <i8*> [#uses=3]
	%28 = ptrtoint i8* %27 to i32		; <i32> [#uses=1]
	%29 = lshr i32 %28, 2		; <i32> [#uses=1]
	%30 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i27

bb.i27:		; preds = %bb8.i31, %__hashStoreBaseBound.exit
	%counter.0.i26 = phi i32 [ 0, %__hashStoreBaseBound.exit ], [ %indvar.next111, %bb8.i31 ]		; <i32> [#uses=3]
	%31 = add i32 %counter.0.i26, %29		; <i32> [#uses=1]
	%32 = and i32 %31, 134217727		; <i32> [#uses=3]
	%33 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 2		; <i8**> [#uses=2]
	%34 = load i8** %33, align 4		; <i8*> [#uses=2]
	%35 = icmp eq i8* %34, %27		; <i1> [#uses=1]
	%36 = icmp eq i8* %34, null		; <i1> [#uses=1]
	%37 = or i1 %35, %36		; <i1> [#uses=1]
	br i1 %37, label %__hashStoreBaseBound.exit32, label %bb6.i28

bb6.i28:		; preds = %bb.i27
	%38 = icmp ugt i32 %counter.0.i26, 134217727		; <i1> [#uses=1]
	br i1 %38, label %bb7.i29, label %bb8.i31

bb7.i29:		; preds = %bb6.i28
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i31:		; preds = %bb6.i28
	%indvar.next111 = add i32 %counter.0.i26, 1		; <i32> [#uses=1]
	br label %bb.i27

__hashStoreBaseBound.exit32:		; preds = %bb.i27
	%39 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 0		; <i8**> [#uses=1]
	store i8* %24, i8** %39, align 4
	%40 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 1		; <i8**> [#uses=1]
	store i8* %26, i8** %40, align 4
	store i8* %27, i8** %33, align 4
	%41 = getelementptr %struct.ttyent* %0, i32 0, i32 2		; <i8**> [#uses=2]
	%42 = load i8** %41, align 4		; <i8*> [#uses=3]
	%43 = tail call i32 @strlen(i8* %42) nounwind readonly		; <i32> [#uses=1]
	%.sum2 = add i32 %43, 1		; <i32> [#uses=1]
	%44 = getelementptr i8* %42, i32 %.sum2		; <i8*> [#uses=1]
	%45 = getelementptr i8* %1, i32 8		; <i8*> [#uses=3]
	%46 = ptrtoint i8* %45 to i32		; <i32> [#uses=1]
	%47 = lshr i32 %46, 2		; <i32> [#uses=1]
	%48 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i20

bb.i20:		; preds = %bb8.i24, %__hashStoreBaseBound.exit32
	%counter.0.i19 = phi i32 [ 0, %__hashStoreBaseBound.exit32 ], [ %indvar.next106, %bb8.i24 ]		; <i32> [#uses=3]
	%49 = add i32 %counter.0.i19, %47		; <i32> [#uses=1]
	%50 = and i32 %49, 134217727		; <i32> [#uses=3]
	%51 = getelementptr %struct.PtrBaseBound* %48, i32 %50, i32 2		; <i8**> [#uses=2]
	%52 = load i8** %51, align 4		; <i8*> [#uses=2]
	%53 = icmp eq i8* %52, %45		; <i1> [#uses=1]
	%54 = icmp eq i8* %52, null		; <i1> [#uses=1]
	%55 = or i1 %53, %54		; <i1> [#uses=1]
	br i1 %55, label %__hashStoreBaseBound.exit25, label %bb6.i21

bb6.i21:		; preds = %bb.i20
	%56 = icmp ugt i32 %counter.0.i19, 134217727		; <i1> [#uses=1]
	br i1 %56, label %bb7.i22, label %bb8.i24

bb7.i22:		; preds = %bb6.i21
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i24:		; preds = %bb6.i21
	%indvar.next106 = add i32 %counter.0.i19, 1		; <i32> [#uses=1]
	br label %bb.i20

__hashStoreBaseBound.exit25:		; preds = %bb.i20
	%57 = getelementptr %struct.PtrBaseBound* %48, i32 %50, i32 0		; <i8**> [#uses=1]
	store i8* %42, i8** %57, align 4
	%58 = getelementptr %struct.PtrBaseBound* %48, i32 %50, i32 1		; <i8**> [#uses=1]
	store i8* %44, i8** %58, align 4
	store i8* %45, i8** %51, align 4
	%59 = getelementptr %struct.ttyent* %0, i32 0, i32 4		; <i8**> [#uses=1]
	%60 = load i8** %59, align 4		; <i8*> [#uses=2]
	%61 = load i8** %41, align 4		; <i8*> [#uses=1]
	%62 = tail call i32 @strlen(i8* %60) nounwind readonly		; <i32> [#uses=1]
	%.sum1 = add i32 %62, 1		; <i32> [#uses=1]
	%63 = getelementptr i8* %61, i32 %.sum1		; <i8*> [#uses=1]
	%64 = getelementptr i8* %1, i32 16		; <i8*> [#uses=3]
	%65 = ptrtoint i8* %64 to i32		; <i32> [#uses=1]
	%66 = lshr i32 %65, 2		; <i32> [#uses=1]
	%67 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i13

bb.i13:		; preds = %bb8.i17, %__hashStoreBaseBound.exit25
	%counter.0.i12 = phi i32 [ 0, %__hashStoreBaseBound.exit25 ], [ %indvar.next, %bb8.i17 ]		; <i32> [#uses=3]
	%68 = add i32 %counter.0.i12, %66		; <i32> [#uses=1]
	%69 = and i32 %68, 134217727		; <i32> [#uses=3]
	%70 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 2		; <i8**> [#uses=2]
	%71 = load i8** %70, align 4		; <i8*> [#uses=2]
	%72 = icmp eq i8* %71, %64		; <i1> [#uses=1]
	%73 = icmp eq i8* %71, null		; <i1> [#uses=1]
	%74 = or i1 %72, %73		; <i1> [#uses=1]
	br i1 %74, label %__hashStoreBaseBound.exit18, label %bb6.i14

bb6.i14:		; preds = %bb.i13
	%75 = icmp ugt i32 %counter.0.i12, 134217727		; <i1> [#uses=1]
	br i1 %75, label %bb7.i15, label %bb8.i17

bb7.i15:		; preds = %bb6.i14
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i17:		; preds = %bb6.i14
	%indvar.next = add i32 %counter.0.i12, 1		; <i32> [#uses=1]
	br label %bb.i13

__hashStoreBaseBound.exit18:		; preds = %bb.i13
	%76 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 0		; <i8**> [#uses=1]
	store i8* %60, i8** %76, align 4
	%77 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 1		; <i8**> [#uses=1]
	store i8* %63, i8** %77, align 4
	store i8* %64, i8** %70, align 4
	%78 = getelementptr %struct.ttyent* %0, i32 0, i32 5		; <i8**> [#uses=1]
	%79 = load i8** %78, align 4		; <i8*> [#uses=3]
	%80 = tail call i32 @strlen(i8* %79) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %80, 1		; <i32> [#uses=1]
	%81 = getelementptr i8* %79, i32 %.sum		; <i8*> [#uses=1]
	%82 = getelementptr i8* %1, i32 20		; <i8*> [#uses=3]
	%83 = ptrtoint i8* %82 to i32		; <i32> [#uses=1]
	%84 = lshr i32 %83, 2		; <i32> [#uses=1]
	%85 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i6

bb.i6:		; preds = %bb8.i10, %__hashStoreBaseBound.exit18
	%counter.0.i5 = phi i32 [ 0, %__hashStoreBaseBound.exit18 ], [ %indvar.next97, %bb8.i10 ]		; <i32> [#uses=3]
	%86 = add i32 %counter.0.i5, %84		; <i32> [#uses=1]
	%87 = and i32 %86, 134217727		; <i32> [#uses=3]
	%88 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 2		; <i8**> [#uses=2]
	%89 = load i8** %88, align 4		; <i8*> [#uses=2]
	%90 = icmp eq i8* %89, %82		; <i1> [#uses=1]
	%91 = icmp eq i8* %89, null		; <i1> [#uses=1]
	%92 = or i1 %90, %91		; <i1> [#uses=1]
	br i1 %92, label %__hashStoreBaseBound.exit11, label %bb6.i7

bb6.i7:		; preds = %bb.i6
	%93 = icmp ugt i32 %counter.0.i5, 134217727		; <i1> [#uses=1]
	br i1 %93, label %bb7.i8, label %bb8.i10

bb7.i8:		; preds = %bb6.i7
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i10:		; preds = %bb6.i7
	%indvar.next97 = add i32 %counter.0.i5, 1		; <i32> [#uses=1]
	br label %bb.i6

__hashStoreBaseBound.exit11:		; preds = %bb.i6
	%94 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 0		; <i8**> [#uses=1]
	store i8* %79, i8** %94, align 4
	%95 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 1		; <i8**> [#uses=1]
	store i8* %81, i8** %95, align 4
	store i8* %82, i8** %88, align 4
	ret void
}

declare %struct.ttyent* @getttyent() nounwind

define weak i32 @softbound_glob(i8* %pattern, i32 %flags, i32 (i8*, i32)* %errfunc, %struct.glob_t* %pglob, i8* %pattern_base, i8* %pattern_bound, i8* %errfunc_base, i8* %errfunc_bound, i8* %pglob_base, i8* %pglob_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @glob(i8* noalias %pattern, i32 %flags, i32 (i8*, i32)* %errfunc, %struct.glob_t* noalias %pglob) nounwind		; <i32> [#uses=1]
	%1 = getelementptr %struct.glob_t* %pglob, i32 0, i32 2		; <i32*> [#uses=1]
	%2 = load i32* %1, align 4		; <i32> [#uses=1]
	%3 = getelementptr %struct.glob_t* %pglob, i32 0, i32 1		; <i8***> [#uses=3]
	br label %bb1

bb:		; preds = %bb1
	%4 = tail call i32 @strlen(i8* %22) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %4, 1		; <i32> [#uses=1]
	%5 = getelementptr i8* %22, i32 %.sum		; <i8*> [#uses=1]
	%6 = bitcast i8** %21 to i8*		; <i8*> [#uses=2]
	%7 = ptrtoint i8** %21 to i32		; <i32> [#uses=1]
	%8 = lshr i32 %7, 2		; <i32> [#uses=1]
	%9 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb
	%counter.0.i = phi i32 [ 0, %bb ], [ %indvar.next, %bb8.i ]		; <i32> [#uses=3]
	%10 = add i32 %counter.0.i, %8		; <i32> [#uses=1]
	%11 = and i32 %10, 134217727		; <i32> [#uses=3]
	%12 = getelementptr %struct.PtrBaseBound* %9, i32 %11, i32 2		; <i8**> [#uses=2]
	%13 = load i8** %12, align 4		; <i8*> [#uses=2]
	%14 = icmp eq i8* %13, %6		; <i1> [#uses=1]
	%15 = icmp eq i8* %13, null		; <i1> [#uses=1]
	%16 = or i1 %14, %15		; <i1> [#uses=1]
	br i1 %16, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%17 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %17, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%18 = getelementptr %struct.PtrBaseBound* %9, i32 %11, i32 0		; <i8**> [#uses=1]
	store i8* %22, i8** %18, align 4
	%19 = getelementptr %struct.PtrBaseBound* %9, i32 %11, i32 1		; <i8**> [#uses=1]
	store i8* %5, i8** %19, align 4
	store i8* %6, i8** %12, align 4
	%indvar.next58 = add i32 %indvar, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %__hashStoreBaseBound.exit, %entry
	%indvar = phi i32 [ 0, %entry ], [ %indvar.next58, %__hashStoreBaseBound.exit ]		; <i32> [#uses=2]
	%i.0 = add i32 %indvar, %2		; <i32> [#uses=2]
	%20 = load i8*** %3, align 4		; <i8**> [#uses=3]
	%21 = getelementptr i8** %20, i32 %i.0		; <i8**> [#uses=3]
	%22 = load i8** %21, align 4		; <i8*> [#uses=4]
	%23 = icmp eq i8* %22, null		; <i1> [#uses=1]
	br i1 %23, label %bb2, label %bb

bb2:		; preds = %bb1
	%.sum4 = add i32 %i.0, 1		; <i32> [#uses=1]
	%24 = getelementptr i8** %20, i32 %.sum4		; <i8**> [#uses=1]
	%25 = bitcast i8*** %3 to i8*		; <i8*> [#uses=2]
	%26 = bitcast i8** %20 to i8*		; <i8*> [#uses=1]
	%27 = bitcast i8** %24 to i8*		; <i8*> [#uses=1]
	%28 = ptrtoint i8*** %3 to i32		; <i32> [#uses=1]
	%29 = lshr i32 %28, 2		; <i32> [#uses=1]
	%30 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i6

bb.i6:		; preds = %bb8.i10, %bb2
	%counter.0.i5 = phi i32 [ 0, %bb2 ], [ %indvar.next48, %bb8.i10 ]		; <i32> [#uses=3]
	%31 = add i32 %counter.0.i5, %29		; <i32> [#uses=1]
	%32 = and i32 %31, 134217727		; <i32> [#uses=3]
	%33 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 2		; <i8**> [#uses=2]
	%34 = load i8** %33, align 4		; <i8*> [#uses=2]
	%35 = icmp eq i8* %34, %25		; <i1> [#uses=1]
	%36 = icmp eq i8* %34, null		; <i1> [#uses=1]
	%37 = or i1 %35, %36		; <i1> [#uses=1]
	br i1 %37, label %__hashStoreBaseBound.exit11, label %bb6.i7

bb6.i7:		; preds = %bb.i6
	%38 = icmp ugt i32 %counter.0.i5, 134217727		; <i1> [#uses=1]
	br i1 %38, label %bb7.i8, label %bb8.i10

bb7.i8:		; preds = %bb6.i7
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i10:		; preds = %bb6.i7
	%indvar.next48 = add i32 %counter.0.i5, 1		; <i32> [#uses=1]
	br label %bb.i6

__hashStoreBaseBound.exit11:		; preds = %bb.i6
	%39 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 0		; <i8**> [#uses=1]
	store i8* %26, i8** %39, align 4
	%40 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 1		; <i8**> [#uses=1]
	store i8* %27, i8** %40, align 4
	store i8* %25, i8** %33, align 4
	ret i32 %0
}

declare i32 @glob(i8* noalias, i32, i32 (i8*, i32)*, %struct.glob_t* noalias) nounwind

define weak void @softbound_getservbyname(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %proto, i8* %name_base, i8* %name_bound, i8* %proto_base, i8* %proto_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.servent* @getservbyname(i8* %name, i8* %proto) nounwind		; <%struct.servent*> [#uses=5]
	%1 = bitcast %struct.servent* %0 to i8*		; <i8*> [#uses=7]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 16		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	%6 = getelementptr %struct.servent* %0, i32 0, i32 0		; <i8**> [#uses=1]
	%7 = load i8** %6, align 4		; <i8*> [#uses=3]
	%8 = tail call i32 @strlen(i8* %7) nounwind readonly		; <i32> [#uses=1]
	%.sum5 = add i32 %8, 1		; <i32> [#uses=1]
	%9 = getelementptr i8* %7, i32 %.sum5		; <i8*> [#uses=1]
	%10 = ptrtoint %struct.servent* %0 to i32		; <i32> [#uses=1]
	%11 = lshr i32 %10, 2		; <i32> [#uses=1]
	%12 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next106, %bb8.i ]		; <i32> [#uses=3]
	%13 = add i32 %counter.0.i, %11		; <i32> [#uses=1]
	%14 = and i32 %13, 134217727		; <i32> [#uses=3]
	%15 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 2		; <i8**> [#uses=2]
	%16 = load i8** %15, align 4		; <i8*> [#uses=2]
	%17 = icmp eq i8* %16, %1		; <i1> [#uses=1]
	%18 = icmp eq i8* %16, null		; <i1> [#uses=1]
	%19 = or i1 %17, %18		; <i1> [#uses=1]
	br i1 %19, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%20 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %20, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next106 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%21 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 0		; <i8**> [#uses=1]
	store i8* %7, i8** %21, align 4
	%22 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 1		; <i8**> [#uses=1]
	store i8* %9, i8** %22, align 4
	store i8* %1, i8** %15, align 4
	%23 = getelementptr %struct.servent* %0, i32 0, i32 1		; <i8***> [#uses=2]
	%24 = load i8*** %23, align 4		; <i8**> [#uses=1]
	%25 = icmp eq i8** %24, null		; <i1> [#uses=1]
	br i1 %25, label %bb3, label %bb1

bb:		; preds = %bb1
	%26 = tail call i32 @strlen(i8* %44) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %26, 1		; <i32> [#uses=1]
	%27 = getelementptr i8* %44, i32 %.sum		; <i8*> [#uses=1]
	%28 = bitcast i8** %43 to i8*		; <i8*> [#uses=2]
	%29 = ptrtoint i8** %43 to i32		; <i32> [#uses=1]
	%30 = lshr i32 %29, 2		; <i32> [#uses=1]
	%31 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i21

bb.i21:		; preds = %bb8.i25, %bb
	%counter.0.i20 = phi i32 [ 0, %bb ], [ %indvar.next, %bb8.i25 ]		; <i32> [#uses=3]
	%32 = add i32 %counter.0.i20, %30		; <i32> [#uses=1]
	%33 = and i32 %32, 134217727		; <i32> [#uses=3]
	%34 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 2		; <i8**> [#uses=2]
	%35 = load i8** %34, align 4		; <i8*> [#uses=2]
	%36 = icmp eq i8* %35, %28		; <i1> [#uses=1]
	%37 = icmp eq i8* %35, null		; <i1> [#uses=1]
	%38 = or i1 %36, %37		; <i1> [#uses=1]
	br i1 %38, label %__hashStoreBaseBound.exit26, label %bb6.i22

bb6.i22:		; preds = %bb.i21
	%39 = icmp ugt i32 %counter.0.i20, 134217727		; <i1> [#uses=1]
	br i1 %39, label %bb7.i23, label %bb8.i25

bb7.i23:		; preds = %bb6.i22
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i25:		; preds = %bb6.i22
	%indvar.next = add i32 %counter.0.i20, 1		; <i32> [#uses=1]
	br label %bb.i21

__hashStoreBaseBound.exit26:		; preds = %bb.i21
	%40 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 0		; <i8**> [#uses=1]
	store i8* %44, i8** %40, align 4
	%41 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 1		; <i8**> [#uses=1]
	store i8* %27, i8** %41, align 4
	store i8* %28, i8** %34, align 4
	%indvar.next96 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %__hashStoreBaseBound.exit26, %__hashStoreBaseBound.exit
	%i.0 = phi i32 [ %indvar.next96, %__hashStoreBaseBound.exit26 ], [ 0, %__hashStoreBaseBound.exit ]		; <i32> [#uses=3]
	%42 = load i8*** %23, align 4		; <i8**> [#uses=3]
	%43 = getelementptr i8** %42, i32 %i.0		; <i8**> [#uses=3]
	%44 = load i8** %43, align 4		; <i8*> [#uses=4]
	%45 = icmp eq i8* %44, null		; <i1> [#uses=1]
	br i1 %45, label %bb2, label %bb

bb2:		; preds = %bb1
	%46 = add i32 %i.0, 1		; <i32> [#uses=1]
	%47 = getelementptr i8** %42, i32 %46		; <i8**> [#uses=1]
	%48 = getelementptr i8* %1, i32 4		; <i8*> [#uses=3]
	%49 = bitcast i8** %42 to i8*		; <i8*> [#uses=1]
	%50 = bitcast i8** %47 to i8*		; <i8*> [#uses=1]
	%51 = ptrtoint i8* %48 to i32		; <i32> [#uses=1]
	%52 = lshr i32 %51, 2		; <i32> [#uses=1]
	%53 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i14

bb.i14:		; preds = %bb8.i18, %bb2
	%counter.0.i13 = phi i32 [ 0, %bb2 ], [ %indvar.next88, %bb8.i18 ]		; <i32> [#uses=3]
	%54 = add i32 %counter.0.i13, %52		; <i32> [#uses=1]
	%55 = and i32 %54, 134217727		; <i32> [#uses=3]
	%56 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 2		; <i8**> [#uses=2]
	%57 = load i8** %56, align 4		; <i8*> [#uses=2]
	%58 = icmp eq i8* %57, %48		; <i1> [#uses=1]
	%59 = icmp eq i8* %57, null		; <i1> [#uses=1]
	%60 = or i1 %58, %59		; <i1> [#uses=1]
	br i1 %60, label %__hashStoreBaseBound.exit19, label %bb6.i15

bb6.i15:		; preds = %bb.i14
	%61 = icmp ugt i32 %counter.0.i13, 134217727		; <i1> [#uses=1]
	br i1 %61, label %bb7.i16, label %bb8.i18

bb7.i16:		; preds = %bb6.i15
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i18:		; preds = %bb6.i15
	%indvar.next88 = add i32 %counter.0.i13, 1		; <i32> [#uses=1]
	br label %bb.i14

__hashStoreBaseBound.exit19:		; preds = %bb.i14
	%62 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 0		; <i8**> [#uses=1]
	store i8* %49, i8** %62, align 4
	%63 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 1		; <i8**> [#uses=1]
	store i8* %50, i8** %63, align 4
	store i8* %48, i8** %56, align 4
	br label %bb3

bb3:		; preds = %__hashStoreBaseBound.exit19, %__hashStoreBaseBound.exit
	%64 = getelementptr %struct.servent* %0, i32 0, i32 3		; <i8**> [#uses=1]
	%65 = load i8** %64, align 4		; <i8*> [#uses=3]
	%66 = tail call i32 @strlen(i8* %65) nounwind readonly		; <i32> [#uses=1]
	%.sum4 = add i32 %66, 1		; <i32> [#uses=1]
	%67 = getelementptr i8* %65, i32 %.sum4		; <i8*> [#uses=1]
	%68 = getelementptr i8* %1, i32 12		; <i8*> [#uses=3]
	%69 = ptrtoint i8* %68 to i32		; <i32> [#uses=1]
	%70 = lshr i32 %69, 2		; <i32> [#uses=1]
	%71 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i7

bb.i7:		; preds = %bb8.i11, %bb3
	%counter.0.i6 = phi i32 [ 0, %bb3 ], [ %indvar.next101, %bb8.i11 ]		; <i32> [#uses=3]
	%72 = add i32 %counter.0.i6, %70		; <i32> [#uses=1]
	%73 = and i32 %72, 134217727		; <i32> [#uses=3]
	%74 = getelementptr %struct.PtrBaseBound* %71, i32 %73, i32 2		; <i8**> [#uses=2]
	%75 = load i8** %74, align 4		; <i8*> [#uses=2]
	%76 = icmp eq i8* %75, %68		; <i1> [#uses=1]
	%77 = icmp eq i8* %75, null		; <i1> [#uses=1]
	%78 = or i1 %76, %77		; <i1> [#uses=1]
	br i1 %78, label %__hashStoreBaseBound.exit12, label %bb6.i8

bb6.i8:		; preds = %bb.i7
	%79 = icmp ugt i32 %counter.0.i6, 134217727		; <i1> [#uses=1]
	br i1 %79, label %bb7.i9, label %bb8.i11

bb7.i9:		; preds = %bb6.i8
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i11:		; preds = %bb6.i8
	%indvar.next101 = add i32 %counter.0.i6, 1		; <i32> [#uses=1]
	br label %bb.i7

__hashStoreBaseBound.exit12:		; preds = %bb.i7
	%80 = getelementptr %struct.PtrBaseBound* %71, i32 %73, i32 0		; <i8**> [#uses=1]
	store i8* %65, i8** %80, align 4
	%81 = getelementptr %struct.PtrBaseBound* %71, i32 %73, i32 1		; <i8**> [#uses=1]
	store i8* %67, i8** %81, align 4
	store i8* %68, i8** %74, align 4
	ret void
}

declare %struct.servent* @getservbyname(i8*, i8*)

define weak i32 @softbound_getaddrinfo(i8* %node, i8* %service, %struct.addrinfo* %hints, %struct.addrinfo** %res, i8* %node_base, i8* %node_bound, i8* %service_base, i8* %service_bound, i8* %hints_base, i8* %hints_bound, i8* %res_base, i8* %res_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @getaddrinfo(i8* noalias %node, i8* noalias %service, %struct.addrinfo* noalias %hints, %struct.addrinfo** noalias %res) nounwind		; <i32> [#uses=1]
	%1 = load %struct.addrinfo** %res, align 4		; <%struct.addrinfo*> [#uses=2]
	%2 = bitcast %struct.addrinfo* %1 to i8*		; <i8*> [#uses=2]
	%3 = getelementptr i8* %2, i32 32		; <i8*> [#uses=1]
	%4 = bitcast %struct.addrinfo** %res to i8*		; <i8*> [#uses=2]
	%5 = ptrtoint %struct.addrinfo** %res to i32		; <i32> [#uses=1]
	%6 = lshr i32 %5, 2		; <i32> [#uses=1]
	%7 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next92, %bb8.i ]		; <i32> [#uses=3]
	%8 = add i32 %counter.0.i, %6		; <i32> [#uses=1]
	%9 = and i32 %8, 134217727		; <i32> [#uses=3]
	%10 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 2		; <i8**> [#uses=2]
	%11 = load i8** %10, align 4		; <i8*> [#uses=2]
	%12 = icmp eq i8* %11, %4		; <i1> [#uses=1]
	%13 = icmp eq i8* %11, null		; <i1> [#uses=1]
	%14 = or i1 %12, %13		; <i1> [#uses=1]
	br i1 %14, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%15 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %15, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next92 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%16 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 0		; <i8**> [#uses=1]
	store i8* %2, i8** %16, align 4
	%17 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 1		; <i8**> [#uses=1]
	store i8* %3, i8** %17, align 4
	store i8* %4, i8** %10, align 4
	br label %bb3

bb:		; preds = %bb3
	%18 = getelementptr %struct.addrinfo* %temp.0, i32 0, i32 5		; <%struct.sockaddr**> [#uses=3]
	%19 = load %struct.sockaddr** %18, align 4		; <%struct.sockaddr*> [#uses=1]
	%20 = bitcast %struct.sockaddr* %19 to i8*		; <i8*> [#uses=2]
	%21 = getelementptr i8* %20, i32 16		; <i8*> [#uses=1]
	%22 = bitcast %struct.sockaddr** %18 to i8*		; <i8*> [#uses=2]
	%23 = ptrtoint %struct.sockaddr** %18 to i32		; <i32> [#uses=1]
	%24 = lshr i32 %23, 2		; <i32> [#uses=1]
	%25 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i21

bb.i21:		; preds = %bb8.i25, %bb
	%counter.0.i20 = phi i32 [ 0, %bb ], [ %indvar.next78, %bb8.i25 ]		; <i32> [#uses=3]
	%26 = add i32 %counter.0.i20, %24		; <i32> [#uses=1]
	%27 = and i32 %26, 134217727		; <i32> [#uses=3]
	%28 = getelementptr %struct.PtrBaseBound* %25, i32 %27, i32 2		; <i8**> [#uses=2]
	%29 = load i8** %28, align 4		; <i8*> [#uses=2]
	%30 = icmp eq i8* %29, %22		; <i1> [#uses=1]
	%31 = icmp eq i8* %29, null		; <i1> [#uses=1]
	%32 = or i1 %30, %31		; <i1> [#uses=1]
	br i1 %32, label %__hashStoreBaseBound.exit26, label %bb6.i22

bb6.i22:		; preds = %bb.i21
	%33 = icmp ugt i32 %counter.0.i20, 134217727		; <i1> [#uses=1]
	br i1 %33, label %bb7.i23, label %bb8.i25

bb7.i23:		; preds = %bb6.i22
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i25:		; preds = %bb6.i22
	%indvar.next78 = add i32 %counter.0.i20, 1		; <i32> [#uses=1]
	br label %bb.i21

__hashStoreBaseBound.exit26:		; preds = %bb.i21
	%34 = getelementptr %struct.PtrBaseBound* %25, i32 %27, i32 0		; <i8**> [#uses=1]
	store i8* %20, i8** %34, align 4
	%35 = getelementptr %struct.PtrBaseBound* %25, i32 %27, i32 1		; <i8**> [#uses=1]
	store i8* %21, i8** %35, align 4
	store i8* %22, i8** %28, align 4
	%36 = getelementptr %struct.addrinfo* %temp.0, i32 0, i32 6		; <i8**> [#uses=3]
	%37 = load i8** %36, align 4		; <i8*> [#uses=3]
	%38 = tail call i32 @strlen(i8* %37) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %38, 1		; <i32> [#uses=1]
	%39 = getelementptr i8* %37, i32 %.sum		; <i8*> [#uses=1]
	%40 = bitcast i8** %36 to i8*		; <i8*> [#uses=2]
	%41 = ptrtoint i8** %36 to i32		; <i32> [#uses=1]
	%42 = lshr i32 %41, 2		; <i32> [#uses=1]
	%43 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i14

bb.i14:		; preds = %bb8.i18, %__hashStoreBaseBound.exit26
	%counter.0.i13 = phi i32 [ 0, %__hashStoreBaseBound.exit26 ], [ %indvar.next, %bb8.i18 ]		; <i32> [#uses=3]
	%44 = add i32 %counter.0.i13, %42		; <i32> [#uses=1]
	%45 = and i32 %44, 134217727		; <i32> [#uses=3]
	%46 = getelementptr %struct.PtrBaseBound* %43, i32 %45, i32 2		; <i8**> [#uses=2]
	%47 = load i8** %46, align 4		; <i8*> [#uses=2]
	%48 = icmp eq i8* %47, %40		; <i1> [#uses=1]
	%49 = icmp eq i8* %47, null		; <i1> [#uses=1]
	%50 = or i1 %48, %49		; <i1> [#uses=1]
	br i1 %50, label %__hashStoreBaseBound.exit19, label %bb6.i15

bb6.i15:		; preds = %bb.i14
	%51 = icmp ugt i32 %counter.0.i13, 134217727		; <i1> [#uses=1]
	br i1 %51, label %bb7.i16, label %bb8.i18

bb7.i16:		; preds = %bb6.i15
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i18:		; preds = %bb6.i15
	%indvar.next = add i32 %counter.0.i13, 1		; <i32> [#uses=1]
	br label %bb.i14

__hashStoreBaseBound.exit19:		; preds = %bb.i14
	%52 = getelementptr %struct.PtrBaseBound* %43, i32 %45, i32 0		; <i8**> [#uses=1]
	store i8* %37, i8** %52, align 4
	%53 = getelementptr %struct.PtrBaseBound* %43, i32 %45, i32 1		; <i8**> [#uses=1]
	store i8* %39, i8** %53, align 4
	store i8* %40, i8** %46, align 4
	%54 = getelementptr %struct.addrinfo* %temp.0, i32 0, i32 7		; <%struct.addrinfo**> [#uses=4]
	%55 = load %struct.addrinfo** %54, align 4		; <%struct.addrinfo*> [#uses=2]
	%56 = icmp eq %struct.addrinfo* %55, null		; <i1> [#uses=1]
	br i1 %56, label %bb2, label %bb1

bb1:		; preds = %__hashStoreBaseBound.exit19
	%57 = bitcast %struct.addrinfo* %55 to i8*		; <i8*> [#uses=2]
	%58 = getelementptr i8* %57, i32 32		; <i8*> [#uses=1]
	%59 = bitcast %struct.addrinfo** %54 to i8*		; <i8*> [#uses=2]
	%60 = ptrtoint %struct.addrinfo** %54 to i32		; <i32> [#uses=1]
	%61 = lshr i32 %60, 2		; <i32> [#uses=1]
	%62 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i7

bb.i7:		; preds = %bb8.i11, %bb1
	%counter.0.i6 = phi i32 [ 0, %bb1 ], [ %indvar.next87, %bb8.i11 ]		; <i32> [#uses=3]
	%63 = add i32 %counter.0.i6, %61		; <i32> [#uses=1]
	%64 = and i32 %63, 134217727		; <i32> [#uses=3]
	%65 = getelementptr %struct.PtrBaseBound* %62, i32 %64, i32 2		; <i8**> [#uses=2]
	%66 = load i8** %65, align 4		; <i8*> [#uses=2]
	%67 = icmp eq i8* %66, %59		; <i1> [#uses=1]
	%68 = icmp eq i8* %66, null		; <i1> [#uses=1]
	%69 = or i1 %67, %68		; <i1> [#uses=1]
	br i1 %69, label %__hashStoreBaseBound.exit12, label %bb6.i8

bb6.i8:		; preds = %bb.i7
	%70 = icmp ugt i32 %counter.0.i6, 134217727		; <i1> [#uses=1]
	br i1 %70, label %bb7.i9, label %bb8.i11

bb7.i9:		; preds = %bb6.i8
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i11:		; preds = %bb6.i8
	%indvar.next87 = add i32 %counter.0.i6, 1		; <i32> [#uses=1]
	br label %bb.i7

__hashStoreBaseBound.exit12:		; preds = %bb.i7
	%71 = getelementptr %struct.PtrBaseBound* %62, i32 %64, i32 0		; <i8**> [#uses=1]
	store i8* %57, i8** %71, align 4
	%72 = getelementptr %struct.PtrBaseBound* %62, i32 %64, i32 1		; <i8**> [#uses=1]
	store i8* %58, i8** %72, align 4
	store i8* %59, i8** %65, align 4
	br label %bb2

bb2:		; preds = %__hashStoreBaseBound.exit12, %__hashStoreBaseBound.exit19
	%73 = load %struct.addrinfo** %54, align 4		; <%struct.addrinfo*> [#uses=1]
	br label %bb3

bb3:		; preds = %bb2, %__hashStoreBaseBound.exit
	%temp.0 = phi %struct.addrinfo* [ %1, %__hashStoreBaseBound.exit ], [ %73, %bb2 ]		; <%struct.addrinfo*> [#uses=4]
	%74 = icmp eq %struct.addrinfo* %temp.0, null		; <i1> [#uses=1]
	br i1 %74, label %bb4, label %bb

bb4:		; preds = %bb3
	ret i32 %0
}

declare i32 @getaddrinfo(i8* noalias, i8* noalias, %struct.addrinfo* noalias, %struct.addrinfo** noalias)

define weak void @softbound_gethostbyname(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.hostent* @gethostbyname(i8* %name) nounwind		; <%struct.hostent*> [#uses=5]
	%1 = bitcast %struct.hostent* %0 to i8*		; <i8*> [#uses=7]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 20		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	%6 = getelementptr %struct.hostent* %0, i32 0, i32 0		; <i8**> [#uses=1]
	%7 = load i8** %6, align 4		; <i8*> [#uses=3]
	%8 = tail call i32 @strlen(i8* %7) nounwind readonly		; <i32> [#uses=1]
	%9 = getelementptr i8* %7, i32 %8		; <i8*> [#uses=1]
	%10 = ptrtoint %struct.hostent* %0 to i32		; <i32> [#uses=1]
	%11 = lshr i32 %10, 2		; <i32> [#uses=1]
	%12 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next147, %bb8.i ]		; <i32> [#uses=3]
	%13 = add i32 %counter.0.i, %11		; <i32> [#uses=1]
	%14 = and i32 %13, 134217727		; <i32> [#uses=3]
	%15 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 2		; <i8**> [#uses=2]
	%16 = load i8** %15, align 4		; <i8*> [#uses=2]
	%17 = icmp eq i8* %16, %1		; <i1> [#uses=1]
	%18 = icmp eq i8* %16, null		; <i1> [#uses=1]
	%19 = or i1 %17, %18		; <i1> [#uses=1]
	br i1 %19, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%20 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %20, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next147 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%21 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 0		; <i8**> [#uses=1]
	store i8* %7, i8** %21, align 4
	%22 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 1		; <i8**> [#uses=1]
	store i8* %9, i8** %22, align 4
	store i8* %1, i8** %15, align 4
	%23 = getelementptr %struct.hostent* %0, i32 0, i32 1		; <i8***> [#uses=2]
	%24 = load i8*** %23, align 4		; <i8**> [#uses=1]
	%25 = icmp eq i8** %24, null		; <i1> [#uses=1]
	br i1 %25, label %bb3, label %bb1

bb:		; preds = %bb1
	%26 = tail call i32 @strlen(i8* %44) nounwind readonly		; <i32> [#uses=1]
	%27 = getelementptr i8* %44, i32 %26		; <i8*> [#uses=1]
	%28 = bitcast i8** %43 to i8*		; <i8*> [#uses=2]
	%29 = ptrtoint i8** %43 to i32		; <i32> [#uses=1]
	%30 = lshr i32 %29, 2		; <i32> [#uses=1]
	%31 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i30

bb.i30:		; preds = %bb8.i34, %bb
	%counter.0.i29 = phi i32 [ 0, %bb ], [ %indvar.next, %bb8.i34 ]		; <i32> [#uses=3]
	%32 = add i32 %counter.0.i29, %30		; <i32> [#uses=1]
	%33 = and i32 %32, 134217727		; <i32> [#uses=3]
	%34 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 2		; <i8**> [#uses=2]
	%35 = load i8** %34, align 4		; <i8*> [#uses=2]
	%36 = icmp eq i8* %35, %28		; <i1> [#uses=1]
	%37 = icmp eq i8* %35, null		; <i1> [#uses=1]
	%38 = or i1 %36, %37		; <i1> [#uses=1]
	br i1 %38, label %__hashStoreBaseBound.exit35, label %bb6.i31

bb6.i31:		; preds = %bb.i30
	%39 = icmp ugt i32 %counter.0.i29, 134217727		; <i1> [#uses=1]
	br i1 %39, label %bb7.i32, label %bb8.i34

bb7.i32:		; preds = %bb6.i31
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i34:		; preds = %bb6.i31
	%indvar.next = add i32 %counter.0.i29, 1		; <i32> [#uses=1]
	br label %bb.i30

__hashStoreBaseBound.exit35:		; preds = %bb.i30
	%40 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 0		; <i8**> [#uses=1]
	store i8* %44, i8** %40, align 4
	%41 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 1		; <i8**> [#uses=1]
	store i8* %27, i8** %41, align 4
	store i8* %28, i8** %34, align 4
	%indvar.next128 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %__hashStoreBaseBound.exit35, %__hashStoreBaseBound.exit
	%i.0 = phi i32 [ %indvar.next128, %__hashStoreBaseBound.exit35 ], [ 0, %__hashStoreBaseBound.exit ]		; <i32> [#uses=3]
	%42 = load i8*** %23, align 4		; <i8**> [#uses=3]
	%43 = getelementptr i8** %42, i32 %i.0		; <i8**> [#uses=3]
	%44 = load i8** %43, align 4		; <i8*> [#uses=4]
	%45 = icmp eq i8* %44, null		; <i1> [#uses=1]
	br i1 %45, label %bb2, label %bb

bb2:		; preds = %bb1
	%46 = add i32 %i.0, 1		; <i32> [#uses=1]
	%47 = getelementptr i8** %42, i32 %46		; <i8**> [#uses=1]
	%48 = getelementptr i8* %1, i32 4		; <i8*> [#uses=3]
	%49 = bitcast i8** %42 to i8*		; <i8*> [#uses=1]
	%50 = bitcast i8** %47 to i8*		; <i8*> [#uses=1]
	%51 = ptrtoint i8* %48 to i32		; <i32> [#uses=1]
	%52 = lshr i32 %51, 2		; <i32> [#uses=1]
	%53 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i23

bb.i23:		; preds = %bb8.i27, %bb2
	%counter.0.i22 = phi i32 [ 0, %bb2 ], [ %indvar.next120, %bb8.i27 ]		; <i32> [#uses=3]
	%54 = add i32 %counter.0.i22, %52		; <i32> [#uses=1]
	%55 = and i32 %54, 134217727		; <i32> [#uses=3]
	%56 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 2		; <i8**> [#uses=2]
	%57 = load i8** %56, align 4		; <i8*> [#uses=2]
	%58 = icmp eq i8* %57, %48		; <i1> [#uses=1]
	%59 = icmp eq i8* %57, null		; <i1> [#uses=1]
	%60 = or i1 %58, %59		; <i1> [#uses=1]
	br i1 %60, label %__hashStoreBaseBound.exit28, label %bb6.i24

bb6.i24:		; preds = %bb.i23
	%61 = icmp ugt i32 %counter.0.i22, 134217727		; <i1> [#uses=1]
	br i1 %61, label %bb7.i25, label %bb8.i27

bb7.i25:		; preds = %bb6.i24
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i27:		; preds = %bb6.i24
	%indvar.next120 = add i32 %counter.0.i22, 1		; <i32> [#uses=1]
	br label %bb.i23

__hashStoreBaseBound.exit28:		; preds = %bb.i23
	%62 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 0		; <i8**> [#uses=1]
	store i8* %49, i8** %62, align 4
	%63 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 1		; <i8**> [#uses=1]
	store i8* %50, i8** %63, align 4
	store i8* %48, i8** %56, align 4
	br label %bb3

bb3:		; preds = %__hashStoreBaseBound.exit28, %__hashStoreBaseBound.exit
	%64 = getelementptr %struct.hostent* %0, i32 0, i32 4		; <i8***> [#uses=2]
	%65 = load i8*** %64, align 4		; <i8**> [#uses=1]
	%66 = icmp eq i8** %65, null		; <i1> [#uses=1]
	br i1 %66, label %return, label %bb5

bb4:		; preds = %bb5
	%67 = tail call i32 @strlen(i8* %85) nounwind readonly		; <i32> [#uses=1]
	%68 = getelementptr i8* %85, i32 %67		; <i8*> [#uses=1]
	%69 = bitcast i8** %84 to i8*		; <i8*> [#uses=2]
	%70 = ptrtoint i8** %84 to i32		; <i32> [#uses=1]
	%71 = lshr i32 %70, 2		; <i32> [#uses=1]
	%72 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i16

bb.i16:		; preds = %bb8.i20, %bb4
	%counter.0.i15 = phi i32 [ 0, %bb4 ], [ %indvar.next138, %bb8.i20 ]		; <i32> [#uses=3]
	%73 = add i32 %counter.0.i15, %71		; <i32> [#uses=1]
	%74 = and i32 %73, 134217727		; <i32> [#uses=3]
	%75 = getelementptr %struct.PtrBaseBound* %72, i32 %74, i32 2		; <i8**> [#uses=2]
	%76 = load i8** %75, align 4		; <i8*> [#uses=2]
	%77 = icmp eq i8* %76, %69		; <i1> [#uses=1]
	%78 = icmp eq i8* %76, null		; <i1> [#uses=1]
	%79 = or i1 %77, %78		; <i1> [#uses=1]
	br i1 %79, label %__hashStoreBaseBound.exit21, label %bb6.i17

bb6.i17:		; preds = %bb.i16
	%80 = icmp ugt i32 %counter.0.i15, 134217727		; <i1> [#uses=1]
	br i1 %80, label %bb7.i18, label %bb8.i20

bb7.i18:		; preds = %bb6.i17
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i20:		; preds = %bb6.i17
	%indvar.next138 = add i32 %counter.0.i15, 1		; <i32> [#uses=1]
	br label %bb.i16

__hashStoreBaseBound.exit21:		; preds = %bb.i16
	%81 = getelementptr %struct.PtrBaseBound* %72, i32 %74, i32 0		; <i8**> [#uses=1]
	store i8* %85, i8** %81, align 4
	%82 = getelementptr %struct.PtrBaseBound* %72, i32 %74, i32 1		; <i8**> [#uses=1]
	store i8* %68, i8** %82, align 4
	store i8* %69, i8** %75, align 4
	%indvar.next142 = add i32 %i.1, 1		; <i32> [#uses=1]
	br label %bb5

bb5:		; preds = %__hashStoreBaseBound.exit21, %bb3
	%i.1 = phi i32 [ %indvar.next142, %__hashStoreBaseBound.exit21 ], [ 0, %bb3 ]		; <i32> [#uses=3]
	%83 = load i8*** %64, align 4		; <i8**> [#uses=3]
	%84 = getelementptr i8** %83, i32 %i.1		; <i8**> [#uses=3]
	%85 = load i8** %84, align 4		; <i8*> [#uses=4]
	%86 = icmp eq i8* %85, null		; <i1> [#uses=1]
	br i1 %86, label %bb6, label %bb4

bb6:		; preds = %bb5
	%87 = add i32 %i.1, 1		; <i32> [#uses=1]
	%88 = getelementptr i8** %83, i32 %87		; <i8**> [#uses=1]
	%89 = getelementptr i8* %1, i32 16		; <i8*> [#uses=3]
	%90 = bitcast i8** %83 to i8*		; <i8*> [#uses=1]
	%91 = bitcast i8** %88 to i8*		; <i8*> [#uses=1]
	%92 = ptrtoint i8* %89 to i32		; <i32> [#uses=1]
	%93 = lshr i32 %92, 2		; <i32> [#uses=1]
	%94 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i9

bb.i9:		; preds = %bb8.i13, %bb6
	%counter.0.i8 = phi i32 [ 0, %bb6 ], [ %indvar.next133, %bb8.i13 ]		; <i32> [#uses=3]
	%95 = add i32 %counter.0.i8, %93		; <i32> [#uses=1]
	%96 = and i32 %95, 134217727		; <i32> [#uses=3]
	%97 = getelementptr %struct.PtrBaseBound* %94, i32 %96, i32 2		; <i8**> [#uses=2]
	%98 = load i8** %97, align 4		; <i8*> [#uses=2]
	%99 = icmp eq i8* %98, %89		; <i1> [#uses=1]
	%100 = icmp eq i8* %98, null		; <i1> [#uses=1]
	%101 = or i1 %99, %100		; <i1> [#uses=1]
	br i1 %101, label %__hashStoreBaseBound.exit14, label %bb6.i10

bb6.i10:		; preds = %bb.i9
	%102 = icmp ugt i32 %counter.0.i8, 134217727		; <i1> [#uses=1]
	br i1 %102, label %bb7.i11, label %bb8.i13

bb7.i11:		; preds = %bb6.i10
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i13:		; preds = %bb6.i10
	%indvar.next133 = add i32 %counter.0.i8, 1		; <i32> [#uses=1]
	br label %bb.i9

__hashStoreBaseBound.exit14:		; preds = %bb.i9
	%103 = getelementptr %struct.PtrBaseBound* %94, i32 %96, i32 0		; <i8**> [#uses=1]
	store i8* %90, i8** %103, align 4
	%104 = getelementptr %struct.PtrBaseBound* %94, i32 %96, i32 1		; <i8**> [#uses=1]
	store i8* %91, i8** %104, align 4
	store i8* %89, i8** %97, align 4
	ret void

return:		; preds = %bb3
	ret void
}

declare %struct.hostent* @gethostbyname(i8*)

define weak void @softbound_gethostbyaddr(%struct.PtrBaseBound* %ptrs, i8* %addr, i32 %len, i32 %type, i8* %addr_base, i8* %addr_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.hostent* @gethostbyaddr(i8* %addr, i32 %len, i32 %type) nounwind		; <%struct.hostent*> [#uses=5]
	%1 = bitcast %struct.hostent* %0 to i8*		; <i8*> [#uses=7]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %1, i8** %3, align 4
	%4 = getelementptr i8* %1, i32 20		; <i8*> [#uses=1]
	%5 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %4, i8** %5, align 4
	%6 = getelementptr %struct.hostent* %0, i32 0, i32 0		; <i8**> [#uses=1]
	%7 = load i8** %6, align 4		; <i8*> [#uses=3]
	%8 = tail call i32 @strlen(i8* %7) nounwind readonly		; <i32> [#uses=1]
	%9 = getelementptr i8* %7, i32 %8		; <i8*> [#uses=1]
	%10 = ptrtoint %struct.hostent* %0 to i32		; <i32> [#uses=1]
	%11 = lshr i32 %10, 2		; <i32> [#uses=1]
	%12 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next147, %bb8.i ]		; <i32> [#uses=3]
	%13 = add i32 %counter.0.i, %11		; <i32> [#uses=1]
	%14 = and i32 %13, 134217727		; <i32> [#uses=3]
	%15 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 2		; <i8**> [#uses=2]
	%16 = load i8** %15, align 4		; <i8*> [#uses=2]
	%17 = icmp eq i8* %16, %1		; <i1> [#uses=1]
	%18 = icmp eq i8* %16, null		; <i1> [#uses=1]
	%19 = or i1 %17, %18		; <i1> [#uses=1]
	br i1 %19, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%20 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %20, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next147 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%21 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 0		; <i8**> [#uses=1]
	store i8* %7, i8** %21, align 4
	%22 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 1		; <i8**> [#uses=1]
	store i8* %9, i8** %22, align 4
	store i8* %1, i8** %15, align 4
	%23 = getelementptr %struct.hostent* %0, i32 0, i32 1		; <i8***> [#uses=2]
	%24 = load i8*** %23, align 4		; <i8**> [#uses=1]
	%25 = icmp eq i8** %24, null		; <i1> [#uses=1]
	br i1 %25, label %bb3, label %bb1

bb:		; preds = %bb1
	%26 = tail call i32 @strlen(i8* %44) nounwind readonly		; <i32> [#uses=1]
	%27 = getelementptr i8* %44, i32 %26		; <i8*> [#uses=1]
	%28 = bitcast i8** %43 to i8*		; <i8*> [#uses=2]
	%29 = ptrtoint i8** %43 to i32		; <i32> [#uses=1]
	%30 = lshr i32 %29, 2		; <i32> [#uses=1]
	%31 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i30

bb.i30:		; preds = %bb8.i34, %bb
	%counter.0.i29 = phi i32 [ 0, %bb ], [ %indvar.next, %bb8.i34 ]		; <i32> [#uses=3]
	%32 = add i32 %counter.0.i29, %30		; <i32> [#uses=1]
	%33 = and i32 %32, 134217727		; <i32> [#uses=3]
	%34 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 2		; <i8**> [#uses=2]
	%35 = load i8** %34, align 4		; <i8*> [#uses=2]
	%36 = icmp eq i8* %35, %28		; <i1> [#uses=1]
	%37 = icmp eq i8* %35, null		; <i1> [#uses=1]
	%38 = or i1 %36, %37		; <i1> [#uses=1]
	br i1 %38, label %__hashStoreBaseBound.exit35, label %bb6.i31

bb6.i31:		; preds = %bb.i30
	%39 = icmp ugt i32 %counter.0.i29, 134217727		; <i1> [#uses=1]
	br i1 %39, label %bb7.i32, label %bb8.i34

bb7.i32:		; preds = %bb6.i31
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i34:		; preds = %bb6.i31
	%indvar.next = add i32 %counter.0.i29, 1		; <i32> [#uses=1]
	br label %bb.i30

__hashStoreBaseBound.exit35:		; preds = %bb.i30
	%40 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 0		; <i8**> [#uses=1]
	store i8* %44, i8** %40, align 4
	%41 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 1		; <i8**> [#uses=1]
	store i8* %27, i8** %41, align 4
	store i8* %28, i8** %34, align 4
	%indvar.next128 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %__hashStoreBaseBound.exit35, %__hashStoreBaseBound.exit
	%i.0 = phi i32 [ %indvar.next128, %__hashStoreBaseBound.exit35 ], [ 0, %__hashStoreBaseBound.exit ]		; <i32> [#uses=3]
	%42 = load i8*** %23, align 4		; <i8**> [#uses=3]
	%43 = getelementptr i8** %42, i32 %i.0		; <i8**> [#uses=3]
	%44 = load i8** %43, align 4		; <i8*> [#uses=4]
	%45 = icmp eq i8* %44, null		; <i1> [#uses=1]
	br i1 %45, label %bb2, label %bb

bb2:		; preds = %bb1
	%46 = add i32 %i.0, 1		; <i32> [#uses=1]
	%47 = getelementptr i8** %42, i32 %46		; <i8**> [#uses=1]
	%48 = getelementptr i8* %1, i32 4		; <i8*> [#uses=3]
	%49 = bitcast i8** %42 to i8*		; <i8*> [#uses=1]
	%50 = bitcast i8** %47 to i8*		; <i8*> [#uses=1]
	%51 = ptrtoint i8* %48 to i32		; <i32> [#uses=1]
	%52 = lshr i32 %51, 2		; <i32> [#uses=1]
	%53 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i23

bb.i23:		; preds = %bb8.i27, %bb2
	%counter.0.i22 = phi i32 [ 0, %bb2 ], [ %indvar.next120, %bb8.i27 ]		; <i32> [#uses=3]
	%54 = add i32 %counter.0.i22, %52		; <i32> [#uses=1]
	%55 = and i32 %54, 134217727		; <i32> [#uses=3]
	%56 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 2		; <i8**> [#uses=2]
	%57 = load i8** %56, align 4		; <i8*> [#uses=2]
	%58 = icmp eq i8* %57, %48		; <i1> [#uses=1]
	%59 = icmp eq i8* %57, null		; <i1> [#uses=1]
	%60 = or i1 %58, %59		; <i1> [#uses=1]
	br i1 %60, label %__hashStoreBaseBound.exit28, label %bb6.i24

bb6.i24:		; preds = %bb.i23
	%61 = icmp ugt i32 %counter.0.i22, 134217727		; <i1> [#uses=1]
	br i1 %61, label %bb7.i25, label %bb8.i27

bb7.i25:		; preds = %bb6.i24
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i27:		; preds = %bb6.i24
	%indvar.next120 = add i32 %counter.0.i22, 1		; <i32> [#uses=1]
	br label %bb.i23

__hashStoreBaseBound.exit28:		; preds = %bb.i23
	%62 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 0		; <i8**> [#uses=1]
	store i8* %49, i8** %62, align 4
	%63 = getelementptr %struct.PtrBaseBound* %53, i32 %55, i32 1		; <i8**> [#uses=1]
	store i8* %50, i8** %63, align 4
	store i8* %48, i8** %56, align 4
	br label %bb3

bb3:		; preds = %__hashStoreBaseBound.exit28, %__hashStoreBaseBound.exit
	%64 = getelementptr %struct.hostent* %0, i32 0, i32 4		; <i8***> [#uses=2]
	%65 = load i8*** %64, align 4		; <i8**> [#uses=1]
	%66 = icmp eq i8** %65, null		; <i1> [#uses=1]
	br i1 %66, label %return, label %bb5

bb4:		; preds = %bb5
	%67 = tail call i32 @strlen(i8* %85) nounwind readonly		; <i32> [#uses=1]
	%68 = getelementptr i8* %85, i32 %67		; <i8*> [#uses=1]
	%69 = bitcast i8** %84 to i8*		; <i8*> [#uses=2]
	%70 = ptrtoint i8** %84 to i32		; <i32> [#uses=1]
	%71 = lshr i32 %70, 2		; <i32> [#uses=1]
	%72 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i16

bb.i16:		; preds = %bb8.i20, %bb4
	%counter.0.i15 = phi i32 [ 0, %bb4 ], [ %indvar.next138, %bb8.i20 ]		; <i32> [#uses=3]
	%73 = add i32 %counter.0.i15, %71		; <i32> [#uses=1]
	%74 = and i32 %73, 134217727		; <i32> [#uses=3]
	%75 = getelementptr %struct.PtrBaseBound* %72, i32 %74, i32 2		; <i8**> [#uses=2]
	%76 = load i8** %75, align 4		; <i8*> [#uses=2]
	%77 = icmp eq i8* %76, %69		; <i1> [#uses=1]
	%78 = icmp eq i8* %76, null		; <i1> [#uses=1]
	%79 = or i1 %77, %78		; <i1> [#uses=1]
	br i1 %79, label %__hashStoreBaseBound.exit21, label %bb6.i17

bb6.i17:		; preds = %bb.i16
	%80 = icmp ugt i32 %counter.0.i15, 134217727		; <i1> [#uses=1]
	br i1 %80, label %bb7.i18, label %bb8.i20

bb7.i18:		; preds = %bb6.i17
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i20:		; preds = %bb6.i17
	%indvar.next138 = add i32 %counter.0.i15, 1		; <i32> [#uses=1]
	br label %bb.i16

__hashStoreBaseBound.exit21:		; preds = %bb.i16
	%81 = getelementptr %struct.PtrBaseBound* %72, i32 %74, i32 0		; <i8**> [#uses=1]
	store i8* %85, i8** %81, align 4
	%82 = getelementptr %struct.PtrBaseBound* %72, i32 %74, i32 1		; <i8**> [#uses=1]
	store i8* %68, i8** %82, align 4
	store i8* %69, i8** %75, align 4
	%indvar.next142 = add i32 %i.1, 1		; <i32> [#uses=1]
	br label %bb5

bb5:		; preds = %__hashStoreBaseBound.exit21, %bb3
	%i.1 = phi i32 [ %indvar.next142, %__hashStoreBaseBound.exit21 ], [ 0, %bb3 ]		; <i32> [#uses=3]
	%83 = load i8*** %64, align 4		; <i8**> [#uses=3]
	%84 = getelementptr i8** %83, i32 %i.1		; <i8**> [#uses=3]
	%85 = load i8** %84, align 4		; <i8*> [#uses=4]
	%86 = icmp eq i8* %85, null		; <i1> [#uses=1]
	br i1 %86, label %bb6, label %bb4

bb6:		; preds = %bb5
	%87 = add i32 %i.1, 1		; <i32> [#uses=1]
	%88 = getelementptr i8** %83, i32 %87		; <i8**> [#uses=1]
	%89 = getelementptr i8* %1, i32 16		; <i8*> [#uses=3]
	%90 = bitcast i8** %83 to i8*		; <i8*> [#uses=1]
	%91 = bitcast i8** %88 to i8*		; <i8*> [#uses=1]
	%92 = ptrtoint i8* %89 to i32		; <i32> [#uses=1]
	%93 = lshr i32 %92, 2		; <i32> [#uses=1]
	%94 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i9

bb.i9:		; preds = %bb8.i13, %bb6
	%counter.0.i8 = phi i32 [ 0, %bb6 ], [ %indvar.next133, %bb8.i13 ]		; <i32> [#uses=3]
	%95 = add i32 %counter.0.i8, %93		; <i32> [#uses=1]
	%96 = and i32 %95, 134217727		; <i32> [#uses=3]
	%97 = getelementptr %struct.PtrBaseBound* %94, i32 %96, i32 2		; <i8**> [#uses=2]
	%98 = load i8** %97, align 4		; <i8*> [#uses=2]
	%99 = icmp eq i8* %98, %89		; <i1> [#uses=1]
	%100 = icmp eq i8* %98, null		; <i1> [#uses=1]
	%101 = or i1 %99, %100		; <i1> [#uses=1]
	br i1 %101, label %__hashStoreBaseBound.exit14, label %bb6.i10

bb6.i10:		; preds = %bb.i9
	%102 = icmp ugt i32 %counter.0.i8, 134217727		; <i1> [#uses=1]
	br i1 %102, label %bb7.i11, label %bb8.i13

bb7.i11:		; preds = %bb6.i10
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i13:		; preds = %bb6.i10
	%indvar.next133 = add i32 %counter.0.i8, 1		; <i32> [#uses=1]
	br label %bb.i9

__hashStoreBaseBound.exit14:		; preds = %bb.i9
	%103 = getelementptr %struct.PtrBaseBound* %94, i32 %96, i32 0		; <i8**> [#uses=1]
	store i8* %90, i8** %103, align 4
	%104 = getelementptr %struct.PtrBaseBound* %94, i32 %96, i32 1		; <i8**> [#uses=1]
	store i8* %91, i8** %104, align 4
	store i8* %89, i8** %97, align 4
	ret void

return:		; preds = %bb3
	ret void
}

declare %struct.hostent* @gethostbyaddr(i8*, i32, i32)

define weak i32 @softbound_scandir(i8* %dir, %struct.dirent*** %namelist, i32 (%struct.dirent*)* %filter, i32 (i8*, i8*)* %compar, i8* %dir_base, i8* %dir_bound, i8* %namelist_base, i8* %namelist_bound, i8* %filter_base, i8* %filter_bound, i8* %compar_base, i8* %compar_bound) nounwind alwaysinline {
entry:
	%0 = bitcast i32 (i8*, i8*)* %compar to i32 (%struct.dirent**, %struct.dirent**)*		; <i32 (%struct.dirent**, %struct.dirent**)*> [#uses=1]
	%1 = tail call i32 @scandir(i8* noalias %dir, %struct.dirent*** noalias %namelist, i32 (%struct.dirent*)* %filter, i32 (%struct.dirent**, %struct.dirent**)* %0) nounwind		; <i32> [#uses=4]
	%2 = icmp eq %struct.dirent*** %namelist, null		; <i1> [#uses=1]
	br i1 %2, label %bb4, label %bb

bb:		; preds = %entry
	%3 = load %struct.dirent*** %namelist, align 4		; <%struct.dirent**> [#uses=5]
	%4 = icmp sgt i32 %1, 0		; <i1> [#uses=1]
	%5 = bitcast %struct.dirent** %3 to i8*		; <i8*> [#uses=3]
	%6 = ptrtoint %struct.dirent** %3 to i32		; <i32> [#uses=1]
	%7 = lshr i32 %6, 2		; <i32> [#uses=1]
	br i1 %4, label %bb2, label %bb3.split

bb.i:		; preds = %bb2, %bb8.i
	%counter.0.i = phi i32 [ 0, %bb2 ], [ %indvar.next, %bb8.i ]		; <i32> [#uses=3]
	%8 = add i32 %counter.0.i, %37		; <i32> [#uses=1]
	%9 = and i32 %8, 134217727		; <i32> [#uses=3]
	%10 = getelementptr %struct.PtrBaseBound* %38, i32 %9, i32 2		; <i8**> [#uses=2]
	%11 = load i8** %10, align 4		; <i8*> [#uses=2]
	%12 = icmp eq i8* %11, %35		; <i1> [#uses=1]
	%13 = icmp eq i8* %11, null		; <i1> [#uses=1]
	%14 = or i1 %12, %13		; <i1> [#uses=1]
	br i1 %14, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%15 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %15, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%16 = getelementptr %struct.PtrBaseBound* %38, i32 %9, i32 0		; <i8**> [#uses=1]
	store i8* %35, i8** %16, align 4
	%17 = getelementptr %struct.PtrBaseBound* %38, i32 %9, i32 1		; <i8**> [#uses=1]
	store i8* %34, i8** %17, align 4
	store i8* %35, i8** %10, align 4
	%18 = load %struct.dirent** %3, align 4		; <%struct.dirent*> [#uses=2]
	%19 = getelementptr %struct.dirent* %18, i32 268		; <%struct.dirent*> [#uses=1]
	%20 = bitcast %struct.dirent* %18 to i8*		; <i8*> [#uses=1]
	%21 = bitcast %struct.dirent* %19 to i8*		; <i8*> [#uses=1]
	%22 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i14

bb.i14:		; preds = %bb8.i18, %__hashStoreBaseBound.exit
	%counter.0.i13 = phi i32 [ 0, %__hashStoreBaseBound.exit ], [ %indvar.next67, %bb8.i18 ]		; <i32> [#uses=3]
	%23 = add i32 %counter.0.i13, %7		; <i32> [#uses=1]
	%24 = and i32 %23, 134217727		; <i32> [#uses=3]
	%25 = getelementptr %struct.PtrBaseBound* %22, i32 %24, i32 2		; <i8**> [#uses=2]
	%26 = load i8** %25, align 4		; <i8*> [#uses=2]
	%27 = icmp eq i8* %26, %5		; <i1> [#uses=1]
	%28 = icmp eq i8* %26, null		; <i1> [#uses=1]
	%29 = or i1 %27, %28		; <i1> [#uses=1]
	br i1 %29, label %__hashStoreBaseBound.exit19, label %bb6.i15

bb6.i15:		; preds = %bb.i14
	%30 = icmp ugt i32 %counter.0.i13, 134217727		; <i1> [#uses=1]
	br i1 %30, label %bb7.i16, label %bb8.i18

bb7.i16:		; preds = %bb6.i15
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i18:		; preds = %bb6.i15
	%indvar.next67 = add i32 %counter.0.i13, 1		; <i32> [#uses=1]
	br label %bb.i14

__hashStoreBaseBound.exit19:		; preds = %bb.i14
	%31 = getelementptr %struct.PtrBaseBound* %22, i32 %24, i32 0		; <i8**> [#uses=1]
	store i8* %20, i8** %31, align 4
	%32 = getelementptr %struct.PtrBaseBound* %22, i32 %24, i32 1		; <i8**> [#uses=1]
	store i8* %21, i8** %32, align 4
	store i8* %5, i8** %25, align 4
	br label %bb2

bb2:		; preds = %__hashStoreBaseBound.exit19, %bb
	%33 = load %struct.dirent** %3, align 4		; <%struct.dirent*> [#uses=2]
	%34 = getelementptr %struct.dirent* %33, i32 0, i32 4, i32 256		; <i8*> [#uses=1]
	%35 = getelementptr %struct.dirent* %33, i32 0, i32 4, i32 0		; <i8*> [#uses=4]
	%36 = ptrtoint i8* %35 to i32		; <i32> [#uses=1]
	%37 = lshr i32 %36, 2		; <i32> [#uses=1]
	%38 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb3.split:		; preds = %bb
	%39 = getelementptr %struct.dirent** %3, i32 %1		; <%struct.dirent**> [#uses=1]
	%40 = bitcast %struct.dirent*** %namelist to i8*		; <i8*> [#uses=2]
	%41 = bitcast %struct.dirent** %39 to i8*		; <i8*> [#uses=1]
	%42 = ptrtoint %struct.dirent*** %namelist to i32		; <i32> [#uses=1]
	%43 = lshr i32 %42, 2		; <i32> [#uses=1]
	%44 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i7

bb.i7:		; preds = %bb8.i11, %bb3.split
	%counter.0.i6 = phi i32 [ 0, %bb3.split ], [ %indvar.next58, %bb8.i11 ]		; <i32> [#uses=3]
	%45 = add i32 %counter.0.i6, %43		; <i32> [#uses=1]
	%46 = and i32 %45, 134217727		; <i32> [#uses=3]
	%47 = getelementptr %struct.PtrBaseBound* %44, i32 %46, i32 2		; <i8**> [#uses=2]
	%48 = load i8** %47, align 4		; <i8*> [#uses=2]
	%49 = icmp eq i8* %48, %40		; <i1> [#uses=1]
	%50 = icmp eq i8* %48, null		; <i1> [#uses=1]
	%51 = or i1 %49, %50		; <i1> [#uses=1]
	br i1 %51, label %__hashStoreBaseBound.exit12, label %bb6.i8

bb6.i8:		; preds = %bb.i7
	%52 = icmp ugt i32 %counter.0.i6, 134217727		; <i1> [#uses=1]
	br i1 %52, label %bb7.i9, label %bb8.i11

bb7.i9:		; preds = %bb6.i8
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i11:		; preds = %bb6.i8
	%indvar.next58 = add i32 %counter.0.i6, 1		; <i32> [#uses=1]
	br label %bb.i7

__hashStoreBaseBound.exit12:		; preds = %bb.i7
	%53 = getelementptr %struct.PtrBaseBound* %44, i32 %46, i32 0		; <i8**> [#uses=1]
	store i8* %5, i8** %53, align 4
	%54 = getelementptr %struct.PtrBaseBound* %44, i32 %46, i32 1		; <i8**> [#uses=1]
	store i8* %41, i8** %54, align 4
	store i8* %40, i8** %47, align 4
	ret i32 %1

bb4:		; preds = %entry
	ret i32 %1
}

declare i32 @scandir(i8* noalias, %struct.dirent*** noalias, i32 (%struct.dirent*)*, i32 (%struct.dirent**, %struct.dirent**)*)

define weak void @softbound_getpwnam(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
	%0 = tail call %struct.passwd* @getpwnam(i8* %name) nounwind		; <%struct.passwd*> [#uses=8]
	%1 = bitcast %struct.passwd* %0 to i8*		; <i8*> [#uses=9]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = icmp eq %struct.passwd* %0, null		; <i1> [#uses=1]
	%4 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %3, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %1, i8** %4, align 4
	%5 = getelementptr i8* %1, i32 28		; <i8*> [#uses=1]
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %5, i8** %6, align 4
	%7 = getelementptr %struct.passwd* %0, i32 0, i32 0		; <i8**> [#uses=1]
	%8 = load i8** %7, align 4		; <i8*> [#uses=3]
	%9 = tail call i32 @strlen(i8* %8) nounwind readonly		; <i32> [#uses=1]
	%.sum6 = add i32 %9, 1		; <i32> [#uses=1]
	%10 = getelementptr i8* %8, i32 %.sum6		; <i8*> [#uses=1]
	%11 = ptrtoint %struct.passwd* %0 to i32		; <i32> [#uses=1]
	%12 = lshr i32 %11, 2		; <i32> [#uses=1]
	%13 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb
	%counter.0.i = phi i32 [ 0, %bb ], [ %indvar.next118, %bb8.i ]		; <i32> [#uses=3]
	%14 = add i32 %counter.0.i, %12		; <i32> [#uses=1]
	%15 = and i32 %14, 134217727		; <i32> [#uses=3]
	%16 = getelementptr %struct.PtrBaseBound* %13, i32 %15, i32 2		; <i8**> [#uses=2]
	%17 = load i8** %16, align 4		; <i8*> [#uses=2]
	%18 = icmp eq i8* %17, %1		; <i1> [#uses=1]
	%19 = icmp eq i8* %17, null		; <i1> [#uses=1]
	%20 = or i1 %18, %19		; <i1> [#uses=1]
	br i1 %20, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%21 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %21, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next118 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%22 = getelementptr %struct.PtrBaseBound* %13, i32 %15, i32 0		; <i8**> [#uses=1]
	store i8* %8, i8** %22, align 4
	%23 = getelementptr %struct.PtrBaseBound* %13, i32 %15, i32 1		; <i8**> [#uses=1]
	store i8* %10, i8** %23, align 4
	store i8* %1, i8** %16, align 4
	%24 = getelementptr %struct.passwd* %0, i32 0, i32 1		; <i8**> [#uses=1]
	%25 = load i8** %24, align 4		; <i8*> [#uses=3]
	%26 = tail call i32 @strlen(i8* %25) nounwind readonly		; <i32> [#uses=1]
	%.sum5 = add i32 %26, 1		; <i32> [#uses=1]
	%27 = getelementptr i8* %25, i32 %.sum5		; <i8*> [#uses=1]
	%28 = getelementptr i8* %1, i32 4		; <i8*> [#uses=3]
	%29 = ptrtoint i8* %28 to i32		; <i32> [#uses=1]
	%30 = lshr i32 %29, 2		; <i32> [#uses=1]
	%31 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i29

bb.i29:		; preds = %bb8.i33, %__hashStoreBaseBound.exit
	%counter.0.i28 = phi i32 [ 0, %__hashStoreBaseBound.exit ], [ %indvar.next113, %bb8.i33 ]		; <i32> [#uses=3]
	%32 = add i32 %counter.0.i28, %30		; <i32> [#uses=1]
	%33 = and i32 %32, 134217727		; <i32> [#uses=3]
	%34 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 2		; <i8**> [#uses=2]
	%35 = load i8** %34, align 4		; <i8*> [#uses=2]
	%36 = icmp eq i8* %35, %28		; <i1> [#uses=1]
	%37 = icmp eq i8* %35, null		; <i1> [#uses=1]
	%38 = or i1 %36, %37		; <i1> [#uses=1]
	br i1 %38, label %__hashStoreBaseBound.exit34, label %bb6.i30

bb6.i30:		; preds = %bb.i29
	%39 = icmp ugt i32 %counter.0.i28, 134217727		; <i1> [#uses=1]
	br i1 %39, label %bb7.i31, label %bb8.i33

bb7.i31:		; preds = %bb6.i30
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i33:		; preds = %bb6.i30
	%indvar.next113 = add i32 %counter.0.i28, 1		; <i32> [#uses=1]
	br label %bb.i29

__hashStoreBaseBound.exit34:		; preds = %bb.i29
	%40 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 0		; <i8**> [#uses=1]
	store i8* %25, i8** %40, align 4
	%41 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 1		; <i8**> [#uses=1]
	store i8* %27, i8** %41, align 4
	store i8* %28, i8** %34, align 4
	%42 = getelementptr %struct.passwd* %0, i32 0, i32 4		; <i8**> [#uses=1]
	%43 = load i8** %42, align 4		; <i8*> [#uses=3]
	%44 = tail call i32 @strlen(i8* %43) nounwind readonly		; <i32> [#uses=1]
	%.sum4 = add i32 %44, 1		; <i32> [#uses=1]
	%45 = getelementptr i8* %43, i32 %.sum4		; <i8*> [#uses=1]
	%46 = getelementptr i8* %1, i32 16		; <i8*> [#uses=3]
	%47 = ptrtoint i8* %46 to i32		; <i32> [#uses=1]
	%48 = lshr i32 %47, 2		; <i32> [#uses=1]
	%49 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i22

bb.i22:		; preds = %bb8.i26, %__hashStoreBaseBound.exit34
	%counter.0.i21 = phi i32 [ 0, %__hashStoreBaseBound.exit34 ], [ %indvar.next108, %bb8.i26 ]		; <i32> [#uses=3]
	%50 = add i32 %counter.0.i21, %48		; <i32> [#uses=1]
	%51 = and i32 %50, 134217727		; <i32> [#uses=3]
	%52 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 2		; <i8**> [#uses=2]
	%53 = load i8** %52, align 4		; <i8*> [#uses=2]
	%54 = icmp eq i8* %53, %46		; <i1> [#uses=1]
	%55 = icmp eq i8* %53, null		; <i1> [#uses=1]
	%56 = or i1 %54, %55		; <i1> [#uses=1]
	br i1 %56, label %__hashStoreBaseBound.exit27, label %bb6.i23

bb6.i23:		; preds = %bb.i22
	%57 = icmp ugt i32 %counter.0.i21, 134217727		; <i1> [#uses=1]
	br i1 %57, label %bb7.i24, label %bb8.i26

bb7.i24:		; preds = %bb6.i23
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i26:		; preds = %bb6.i23
	%indvar.next108 = add i32 %counter.0.i21, 1		; <i32> [#uses=1]
	br label %bb.i22

__hashStoreBaseBound.exit27:		; preds = %bb.i22
	%58 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 0		; <i8**> [#uses=1]
	store i8* %43, i8** %58, align 4
	%59 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 1		; <i8**> [#uses=1]
	store i8* %45, i8** %59, align 4
	store i8* %46, i8** %52, align 4
	%60 = getelementptr %struct.passwd* %0, i32 0, i32 5		; <i8**> [#uses=1]
	%61 = load i8** %60, align 4		; <i8*> [#uses=3]
	%62 = tail call i32 @strlen(i8* %61) nounwind readonly		; <i32> [#uses=1]
	%.sum3 = add i32 %62, 1		; <i32> [#uses=1]
	%63 = getelementptr i8* %61, i32 %.sum3		; <i8*> [#uses=1]
	%64 = getelementptr i8* %1, i32 20		; <i8*> [#uses=3]
	%65 = ptrtoint i8* %64 to i32		; <i32> [#uses=1]
	%66 = lshr i32 %65, 2		; <i32> [#uses=1]
	%67 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i15

bb.i15:		; preds = %bb8.i19, %__hashStoreBaseBound.exit27
	%counter.0.i14 = phi i32 [ 0, %__hashStoreBaseBound.exit27 ], [ %indvar.next, %bb8.i19 ]		; <i32> [#uses=3]
	%68 = add i32 %counter.0.i14, %66		; <i32> [#uses=1]
	%69 = and i32 %68, 134217727		; <i32> [#uses=3]
	%70 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 2		; <i8**> [#uses=2]
	%71 = load i8** %70, align 4		; <i8*> [#uses=2]
	%72 = icmp eq i8* %71, %64		; <i1> [#uses=1]
	%73 = icmp eq i8* %71, null		; <i1> [#uses=1]
	%74 = or i1 %72, %73		; <i1> [#uses=1]
	br i1 %74, label %__hashStoreBaseBound.exit20, label %bb6.i16

bb6.i16:		; preds = %bb.i15
	%75 = icmp ugt i32 %counter.0.i14, 134217727		; <i1> [#uses=1]
	br i1 %75, label %bb7.i17, label %bb8.i19

bb7.i17:		; preds = %bb6.i16
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i19:		; preds = %bb6.i16
	%indvar.next = add i32 %counter.0.i14, 1		; <i32> [#uses=1]
	br label %bb.i15

__hashStoreBaseBound.exit20:		; preds = %bb.i15
	%76 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 0		; <i8**> [#uses=1]
	store i8* %61, i8** %76, align 4
	%77 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 1		; <i8**> [#uses=1]
	store i8* %63, i8** %77, align 4
	store i8* %64, i8** %70, align 4
	%78 = getelementptr %struct.passwd* %0, i32 0, i32 6		; <i8**> [#uses=1]
	%79 = load i8** %78, align 4		; <i8*> [#uses=3]
	%80 = tail call i32 @strlen(i8* %79) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %80, 1		; <i32> [#uses=1]
	%81 = getelementptr i8* %79, i32 %.sum		; <i8*> [#uses=1]
	%82 = getelementptr i8* %1, i32 24		; <i8*> [#uses=3]
	%83 = ptrtoint i8* %82 to i32		; <i32> [#uses=1]
	%84 = lshr i32 %83, 2		; <i32> [#uses=1]
	%85 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i8

bb.i8:		; preds = %bb8.i12, %__hashStoreBaseBound.exit20
	%counter.0.i7 = phi i32 [ 0, %__hashStoreBaseBound.exit20 ], [ %indvar.next99, %bb8.i12 ]		; <i32> [#uses=3]
	%86 = add i32 %counter.0.i7, %84		; <i32> [#uses=1]
	%87 = and i32 %86, 134217727		; <i32> [#uses=3]
	%88 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 2		; <i8**> [#uses=2]
	%89 = load i8** %88, align 4		; <i8*> [#uses=2]
	%90 = icmp eq i8* %89, %82		; <i1> [#uses=1]
	%91 = icmp eq i8* %89, null		; <i1> [#uses=1]
	%92 = or i1 %90, %91		; <i1> [#uses=1]
	br i1 %92, label %__hashStoreBaseBound.exit13, label %bb6.i9

bb6.i9:		; preds = %bb.i8
	%93 = icmp ugt i32 %counter.0.i7, 134217727		; <i1> [#uses=1]
	br i1 %93, label %bb7.i10, label %bb8.i12

bb7.i10:		; preds = %bb6.i9
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i12:		; preds = %bb6.i9
	%indvar.next99 = add i32 %counter.0.i7, 1		; <i32> [#uses=1]
	br label %bb.i8

__hashStoreBaseBound.exit13:		; preds = %bb.i8
	%94 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 0		; <i8**> [#uses=1]
	store i8* %79, i8** %94, align 4
	%95 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 1		; <i8**> [#uses=1]
	store i8* %81, i8** %95, align 4
	store i8* %82, i8** %88, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %4, align 4
	%96 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %96, align 4
	ret void
}

declare %struct.passwd* @getpwnam(i8*)

define weak void @softbound_getgrgid(%struct.PtrBaseBound* %ptrs, i32 %gid) nounwind alwaysinline {
entry:
	%0 = tail call %struct.group* @getgrgid(i32 %gid) nounwind		; <%struct.group*> [#uses=2]
	%1 = bitcast %struct.group* %0 to i8*		; <i8*> [#uses=1]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = icmp eq %struct.group* %0, null		; <i1> [#uses=1]
	br i1 %3, label %bb5, label %bb

bb:		; preds = %entry
	%4 = tail call %struct.group* @getgrgid(i32 %gid) nounwind		; <%struct.group*> [#uses=5]
	%5 = getelementptr %struct.group* %4, i32 0, i32 0		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=3]
	%7 = tail call i32 @strlen(i8* %6) nounwind readonly		; <i32> [#uses=1]
	%.sum8 = add i32 %7, 1		; <i32> [#uses=1]
	%8 = getelementptr i8* %6, i32 %.sum8		; <i8*> [#uses=1]
	%9 = bitcast %struct.group* %4 to i8*		; <i8*> [#uses=2]
	%10 = ptrtoint %struct.group* %4 to i32		; <i32> [#uses=1]
	%11 = lshr i32 %10, 2		; <i32> [#uses=1]
	%12 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb
	%counter.0.i = phi i32 [ 0, %bb ], [ %indvar.next101, %bb8.i ]		; <i32> [#uses=3]
	%13 = add i32 %counter.0.i, %11		; <i32> [#uses=1]
	%14 = and i32 %13, 134217727		; <i32> [#uses=3]
	%15 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 2		; <i8**> [#uses=2]
	%16 = load i8** %15, align 4		; <i8*> [#uses=2]
	%17 = icmp eq i8* %16, %9		; <i1> [#uses=1]
	%18 = icmp eq i8* %16, null		; <i1> [#uses=1]
	%19 = or i1 %17, %18		; <i1> [#uses=1]
	br i1 %19, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%20 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %20, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next101 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%21 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 0		; <i8**> [#uses=1]
	store i8* %6, i8** %21, align 4
	%22 = getelementptr %struct.PtrBaseBound* %12, i32 %14, i32 1		; <i8**> [#uses=1]
	store i8* %8, i8** %22, align 4
	store i8* %9, i8** %15, align 4
	%23 = getelementptr %struct.group* %4, i32 0, i32 1		; <i8**> [#uses=3]
	%24 = load i8** %23, align 4		; <i8*> [#uses=3]
	%25 = tail call i32 @strlen(i8* %24) nounwind readonly		; <i32> [#uses=1]
	%.sum7 = add i32 %25, 1		; <i32> [#uses=1]
	%26 = getelementptr i8* %24, i32 %.sum7		; <i8*> [#uses=1]
	%27 = bitcast i8** %23 to i8*		; <i8*> [#uses=2]
	%28 = ptrtoint i8** %23 to i32		; <i32> [#uses=1]
	%29 = lshr i32 %28, 2		; <i32> [#uses=1]
	%30 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i24

bb.i24:		; preds = %bb8.i28, %__hashStoreBaseBound.exit
	%counter.0.i23 = phi i32 [ 0, %__hashStoreBaseBound.exit ], [ %indvar.next96, %bb8.i28 ]		; <i32> [#uses=3]
	%31 = add i32 %counter.0.i23, %29		; <i32> [#uses=1]
	%32 = and i32 %31, 134217727		; <i32> [#uses=3]
	%33 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 2		; <i8**> [#uses=2]
	%34 = load i8** %33, align 4		; <i8*> [#uses=2]
	%35 = icmp eq i8* %34, %27		; <i1> [#uses=1]
	%36 = icmp eq i8* %34, null		; <i1> [#uses=1]
	%37 = or i1 %35, %36		; <i1> [#uses=1]
	br i1 %37, label %__hashStoreBaseBound.exit29, label %bb6.i25

bb6.i25:		; preds = %bb.i24
	%38 = icmp ugt i32 %counter.0.i23, 134217727		; <i1> [#uses=1]
	br i1 %38, label %bb7.i26, label %bb8.i28

bb7.i26:		; preds = %bb6.i25
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i28:		; preds = %bb6.i25
	%indvar.next96 = add i32 %counter.0.i23, 1		; <i32> [#uses=1]
	br label %bb.i24

__hashStoreBaseBound.exit29:		; preds = %bb.i24
	%39 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 0		; <i8**> [#uses=1]
	store i8* %24, i8** %39, align 4
	%40 = getelementptr %struct.PtrBaseBound* %30, i32 %32, i32 1		; <i8**> [#uses=1]
	store i8* %26, i8** %40, align 4
	store i8* %27, i8** %33, align 4
	%41 = getelementptr %struct.group* %4, i32 0, i32 3		; <i8***> [#uses=4]
	%42 = load i8*** %41, align 4		; <i8**> [#uses=2]
	%43 = icmp eq i8** %42, null		; <i1> [#uses=1]
	br i1 %43, label %return, label %bb3

bb2:		; preds = %bb3
	%44 = tail call i32 @strlen(i8* %61) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %44, 1		; <i32> [#uses=1]
	%45 = getelementptr i8* %61, i32 %.sum		; <i8*> [#uses=1]
	%46 = bitcast i8** %60 to i8*		; <i8*> [#uses=2]
	%47 = ptrtoint i8** %60 to i32		; <i32> [#uses=1]
	%48 = lshr i32 %47, 2		; <i32> [#uses=1]
	%49 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i17

bb.i17:		; preds = %bb8.i21, %bb2
	%counter.0.i16 = phi i32 [ 0, %bb2 ], [ %indvar.next, %bb8.i21 ]		; <i32> [#uses=3]
	%50 = add i32 %counter.0.i16, %48		; <i32> [#uses=1]
	%51 = and i32 %50, 134217727		; <i32> [#uses=3]
	%52 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 2		; <i8**> [#uses=2]
	%53 = load i8** %52, align 4		; <i8*> [#uses=2]
	%54 = icmp eq i8* %53, %46		; <i1> [#uses=1]
	%55 = icmp eq i8* %53, null		; <i1> [#uses=1]
	%56 = or i1 %54, %55		; <i1> [#uses=1]
	br i1 %56, label %__hashStoreBaseBound.exit22, label %bb6.i18

bb6.i18:		; preds = %bb.i17
	%57 = icmp ugt i32 %counter.0.i16, 134217727		; <i1> [#uses=1]
	br i1 %57, label %bb7.i19, label %bb8.i21

bb7.i19:		; preds = %bb6.i18
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i21:		; preds = %bb6.i18
	%indvar.next = add i32 %counter.0.i16, 1		; <i32> [#uses=1]
	br label %bb.i17

__hashStoreBaseBound.exit22:		; preds = %bb.i17
	%58 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 0		; <i8**> [#uses=1]
	store i8* %61, i8** %58, align 4
	%59 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 1		; <i8**> [#uses=1]
	store i8* %45, i8** %59, align 4
	store i8* %46, i8** %52, align 4
	%indvar.next91 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb3

bb3:		; preds = %__hashStoreBaseBound.exit22, %__hashStoreBaseBound.exit29
	%i.0 = phi i32 [ %indvar.next91, %__hashStoreBaseBound.exit22 ], [ 0, %__hashStoreBaseBound.exit29 ]		; <i32> [#uses=3]
	%60 = getelementptr i8** %42, i32 %i.0		; <i8**> [#uses=3]
	%61 = load i8** %60, align 4		; <i8*> [#uses=4]
	%62 = icmp eq i8* %61, null		; <i1> [#uses=1]
	br i1 %62, label %bb4, label %bb2

bb4:		; preds = %bb3
	%63 = load i8*** %41, align 4		; <i8**> [#uses=2]
	%64 = add i32 %i.0, 1		; <i32> [#uses=1]
	%65 = getelementptr i8** %63, i32 %64		; <i8**> [#uses=1]
	%66 = bitcast i8*** %41 to i8*		; <i8*> [#uses=2]
	%67 = bitcast i8** %63 to i8*		; <i8*> [#uses=1]
	%68 = bitcast i8** %65 to i8*		; <i8*> [#uses=1]
	%69 = ptrtoint i8*** %41 to i32		; <i32> [#uses=1]
	%70 = lshr i32 %69, 2		; <i32> [#uses=1]
	%71 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i10

bb.i10:		; preds = %bb8.i14, %bb4
	%counter.0.i9 = phi i32 [ 0, %bb4 ], [ %indvar.next85, %bb8.i14 ]		; <i32> [#uses=3]
	%72 = add i32 %counter.0.i9, %70		; <i32> [#uses=1]
	%73 = and i32 %72, 134217727		; <i32> [#uses=3]
	%74 = getelementptr %struct.PtrBaseBound* %71, i32 %73, i32 2		; <i8**> [#uses=2]
	%75 = load i8** %74, align 4		; <i8*> [#uses=2]
	%76 = icmp eq i8* %75, %66		; <i1> [#uses=1]
	%77 = icmp eq i8* %75, null		; <i1> [#uses=1]
	%78 = or i1 %76, %77		; <i1> [#uses=1]
	br i1 %78, label %__hashStoreBaseBound.exit15, label %bb6.i11

bb6.i11:		; preds = %bb.i10
	%79 = icmp ugt i32 %counter.0.i9, 134217727		; <i1> [#uses=1]
	br i1 %79, label %bb7.i12, label %bb8.i14

bb7.i12:		; preds = %bb6.i11
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i14:		; preds = %bb6.i11
	%indvar.next85 = add i32 %counter.0.i9, 1		; <i32> [#uses=1]
	br label %bb.i10

__hashStoreBaseBound.exit15:		; preds = %bb.i10
	%80 = getelementptr %struct.PtrBaseBound* %71, i32 %73, i32 0		; <i8**> [#uses=1]
	store i8* %67, i8** %80, align 4
	%81 = getelementptr %struct.PtrBaseBound* %71, i32 %73, i32 1		; <i8**> [#uses=1]
	store i8* %68, i8** %81, align 4
	store i8* %66, i8** %74, align 4
	ret void

bb5:		; preds = %entry
	%82 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* null, i8** %82, align 4
	%83 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %83, align 4
	ret void

return:		; preds = %__hashStoreBaseBound.exit29
	ret void
}

declare %struct.group* @getgrgid(i32)

define weak void @softbound_getpwuid(%struct.PtrBaseBound* %ptrs, i32 %uid) nounwind alwaysinline {
entry:
	%0 = tail call %struct.passwd* @getpwuid(i32 %uid) nounwind		; <%struct.passwd*> [#uses=8]
	%1 = bitcast %struct.passwd* %0 to i8*		; <i8*> [#uses=9]
	%2 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %2, align 4
	%3 = icmp eq %struct.passwd* %0, null		; <i1> [#uses=1]
	%4 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=2]
	br i1 %3, label %bb1, label %bb

bb:		; preds = %entry
	store i8* %1, i8** %4, align 4
	%5 = getelementptr i8* %1, i32 28		; <i8*> [#uses=1]
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %5, i8** %6, align 4
	%7 = getelementptr %struct.passwd* %0, i32 0, i32 0		; <i8**> [#uses=1]
	%8 = load i8** %7, align 4		; <i8*> [#uses=3]
	%9 = tail call i32 @strlen(i8* %8) nounwind readonly		; <i32> [#uses=1]
	%.sum6 = add i32 %9, 1		; <i32> [#uses=1]
	%10 = getelementptr i8* %8, i32 %.sum6		; <i8*> [#uses=1]
	%11 = ptrtoint %struct.passwd* %0 to i32		; <i32> [#uses=1]
	%12 = lshr i32 %11, 2		; <i32> [#uses=1]
	%13 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb
	%counter.0.i = phi i32 [ 0, %bb ], [ %indvar.next118, %bb8.i ]		; <i32> [#uses=3]
	%14 = add i32 %counter.0.i, %12		; <i32> [#uses=1]
	%15 = and i32 %14, 134217727		; <i32> [#uses=3]
	%16 = getelementptr %struct.PtrBaseBound* %13, i32 %15, i32 2		; <i8**> [#uses=2]
	%17 = load i8** %16, align 4		; <i8*> [#uses=2]
	%18 = icmp eq i8* %17, %1		; <i1> [#uses=1]
	%19 = icmp eq i8* %17, null		; <i1> [#uses=1]
	%20 = or i1 %18, %19		; <i1> [#uses=1]
	br i1 %20, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%21 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %21, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next118 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%22 = getelementptr %struct.PtrBaseBound* %13, i32 %15, i32 0		; <i8**> [#uses=1]
	store i8* %8, i8** %22, align 4
	%23 = getelementptr %struct.PtrBaseBound* %13, i32 %15, i32 1		; <i8**> [#uses=1]
	store i8* %10, i8** %23, align 4
	store i8* %1, i8** %16, align 4
	%24 = getelementptr %struct.passwd* %0, i32 0, i32 1		; <i8**> [#uses=1]
	%25 = load i8** %24, align 4		; <i8*> [#uses=3]
	%26 = tail call i32 @strlen(i8* %25) nounwind readonly		; <i32> [#uses=1]
	%.sum5 = add i32 %26, 1		; <i32> [#uses=1]
	%27 = getelementptr i8* %25, i32 %.sum5		; <i8*> [#uses=1]
	%28 = getelementptr i8* %1, i32 4		; <i8*> [#uses=3]
	%29 = ptrtoint i8* %28 to i32		; <i32> [#uses=1]
	%30 = lshr i32 %29, 2		; <i32> [#uses=1]
	%31 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i29

bb.i29:		; preds = %bb8.i33, %__hashStoreBaseBound.exit
	%counter.0.i28 = phi i32 [ 0, %__hashStoreBaseBound.exit ], [ %indvar.next113, %bb8.i33 ]		; <i32> [#uses=3]
	%32 = add i32 %counter.0.i28, %30		; <i32> [#uses=1]
	%33 = and i32 %32, 134217727		; <i32> [#uses=3]
	%34 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 2		; <i8**> [#uses=2]
	%35 = load i8** %34, align 4		; <i8*> [#uses=2]
	%36 = icmp eq i8* %35, %28		; <i1> [#uses=1]
	%37 = icmp eq i8* %35, null		; <i1> [#uses=1]
	%38 = or i1 %36, %37		; <i1> [#uses=1]
	br i1 %38, label %__hashStoreBaseBound.exit34, label %bb6.i30

bb6.i30:		; preds = %bb.i29
	%39 = icmp ugt i32 %counter.0.i28, 134217727		; <i1> [#uses=1]
	br i1 %39, label %bb7.i31, label %bb8.i33

bb7.i31:		; preds = %bb6.i30
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i33:		; preds = %bb6.i30
	%indvar.next113 = add i32 %counter.0.i28, 1		; <i32> [#uses=1]
	br label %bb.i29

__hashStoreBaseBound.exit34:		; preds = %bb.i29
	%40 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 0		; <i8**> [#uses=1]
	store i8* %25, i8** %40, align 4
	%41 = getelementptr %struct.PtrBaseBound* %31, i32 %33, i32 1		; <i8**> [#uses=1]
	store i8* %27, i8** %41, align 4
	store i8* %28, i8** %34, align 4
	%42 = getelementptr %struct.passwd* %0, i32 0, i32 4		; <i8**> [#uses=1]
	%43 = load i8** %42, align 4		; <i8*> [#uses=3]
	%44 = tail call i32 @strlen(i8* %43) nounwind readonly		; <i32> [#uses=1]
	%.sum4 = add i32 %44, 1		; <i32> [#uses=1]
	%45 = getelementptr i8* %43, i32 %.sum4		; <i8*> [#uses=1]
	%46 = getelementptr i8* %1, i32 16		; <i8*> [#uses=3]
	%47 = ptrtoint i8* %46 to i32		; <i32> [#uses=1]
	%48 = lshr i32 %47, 2		; <i32> [#uses=1]
	%49 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i22

bb.i22:		; preds = %bb8.i26, %__hashStoreBaseBound.exit34
	%counter.0.i21 = phi i32 [ 0, %__hashStoreBaseBound.exit34 ], [ %indvar.next108, %bb8.i26 ]		; <i32> [#uses=3]
	%50 = add i32 %counter.0.i21, %48		; <i32> [#uses=1]
	%51 = and i32 %50, 134217727		; <i32> [#uses=3]
	%52 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 2		; <i8**> [#uses=2]
	%53 = load i8** %52, align 4		; <i8*> [#uses=2]
	%54 = icmp eq i8* %53, %46		; <i1> [#uses=1]
	%55 = icmp eq i8* %53, null		; <i1> [#uses=1]
	%56 = or i1 %54, %55		; <i1> [#uses=1]
	br i1 %56, label %__hashStoreBaseBound.exit27, label %bb6.i23

bb6.i23:		; preds = %bb.i22
	%57 = icmp ugt i32 %counter.0.i21, 134217727		; <i1> [#uses=1]
	br i1 %57, label %bb7.i24, label %bb8.i26

bb7.i24:		; preds = %bb6.i23
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i26:		; preds = %bb6.i23
	%indvar.next108 = add i32 %counter.0.i21, 1		; <i32> [#uses=1]
	br label %bb.i22

__hashStoreBaseBound.exit27:		; preds = %bb.i22
	%58 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 0		; <i8**> [#uses=1]
	store i8* %43, i8** %58, align 4
	%59 = getelementptr %struct.PtrBaseBound* %49, i32 %51, i32 1		; <i8**> [#uses=1]
	store i8* %45, i8** %59, align 4
	store i8* %46, i8** %52, align 4
	%60 = getelementptr %struct.passwd* %0, i32 0, i32 5		; <i8**> [#uses=1]
	%61 = load i8** %60, align 4		; <i8*> [#uses=3]
	%62 = tail call i32 @strlen(i8* %61) nounwind readonly		; <i32> [#uses=1]
	%.sum3 = add i32 %62, 1		; <i32> [#uses=1]
	%63 = getelementptr i8* %61, i32 %.sum3		; <i8*> [#uses=1]
	%64 = getelementptr i8* %1, i32 20		; <i8*> [#uses=3]
	%65 = ptrtoint i8* %64 to i32		; <i32> [#uses=1]
	%66 = lshr i32 %65, 2		; <i32> [#uses=1]
	%67 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i15

bb.i15:		; preds = %bb8.i19, %__hashStoreBaseBound.exit27
	%counter.0.i14 = phi i32 [ 0, %__hashStoreBaseBound.exit27 ], [ %indvar.next, %bb8.i19 ]		; <i32> [#uses=3]
	%68 = add i32 %counter.0.i14, %66		; <i32> [#uses=1]
	%69 = and i32 %68, 134217727		; <i32> [#uses=3]
	%70 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 2		; <i8**> [#uses=2]
	%71 = load i8** %70, align 4		; <i8*> [#uses=2]
	%72 = icmp eq i8* %71, %64		; <i1> [#uses=1]
	%73 = icmp eq i8* %71, null		; <i1> [#uses=1]
	%74 = or i1 %72, %73		; <i1> [#uses=1]
	br i1 %74, label %__hashStoreBaseBound.exit20, label %bb6.i16

bb6.i16:		; preds = %bb.i15
	%75 = icmp ugt i32 %counter.0.i14, 134217727		; <i1> [#uses=1]
	br i1 %75, label %bb7.i17, label %bb8.i19

bb7.i17:		; preds = %bb6.i16
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i19:		; preds = %bb6.i16
	%indvar.next = add i32 %counter.0.i14, 1		; <i32> [#uses=1]
	br label %bb.i15

__hashStoreBaseBound.exit20:		; preds = %bb.i15
	%76 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 0		; <i8**> [#uses=1]
	store i8* %61, i8** %76, align 4
	%77 = getelementptr %struct.PtrBaseBound* %67, i32 %69, i32 1		; <i8**> [#uses=1]
	store i8* %63, i8** %77, align 4
	store i8* %64, i8** %70, align 4
	%78 = getelementptr %struct.passwd* %0, i32 0, i32 6		; <i8**> [#uses=1]
	%79 = load i8** %78, align 4		; <i8*> [#uses=3]
	%80 = tail call i32 @strlen(i8* %79) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %80, 1		; <i32> [#uses=1]
	%81 = getelementptr i8* %79, i32 %.sum		; <i8*> [#uses=1]
	%82 = getelementptr i8* %1, i32 24		; <i8*> [#uses=3]
	%83 = ptrtoint i8* %82 to i32		; <i32> [#uses=1]
	%84 = lshr i32 %83, 2		; <i32> [#uses=1]
	%85 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i8

bb.i8:		; preds = %bb8.i12, %__hashStoreBaseBound.exit20
	%counter.0.i7 = phi i32 [ 0, %__hashStoreBaseBound.exit20 ], [ %indvar.next99, %bb8.i12 ]		; <i32> [#uses=3]
	%86 = add i32 %counter.0.i7, %84		; <i32> [#uses=1]
	%87 = and i32 %86, 134217727		; <i32> [#uses=3]
	%88 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 2		; <i8**> [#uses=2]
	%89 = load i8** %88, align 4		; <i8*> [#uses=2]
	%90 = icmp eq i8* %89, %82		; <i1> [#uses=1]
	%91 = icmp eq i8* %89, null		; <i1> [#uses=1]
	%92 = or i1 %90, %91		; <i1> [#uses=1]
	br i1 %92, label %__hashStoreBaseBound.exit13, label %bb6.i9

bb6.i9:		; preds = %bb.i8
	%93 = icmp ugt i32 %counter.0.i7, 134217727		; <i1> [#uses=1]
	br i1 %93, label %bb7.i10, label %bb8.i12

bb7.i10:		; preds = %bb6.i9
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i12:		; preds = %bb6.i9
	%indvar.next99 = add i32 %counter.0.i7, 1		; <i32> [#uses=1]
	br label %bb.i8

__hashStoreBaseBound.exit13:		; preds = %bb.i8
	%94 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 0		; <i8**> [#uses=1]
	store i8* %79, i8** %94, align 4
	%95 = getelementptr %struct.PtrBaseBound* %85, i32 %87, i32 1		; <i8**> [#uses=1]
	store i8* %81, i8** %95, align 4
	store i8* %82, i8** %88, align 4
	ret void

bb1:		; preds = %entry
	store i8* null, i8** %4, align 4
	%96 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* null, i8** %96, align 4
	ret void
}

declare %struct.passwd* @getpwuid(i32)

define weak void @softbound_new_realloc(%struct.PtrBaseBound* %ptrs, i8* %ptr, i32 %size, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
	%bound = alloca i8*, align 4		; <i8**> [#uses=3]
	%base = alloca i8*, align 4		; <i8**> [#uses=3]
	%0 = call i8* @realloc(i8* %ptr, i32 %size) nounwind		; <i8*> [#uses=6]
	%1 = icmp ne i8* %0, %ptr		; <i1> [#uses=1]
	%2 = icmp ne i8* %0, null		; <i1> [#uses=1]
	%3 = and i1 %1, %2		; <i1> [#uses=1]
	br i1 %3, label %bb5, label %bb6

bb:		; preds = %bb5
	store i8* null, i8** %base, align 4
	store i8* null, i8** %bound, align 4
	%4 = call i32 @__hashProbeAddrOfPtr(i8* %ptr_addr.0, i8** %base, i8** %bound) nounwind alwaysinline		; <i32> [#uses=1]
	%5 = icmp eq i32 %4, 0		; <i1> [#uses=1]
	br i1 %5, label %bb4, label %bb3

bb3:		; preds = %bb
	%6 = load i8** %bound, align 4		; <i8*> [#uses=1]
	%7 = load i8** %base, align 4		; <i8*> [#uses=1]
	%8 = ptrtoint i8* %temp.0 to i32		; <i32> [#uses=1]
	%9 = lshr i32 %8, 2		; <i32> [#uses=1]
	%10 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb3
	%counter.0.i = phi i32 [ 0, %bb3 ], [ %indvar.next21, %bb8.i ]		; <i32> [#uses=3]
	%11 = add i32 %counter.0.i, %9		; <i32> [#uses=1]
	%12 = and i32 %11, 134217727		; <i32> [#uses=3]
	%13 = getelementptr %struct.PtrBaseBound* %10, i32 %12, i32 2		; <i8**> [#uses=2]
	%14 = load i8** %13, align 4		; <i8*> [#uses=2]
	%15 = icmp eq i8* %14, %temp.0		; <i1> [#uses=1]
	%16 = icmp eq i8* %14, null		; <i1> [#uses=1]
	%17 = or i1 %15, %16		; <i1> [#uses=1]
	br i1 %17, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%18 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %18, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next21 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%19 = getelementptr %struct.PtrBaseBound* %10, i32 %12, i32 0		; <i8**> [#uses=1]
	store i8* %7, i8** %19, align 4
	%20 = getelementptr %struct.PtrBaseBound* %10, i32 %12, i32 1		; <i8**> [#uses=1]
	store i8* %6, i8** %20, align 4
	store i8* %temp.0, i8** %13, align 4
	br label %bb4

bb4:		; preds = %__hashStoreBaseBound.exit, %bb
	%indvar.next = add i32 %ptr_addr.0.rec, 1		; <i32> [#uses=1]
	br label %bb5

bb5:		; preds = %bb4, %entry
	%ptr_addr.0.rec = phi i32 [ %indvar.next, %bb4 ], [ 0, %entry ]		; <i32> [#uses=3]
	%temp.0 = getelementptr i8* %0, i32 %ptr_addr.0.rec		; <i8*> [#uses=3]
	%ptr_addr.0 = getelementptr i8* %ptr, i32 %ptr_addr.0.rec		; <i8*> [#uses=2]
	%21 = icmp ult i8* %ptr_addr.0, %ptr_bound		; <i1> [#uses=1]
	br i1 %21, label %bb, label %bb6

bb6:		; preds = %bb5, %entry
	%22 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %0, i8** %22, align 4
	%23 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %0, i8** %23, align 4
	%24 = getelementptr i8* %0, i32 %size		; <i8*> [#uses=1]
	%25 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %24, i8** %25, align 4
	ret void
}

define weak void @softbound_new_memcpy(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i32 %n, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
	%bound = alloca i8*, align 4		; <i8**> [#uses=3]
	%base = alloca i8*, align 4		; <i8**> [#uses=3]
	call void @llvm.memcpy.i32(i8* %dest, i8* %src, i32 %n, i32 1)
	br label %bb3

bb:		; preds = %bb3
	%temp2.0 = getelementptr i8* %src, i32 %count.0		; <i8*> [#uses=1]
	store i8* null, i8** %base, align 4
	store i8* null, i8** %bound, align 4
	%0 = call i32 @__hashProbeAddrOfPtr(i8* %temp2.0, i8** %base, i8** %bound) nounwind alwaysinline		; <i32> [#uses=1]
	%1 = icmp eq i32 %0, 0		; <i1> [#uses=1]
	br i1 %1, label %bb2, label %bb1

bb1:		; preds = %bb
	%2 = load i8** %bound, align 4		; <i8*> [#uses=1]
	%3 = load i8** %base, align 4		; <i8*> [#uses=1]
	%4 = ptrtoint i8* %temp1.0 to i32		; <i32> [#uses=1]
	%5 = lshr i32 %4, 2		; <i32> [#uses=1]
	%6 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %bb1
	%counter.0.i = phi i32 [ 0, %bb1 ], [ %indvar.next19, %bb8.i ]		; <i32> [#uses=3]
	%7 = add i32 %counter.0.i, %5		; <i32> [#uses=1]
	%8 = and i32 %7, 134217727		; <i32> [#uses=3]
	%9 = getelementptr %struct.PtrBaseBound* %6, i32 %8, i32 2		; <i8**> [#uses=2]
	%10 = load i8** %9, align 4		; <i8*> [#uses=2]
	%11 = icmp eq i8* %10, %temp1.0		; <i1> [#uses=1]
	%12 = icmp eq i8* %10, null		; <i1> [#uses=1]
	%13 = or i1 %11, %12		; <i1> [#uses=1]
	br i1 %13, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%14 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %14, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next19 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%15 = getelementptr %struct.PtrBaseBound* %6, i32 %8, i32 0		; <i8**> [#uses=1]
	store i8* %3, i8** %15, align 4
	%16 = getelementptr %struct.PtrBaseBound* %6, i32 %8, i32 1		; <i8**> [#uses=1]
	store i8* %2, i8** %16, align 4
	store i8* %temp1.0, i8** %9, align 4
	br label %bb2

bb2:		; preds = %__hashStoreBaseBound.exit, %bb
	%indvar.next = add i32 %count.0, 1		; <i32> [#uses=1]
	br label %bb3

bb3:		; preds = %bb2, %entry
	%count.0 = phi i32 [ 0, %entry ], [ %indvar.next, %bb2 ]		; <i32> [#uses=4]
	%temp1.0 = getelementptr i8* %dest, i32 %count.0		; <i8*> [#uses=3]
	%17 = icmp ult i32 %count.0, %n		; <i1> [#uses=1]
	br i1 %17, label %bb, label %bb4

bb4:		; preds = %bb3
	%18 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %dest, i8** %18, align 4
	%19 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %dest_base, i8** %19, align 4
	%20 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %dest_bound, i8** %20, align 4
	ret void
}

declare void @llvm.memcpy.i32(i8* nocapture, i8* nocapture, i32, i32) nounwind

define void @ptr_memcopy(i8** %fake_buffer, i8** %true_buffer, i32 %size) nounwind {
entry:
	br label %bb1

bb:		; preds = %bb1
	%0 = getelementptr i8** %true_buffer, i32 %i.0		; <i8**> [#uses=3]
	%1 = load i8** %0, align 4		; <i8*> [#uses=1]
	%2 = getelementptr i8** %fake_buffer, i32 %i.0		; <i8**> [#uses=3]
	store i8* %1, i8** %2, align 4
	%3 = bitcast i8** %0 to i8*		; <i8*> [#uses=1]
	%4 = ptrtoint i8** %0 to i32		; <i32> [#uses=1]
	%5 = lshr i32 %4, 2		; <i32> [#uses=1]
	%6 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=6]
	br label %bb.i

bb.i:		; preds = %bb2.i, %bb
	%counter.0.i = phi i32 [ 0, %bb ], [ %11, %bb2.i ]		; <i32> [#uses=2]
	%7 = add i32 %counter.0.i, %5		; <i32> [#uses=1]
	%8 = and i32 %7, 134217727		; <i32> [#uses=3]
	%9 = getelementptr %struct.PtrBaseBound* %6, i32 %8, i32 2		; <i8**> [#uses=1]
	%10 = load i8** %9, align 4		; <i8*> [#uses=2]
	%11 = add i32 %counter.0.i, 1		; <i32> [#uses=2]
	%12 = icmp eq i8* %10, %3		; <i1> [#uses=1]
	br i1 %12, label %bb1.i, label %bb2.i

bb1.i:		; preds = %bb.i
	%13 = getelementptr %struct.PtrBaseBound* %6, i32 %8, i32 0		; <i8**> [#uses=1]
	%14 = load i8** %13, align 4		; <i8*> [#uses=1]
	%15 = getelementptr %struct.PtrBaseBound* %6, i32 %8, i32 1		; <i8**> [#uses=1]
	%16 = load i8** %15, align 4		; <i8*> [#uses=1]
	br label %bb4.i

bb2.i:		; preds = %bb.i
	%17 = icmp eq i8* %10, null		; <i1> [#uses=1]
	br i1 %17, label %bb4.i, label %bb.i

bb4.i:		; preds = %bb2.i, %bb1.i
	%final_bound.0.i = phi i8* [ %16, %bb1.i ], [ null, %bb2.i ]		; <i8*> [#uses=1]
	%final_base.0.i = phi i8* [ %14, %bb1.i ], [ null, %bb2.i ]		; <i8*> [#uses=1]
	%18 = icmp ugt i32 %11, 134217727		; <i1> [#uses=1]
	br i1 %18, label %bb5.i, label %__hashLoadBaseBound.exit

bb5.i:		; preds = %bb4.i
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

__hashLoadBaseBound.exit:		; preds = %bb4.i
	%19 = bitcast i8** %2 to i8*		; <i8*> [#uses=2]
	%20 = ptrtoint i8** %2 to i32		; <i32> [#uses=1]
	%21 = lshr i32 %20, 2		; <i32> [#uses=1]
	br label %bb.i4

bb.i4:		; preds = %bb8.i, %__hashLoadBaseBound.exit
	%counter.0.i3 = phi i32 [ 0, %__hashLoadBaseBound.exit ], [ %indvar.next40, %bb8.i ]		; <i32> [#uses=3]
	%22 = add i32 %counter.0.i3, %21		; <i32> [#uses=1]
	%23 = and i32 %22, 134217727		; <i32> [#uses=3]
	%24 = getelementptr %struct.PtrBaseBound* %6, i32 %23, i32 2		; <i8**> [#uses=2]
	%25 = load i8** %24, align 4		; <i8*> [#uses=2]
	%26 = icmp eq i8* %25, %19		; <i1> [#uses=1]
	%27 = icmp eq i8* %25, null		; <i1> [#uses=1]
	%28 = or i1 %26, %27		; <i1> [#uses=1]
	br i1 %28, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i4
	%29 = icmp ugt i32 %counter.0.i3, 134217727		; <i1> [#uses=1]
	br i1 %29, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next40 = add i32 %counter.0.i3, 1		; <i32> [#uses=1]
	br label %bb.i4

__hashStoreBaseBound.exit:		; preds = %bb.i4
	%30 = getelementptr %struct.PtrBaseBound* %6, i32 %23, i32 0		; <i8**> [#uses=1]
	store i8* %final_base.0.i, i8** %30, align 4
	%31 = getelementptr %struct.PtrBaseBound* %6, i32 %23, i32 1		; <i8**> [#uses=1]
	store i8* %final_bound.0.i, i8** %31, align 4
	store i8* %19, i8** %24, align 4
	%indvar.next41 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %__hashStoreBaseBound.exit, %entry
	%i.0 = phi i32 [ 0, %entry ], [ %indvar.next41, %__hashStoreBaseBound.exit ]		; <i32> [#uses=4]
	%32 = icmp ult i32 %i.0, %size		; <i1> [#uses=1]
	br i1 %32, label %bb, label %return

return:		; preds = %bb1
	ret void
}

define weak void @softbound_changed_realloc(%struct.PtrBaseBound* %ptrs, i8** %current_ptr, i32 %n_gathers, i8* %current_ptr_base, i8* %current_ptr_bound) nounwind alwaysinline {
entry:
	%0 = malloc i8*, i32 %n_gathers		; <i8**> [#uses=2]
	%tmpcast = bitcast i8** %0 to i8*		; <i8*> [#uses=3]
	%1 = ptrtoint i8* %current_ptr_bound to i32		; <i32> [#uses=1]
	%2 = ptrtoint i8* %current_ptr_base to i32		; <i32> [#uses=1]
	%3 = sub i32 %1, %2		; <i32> [#uses=1]
	%4 = lshr i32 %3, 2		; <i32> [#uses=1]
	%5 = add i32 %4, -1		; <i32> [#uses=1]
	tail call void @ptr_memcopy(i8** %0, i8** %current_ptr, i32 %5) nounwind
	free i8** %current_ptr
	%6 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 0		; <i8**> [#uses=1]
	store i8* %tmpcast, i8** %6, align 4
	%7 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 1		; <i8**> [#uses=1]
	store i8* %tmpcast, i8** %7, align 4
	%8 = shl i32 %n_gathers, 2		; <i32> [#uses=1]
	%9 = getelementptr i8* %tmpcast, i32 %8		; <i8*> [#uses=1]
	%10 = getelementptr %struct.PtrBaseBound* %ptrs, i32 0, i32 2		; <i8**> [#uses=1]
	store i8* %9, i8** %10, align 4
	ret void
}

define weak i32 @softbound_strtol(i8* %nptr, i8** %endptr, i32 %base, i8* %nptr_base, i8* %nptr_bound, i8* %endptr_base, i8* %endptr_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strtol(i8* noalias %nptr, i8** noalias %endptr, i32 %base) nounwind		; <i32> [#uses=1]
	%1 = load i8** %endptr, align 4		; <i8*> [#uses=3]
	%2 = tail call i32 @strlen(i8* %1) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %2, 1		; <i32> [#uses=1]
	%3 = getelementptr i8* %1, i32 %.sum		; <i8*> [#uses=1]
	%4 = bitcast i8** %endptr to i8*		; <i8*> [#uses=2]
	%5 = ptrtoint i8** %endptr to i32		; <i32> [#uses=1]
	%6 = lshr i32 %5, 2		; <i32> [#uses=1]
	%7 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next14, %bb8.i ]		; <i32> [#uses=3]
	%8 = add i32 %counter.0.i, %6		; <i32> [#uses=1]
	%9 = and i32 %8, 134217727		; <i32> [#uses=3]
	%10 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 2		; <i8**> [#uses=2]
	%11 = load i8** %10, align 4		; <i8*> [#uses=2]
	%12 = icmp eq i8* %11, %4		; <i1> [#uses=1]
	%13 = icmp eq i8* %11, null		; <i1> [#uses=1]
	%14 = or i1 %12, %13		; <i1> [#uses=1]
	br i1 %14, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%15 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %15, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next14 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%16 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %16, align 4
	%17 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 1		; <i8**> [#uses=1]
	store i8* %3, i8** %17, align 4
	store i8* %4, i8** %10, align 4
	ret i32 %0
}

declare i32 @strtol(i8* noalias, i8** noalias, i32) nounwind

define weak i32 @softbound_strtoul(i8* %nptr, i8** %endptr, i32 %base, i8* %nptr_base, i8* %nptr_bound, i8* %endptr_base, i8* %endptr_bound) nounwind alwaysinline {
entry:
	%0 = tail call i32 @strtoul(i8* noalias %nptr, i8** noalias %endptr, i32 %base) nounwind		; <i32> [#uses=1]
	%1 = load i8** %endptr, align 4		; <i8*> [#uses=3]
	%2 = tail call i32 @strlen(i8* %1) nounwind readonly		; <i32> [#uses=1]
	%.sum = add i32 %2, 1		; <i32> [#uses=1]
	%3 = getelementptr i8* %1, i32 %.sum		; <i8*> [#uses=1]
	%4 = bitcast i8** %endptr to i8*		; <i8*> [#uses=2]
	%5 = ptrtoint i8** %endptr to i32		; <i32> [#uses=1]
	%6 = lshr i32 %5, 2		; <i32> [#uses=1]
	%7 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4		; <%struct.PtrBaseBound*> [#uses=3]
	br label %bb.i

bb.i:		; preds = %bb8.i, %entry
	%counter.0.i = phi i32 [ 0, %entry ], [ %indvar.next14, %bb8.i ]		; <i32> [#uses=3]
	%8 = add i32 %counter.0.i, %6		; <i32> [#uses=1]
	%9 = and i32 %8, 134217727		; <i32> [#uses=3]
	%10 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 2		; <i8**> [#uses=2]
	%11 = load i8** %10, align 4		; <i8*> [#uses=2]
	%12 = icmp eq i8* %11, %4		; <i1> [#uses=1]
	%13 = icmp eq i8* %11, null		; <i1> [#uses=1]
	%14 = or i1 %12, %13		; <i1> [#uses=1]
	br i1 %14, label %__hashStoreBaseBound.exit, label %bb6.i

bb6.i:		; preds = %bb.i
	%15 = icmp ugt i32 %counter.0.i, 134217727		; <i1> [#uses=1]
	br i1 %15, label %bb7.i, label %bb8.i

bb7.i:		; preds = %bb6.i
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str211, i32 0, i32 0)) nounwind
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

bb8.i:		; preds = %bb6.i
	%indvar.next14 = add i32 %counter.0.i, 1		; <i32> [#uses=1]
	br label %bb.i

__hashStoreBaseBound.exit:		; preds = %bb.i
	%16 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 0		; <i8**> [#uses=1]
	store i8* %1, i8** %16, align 4
	%17 = getelementptr %struct.PtrBaseBound* %7, i32 %9, i32 1		; <i8**> [#uses=1]
	store i8* %3, i8** %17, align 4
	store i8* %4, i8** %10, align 4
	ret i32 %0
}

declare i32 @strtoul(i8* noalias, i8** noalias, i32) nounwind

define internal void @__softbound_global_init13() nounwind {
entry:
	tail call void @__softbound_init(i32 1, i32 0) nounwind
	ret void
}
