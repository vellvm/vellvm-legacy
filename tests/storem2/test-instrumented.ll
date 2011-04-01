; ModuleID = 'test-instrumented.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
	%struct.__softbound_hash_table_entry_t = type { i8*, i8*, i8* }
@__softbound_hash_table_begin = external global %struct.__softbound_hash_table_entry_t*		; <%struct.__softbound_hash_table_entry_t**> [#uses=3]
@.str = internal constant [17 x i8] c"Hash table full\0A\00"		; <[17 x i8]*> [#uses=1]
@llvm.global_ctors = appending global [1 x { i32, void ()* }] [ { i32, void ()* } { i32 65535, void ()* @__softbound_global_init } ]		; <[1 x { i32, void ()* }]*> [#uses=0]
@.str1 = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

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
	tail call void (...)* @__softbound_abort() noreturn nounwind
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
	tail call void (...)* @__softbound_abort() noreturn nounwind
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
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb
	ret void
}

define weak void @__memcopyCheck_i64(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
	%0 = icmp ugt i32 %size, -2147483648		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
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
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb3
	ret void
}

define weak void @__memcopyCheck(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
	%0 = icmp ugt i32 %size, -2147483648		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
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
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb3
	ret void
}

define weak void @__hashStoreBaseBound(i8* %addr_of_ptr, i8* %base, i8* %bound, i8* %actual_ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.__softbound_hash_table_entry_t** @__softbound_hash_table_begin, align 4		; <%struct.__softbound_hash_table_entry_t*> [#uses=3]
	br label %bb

bb:		; preds = %bb8, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %indvar.next19, %bb8 ]		; <i32> [#uses=3]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 2		; <i8**> [#uses=2]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	%8 = icmp eq i8* %6, null		; <i1> [#uses=1]
	%9 = or i1 %7, %8		; <i1> [#uses=1]
	br i1 %9, label %bb3, label %bb6

bb3:		; preds = %bb
	%10 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	store i8* %base, i8** %10, align 4
	%11 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	store i8* %bound, i8** %11, align 4
	store i8* %addr_of_ptr, i8** %5, align 4
	ret void

bb6:		; preds = %bb
	%12 = icmp ugt i32 %counter.0, 134217727		; <i1> [#uses=1]
	br i1 %12, label %bb7, label %bb8

bb7:		; preds = %bb6
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str, i32 0, i32 0)) nounwind
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

bb8:		; preds = %bb6
	%indvar.next19 = add i32 %counter.0, 1		; <i32> [#uses=1]
	br label %bb
}

define weak i32 @__hashProbeAddrOfPtr(i8* %addr_of_ptr, i8** %base, i8** %bound) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.__softbound_hash_table_entry_t** @__softbound_hash_table_begin, align 4		; <%struct.__softbound_hash_table_entry_t*> [#uses=3]
	br label %bb

bb:		; preds = %bb6, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %indvar.next15, %bb6 ]		; <i32> [#uses=2]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 2		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	br i1 %7, label %bb1, label %bb4

bb1:		; preds = %bb
	%8 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	%9 = load i8** %8, align 4		; <i8*> [#uses=2]
	%10 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 1		; <i8**> [#uses=1]
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
	%2 = load %struct.__softbound_hash_table_entry_t** @__softbound_hash_table_begin, align 4		; <%struct.__softbound_hash_table_entry_t*> [#uses=3]
	br label %bb

bb:		; preds = %bb2, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %7, %bb2 ]		; <i32> [#uses=2]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 2		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = add i32 %counter.0, 1		; <i32> [#uses=2]
	%8 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	br i1 %8, label %bb1, label %bb2

bb1:		; preds = %bb
	%9 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	%10 = load i8** %9, align 4		; <i8*> [#uses=1]
	%11 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 1		; <i8**> [#uses=1]
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
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb4
	ret void
}

declare void @__softbound_abort(...) noreturn

declare void @__softbound_printf(i8*, ...)

define internal void @__softbound_global_init() nounwind {
entry:
	tail call void @__softbound_init(i32 1, i32 0) nounwind
	ret void
}

declare void @__softbound_init(i32, i32)

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

declare i32 @softbound_atoi(i8*, i8*, i8*)

declare i32 @atoi(i8*) nounwind readonly

define void @softbound_test(i32 %mm) {
entry:
	%base.alloca = alloca i8*		; <i8**> [#uses=2]
	%bound.alloca = alloca i8*		; <i8**> [#uses=2]
	%safe.ptr9 = alloca i32		; <i32*> [#uses=2]
	%0 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=3]
	%malloc_bound = getelementptr [100 x i32*]* %0, i32 1		; <[100 x i32*]*> [#uses=1]
	%bitcast = bitcast [100 x i32*]* %0 to i8*		; <i8*> [#uses=2]
	%bitcast1 = bitcast [100 x i32*]* %malloc_bound to i8*		; <i8*> [#uses=2]
	%1 = malloc [100 x i32]		; <[100 x i32]*> [#uses=5]
	%malloc_bound2 = getelementptr [100 x i32]* %1, i32 1		; <[100 x i32]*> [#uses=1]
	%bitcast3 = bitcast [100 x i32]* %1 to i8*		; <i8*> [#uses=4]
	%bitcast4 = bitcast [100 x i32]* %malloc_bound2 to i8*		; <i8*> [#uses=4]
	%.sub6 = getelementptr [100 x i32*]* %0, i32 0, i32 0		; <i32**> [#uses=4]
	%.sub5 = getelementptr [100 x i32]* %1, i32 0, i32 0		; <i32*> [#uses=4]
	%bcast_st_dref_base = bitcast i8* %bitcast to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_bound = bitcast i8* %bitcast1 to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_ptr = bitcast i32** %.sub6 to i8*		; <i8*> [#uses=1]
	call void @__storeDereferenceCheck(i8* %bcast_st_dref_base, i8* %bcast_st_dref_bound, i8* %bcast_st_dref_ptr, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 1)
	store i32* %.sub5, i32** %.sub6, align 4
	%.sub6.vptr = bitcast i32** %.sub6 to i8*		; <i8*> [#uses=1]
	%bitcast3.vptr = bitcast i8* %bitcast3 to i8*		; <i8*> [#uses=1]
	%bitcast4.vptr = bitcast i8* %bitcast4 to i8*		; <i8*> [#uses=1]
	%.sub5.aptr = bitcast i32* %.sub5 to i8*		; <i8*> [#uses=1]
	call void @__hashStoreBaseBound(i8* %.sub6.vptr, i8* %bitcast3.vptr, i8* %bitcast4.vptr, i8* %.sub5.aptr, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	br label %bb3

bb:		; preds = %bb3
	%2 = getelementptr [100 x i32]* %1, i32 0, i32 %i.0		; <i32*> [#uses=2]
	%bcast_st_dref_base17 = bitcast i8* %arr1.1_base to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_bound18 = bitcast i8* %arr1.1_bound to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_ptr19 = bitcast i32** %arr1.1 to i8*		; <i8*> [#uses=1]
	call void @__storeDereferenceCheck(i8* %bcast_st_dref_base17, i8* %bcast_st_dref_bound18, i8* %bcast_st_dref_ptr19, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 %safe.phi_node)
	store i32* %2, i32** %arr1.1, align 4
	%arr1.1.vptr = bitcast i32** %arr1.1 to i8*		; <i8*> [#uses=1]
	%bitcast3.vptr12 = bitcast i8* %bitcast3 to i8*		; <i8*> [#uses=1]
	%bitcast4.vptr13 = bitcast i8* %bitcast4 to i8*		; <i8*> [#uses=1]
	%.aptr = bitcast i32* %2 to i8*		; <i8*> [#uses=1]
	call void @__hashStoreBaseBound(i8* %arr1.1.vptr, i8* %bitcast3.vptr12, i8* %bitcast4.vptr13, i8* %.aptr, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%3 = add i32 %i.0, 1		; <i32> [#uses=4]
	%4 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=3]
	%malloc_bound5 = getelementptr [100 x i32*]* %4, i32 1		; <[100 x i32*]*> [#uses=1]
	%bitcast6 = bitcast [100 x i32*]* %4 to i8*		; <i8*> [#uses=2]
	%bitcast7 = bitcast [100 x i32*]* %malloc_bound5 to i8*		; <i8*> [#uses=2]
	%.sub = getelementptr [100 x i32*]* %4, i32 0, i32 0		; <i32**> [#uses=4]
	%5 = getelementptr [100 x i32]* %1, i32 0, i32 %3		; <i32*> [#uses=3]
	%bcast_st_dref_base20 = bitcast i8* %bitcast6 to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_bound21 = bitcast i8* %bitcast7 to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_ptr22 = bitcast i32** %.sub to i8*		; <i8*> [#uses=1]
	call void @__storeDereferenceCheck(i8* %bcast_st_dref_base20, i8* %bcast_st_dref_bound21, i8* %bcast_st_dref_ptr22, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 1)
	store i32* %5, i32** %.sub, align 4
	%.sub.vptr = bitcast i32** %.sub to i8*		; <i8*> [#uses=1]
	%bitcast3.vptr14 = bitcast i8* %bitcast3 to i8*		; <i8*> [#uses=1]
	%bitcast4.vptr15 = bitcast i8* %bitcast4 to i8*		; <i8*> [#uses=1]
	%.aptr16 = bitcast i32* %5 to i8*		; <i8*> [#uses=1]
	call void @__hashStoreBaseBound(i8* %.sub.vptr, i8* %bitcast3.vptr14, i8* %bitcast4.vptr15, i8* %.aptr16, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%6 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str1, i32 0, i32 0), i32* %5) nounwind		; <i32> [#uses=0]
	%7 = and i32 %3, 1		; <i32> [#uses=1]
	%toBool = icmp eq i32 %7, 0		; <i1> [#uses=4]
	%arr1.0.base = select i1 %toBool, i8* %arr1.1_base, i8* %bitcast6		; <i8*> [#uses=2]
	%arr1.0.bound = select i1 %toBool, i8* %arr1.1_bound, i8* %bitcast7		; <i8*> [#uses=2]
	%safe.ptr = select i1 %toBool, i32 %safe.phi_node, i32 1		; <i32> [#uses=2]
	%arr1.0 = select i1 %toBool, i32** %arr1.1, i32** %.sub		; <i32**> [#uses=2]
	%bcast_ld_dref_base = bitcast i8* %bitcast3 to i8*		; <i8*> [#uses=1]
	%bitcast423 = bitcast i8* %bitcast4 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound = bitcast i32* %.sub5 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base, i8* %bitcast423, i8* %bcast_ld_dref_bound, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%8 = load i32* %.sub5, align 4		; <i32> [#uses=1]
	%9 = icmp slt i32 %8, %3		; <i1> [#uses=1]
	br i1 %9, label %bb4, label %bb3

bb3:		; preds = %bb, %entry
	%i.0 = phi i32 [ 0, %entry ], [ %3, %bb ]		; <i32> [#uses=3]
	%arr1.1_base = phi i8* [ %bitcast, %entry ], [ %arr1.0.base, %bb ]		; <i8*> [#uses=3]
	%arr1.1_bound = phi i8* [ %bitcast1, %entry ], [ %arr1.0.bound, %bb ]		; <i8*> [#uses=3]
	%safe.phi_node = phi i32 [ 1, %entry ], [ %safe.ptr, %bb ]		; <i32> [#uses=3]
	%arr1.1 = phi i32** [ %.sub6, %entry ], [ %arr1.0, %bb ]		; <i32**> [#uses=5]
	%10 = icmp slt i32 %i.0, %mm		; <i1> [#uses=1]
	br i1 %10, label %bb, label %bb4

bb4:		; preds = %bb3, %bb
	%arr1.2_base = phi i8* [ %arr1.0.base, %bb ], [ %arr1.1_base, %bb3 ]		; <i8*> [#uses=1]
	%arr1.2_bound = phi i8* [ %arr1.0.bound, %bb ], [ %arr1.1_bound, %bb3 ]		; <i8*> [#uses=1]
	%safe.phi_node8 = phi i32 [ %safe.ptr, %bb ], [ %safe.phi_node, %bb3 ]		; <i32> [#uses=1]
	%arr1.2 = phi i32** [ %arr1.0, %bb ], [ %arr1.1, %bb3 ]		; <i32**> [#uses=3]
	%bcast_ld_dref_base24 = bitcast i8* %arr1.2_base to i8*		; <i8*> [#uses=1]
	%arr1.2_bound25 = bitcast i8* %arr1.2_bound to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound26 = bitcast i32** %arr1.2 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base24, i8* %arr1.2_bound25, i8* %bcast_ld_dref_bound26, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 %safe.phi_node8)
	%11 = load i32** %arr1.2, align 4		; <i32*> [#uses=2]
	%arr1.2.ptr = bitcast i32** %arr1.2 to i8*		; <i8*> [#uses=1]
	%.ptrcast = bitcast i32* %11 to i8*		; <i8*> [#uses=1]
	call void @__hashLoadBaseBound(i8* %arr1.2.ptr, i8** %base.alloca, i8** %bound.alloca, i8* %.ptrcast, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32* %safe.ptr9)
	%base.load = load i8** %base.alloca		; <i8*> [#uses=1]
	%bound.load = load i8** %bound.alloca		; <i8*> [#uses=1]
	%safe.ptr.load = load i32* %safe.ptr9		; <i32> [#uses=0]
	%base.load10 = bitcast i8* %base.load to i8*		; <i8*> [#uses=0]
	%bound.load11 = bitcast i8* %bound.load to i8*		; <i8*> [#uses=0]
	%12 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str1, i32 0, i32 0), i32* %11) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
