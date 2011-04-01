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
	%base.alloca14 = alloca i8*		; <i8**> [#uses=2]
	%bound.alloca15 = alloca i8*		; <i8**> [#uses=2]
	%safe.ptr17 = alloca i32		; <i32*> [#uses=2]
	%base.alloca = alloca i8*		; <i8**> [#uses=2]
	%bound.alloca = alloca i8*		; <i8**> [#uses=2]
	%safe.ptr = alloca i32		; <i32*> [#uses=2]
	%0 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=3]
	%malloc_bound = getelementptr [100 x i32*]* %0, i32 1		; <[100 x i32*]*> [#uses=1]
	%bitcast = bitcast [100 x i32*]* %0 to i8*		; <i8*> [#uses=1]
	%bitcast1 = bitcast [100 x i32*]* %malloc_bound to i8*		; <i8*> [#uses=1]
	%.sub8 = getelementptr [100 x i32*]* %0, i32 0, i32 0		; <i32**> [#uses=1]
	%1 = add i32 %mm, 1		; <i32> [#uses=2]
	br label %bb6

bb:		; preds = %bb6
	%2 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=4]
	%malloc_bound4 = getelementptr [100 x i32*]* %2, i32 1		; <[100 x i32*]*> [#uses=1]
	%bitcast5 = bitcast [100 x i32*]* %2 to i8*		; <i8*> [#uses=2]
	%bitcast6 = bitcast [100 x i32*]* %malloc_bound4 to i8*		; <i8*> [#uses=2]
	%.sub = getelementptr [100 x i32*]* %2, i32 0, i32 0		; <i32**> [#uses=1]
	%3 = icmp sgt i32 %1, %i.1		; <i1> [#uses=1]
	br i1 %3, label %bb.nph, label %bb3

bb.nph:		; preds = %bb
	%i.010 = add i32 %i.1, 1		; <i32> [#uses=1]
	%tmp20 = sub i32 %mm, %i.1		; <i32> [#uses=1]
	%tmp21 = add i32 %tmp20, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %bb1, %bb.nph
	%indvar = phi i32 [ 0, %bb.nph ], [ %indvar.next19, %bb1 ]		; <i32> [#uses=2]
	%.sum = add i32 %i.010, %indvar		; <i32> [#uses=1]
	%4 = getelementptr [100 x i32*]* %2, i32 0, i32 %.sum		; <i32**> [#uses=3]
	%bcast_ld_dref_base27 = bitcast i8* %bitcast5 to i8*		; <i8*> [#uses=1]
	%bitcast628 = bitcast i8* %bitcast6 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound29 = bitcast i32** %4 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base27, i8* %bitcast628, i8* %bcast_ld_dref_bound29, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 1)
	%5 = load i32** %4, align 4		; <i32*> [#uses=2]
	%.ptr13 = bitcast i32** %4 to i8*		; <i8*> [#uses=1]
	%.ptrcast16 = bitcast i32* %5 to i8*		; <i8*> [#uses=1]
	call void @__hashLoadBaseBound(i8* %.ptr13, i8** %base.alloca14, i8** %bound.alloca15, i8* %.ptrcast16, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32* %safe.ptr17)
	%base.load18 = load i8** %base.alloca14		; <i8*> [#uses=1]
	%bound.load19 = load i8** %bound.alloca15		; <i8*> [#uses=1]
	%safe.ptr.load20 = load i32* %safe.ptr17		; <i32> [#uses=1]
	%base.load1821 = bitcast i8* %base.load18 to i8*		; <i8*> [#uses=1]
	%bound.load1922 = bitcast i8* %bound.load19 to i8*		; <i8*> [#uses=1]
	%indvar.next19 = add i32 %indvar, 1		; <i32> [#uses=2]
	%exitcond22 = icmp eq i32 %indvar.next19, %tmp21		; <i1> [#uses=1]
	br i1 %exitcond22, label %bb3, label %bb1

bb3:		; preds = %bb1, %bb
	%i.0.lcssa = phi i32 [ %i.1, %bb ], [ %1, %bb1 ]		; <i32> [#uses=2]
	%ptr2.0.lcssa_base = phi i8* [ %ptr2.1_base, %bb ], [ %base.load1821, %bb1 ]		; <i8*> [#uses=2]
	%ptr2.0.lcssa_bound = phi i8* [ %ptr2.1_bound, %bb ], [ %bound.load1922, %bb1 ]		; <i8*> [#uses=2]
	%safe.phi_node9 = phi i32 [ %safe.phi_node, %bb ], [ %safe.ptr.load20, %bb1 ]		; <i32> [#uses=2]
	%ptr2.0.lcssa = phi i32* [ %ptr2.1, %bb ], [ %5, %bb1 ]		; <i32*> [#uses=2]
	%6 = getelementptr i32** %arr1.1, i32 %i.0.lcssa		; <i32**> [#uses=3]
	%bcast_ld_dref_base = bitcast i8* %arr1.1_base to i8*		; <i8*> [#uses=1]
	%arr1.1_bound23 = bitcast i8* %arr1.1_bound to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound = bitcast i32** %6 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base, i8* %arr1.1_bound23, i8* %bcast_ld_dref_bound, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 1)
	%7 = load i32** %6, align 4		; <i32*> [#uses=5]
	%.ptr = bitcast i32** %6 to i8*		; <i8*> [#uses=1]
	%.ptrcast = bitcast i32* %7 to i8*		; <i8*> [#uses=1]
	call void @__hashLoadBaseBound(i8* %.ptr, i8** %base.alloca, i8** %bound.alloca, i8* %.ptrcast, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32* %safe.ptr)
	%base.load = load i8** %base.alloca		; <i8*> [#uses=1]
	%bound.load = load i8** %bound.alloca		; <i8*> [#uses=1]
	%safe.ptr.load = load i32* %safe.ptr		; <i32> [#uses=3]
	%base.load10 = bitcast i8* %base.load to i8*		; <i8*> [#uses=3]
	%bound.load11 = bitcast i8* %bound.load to i8*		; <i8*> [#uses=3]
	%8 = add i32 %i.0.lcssa, 1		; <i32> [#uses=3]
	%9 = and i32 %8, 1		; <i32> [#uses=1]
	%toBool = icmp eq i32 %9, 0		; <i1> [#uses=4]
	%arr1.0.base = select i1 %toBool, i8* %arr1.1_base, i8* %bitcast5		; <i8*> [#uses=1]
	%arr1.0.bound = select i1 %toBool, i8* %arr1.1_bound, i8* %bitcast6		; <i8*> [#uses=1]
	%safe.ptr12 = select i1 %toBool, i32 %safe.phi_node3, i32 1		; <i32> [#uses=1]
	%arr1.0 = select i1 %toBool, i32** %arr1.1, i32** %.sub		; <i32**> [#uses=1]
	%bcast_ld_dref_base24 = bitcast i8* %base.load10 to i8*		; <i8*> [#uses=1]
	%bound.load1125 = bitcast i8* %bound.load11 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound26 = bitcast i32* %7 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base24, i8* %bound.load1125, i8* %bcast_ld_dref_bound26, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 %safe.ptr.load)
	%10 = load i32* %7, align 4		; <i32> [#uses=1]
	%11 = icmp slt i32 %10, %8		; <i1> [#uses=1]
	br i1 %11, label %bb7, label %bb6

bb6:		; preds = %bb3, %entry
	%ptr2.1_base = phi i8* [ undef, %entry ], [ %ptr2.0.lcssa_base, %bb3 ]		; <i8*> [#uses=2]
	%ptr2.1_bound = phi i8* [ undef, %entry ], [ %ptr2.0.lcssa_bound, %bb3 ]		; <i8*> [#uses=2]
	%safe.phi_node = phi i32 [ 0, %entry ], [ %safe.phi_node9, %bb3 ]		; <i32> [#uses=2]
	%ptr2.1 = phi i32* [ undef, %entry ], [ %ptr2.0.lcssa, %bb3 ]		; <i32*> [#uses=2]
	%i.1 = phi i32 [ 0, %entry ], [ %8, %bb3 ]		; <i32> [#uses=5]
	%ptr1.0_base = phi i8* [ undef, %entry ], [ %base.load10, %bb3 ]		; <i8*> [#uses=1]
	%ptr1.0_bound = phi i8* [ undef, %entry ], [ %bound.load11, %bb3 ]		; <i8*> [#uses=1]
	%safe.phi_node2 = phi i32 [ 0, %entry ], [ %safe.ptr.load, %bb3 ]		; <i32> [#uses=1]
	%ptr1.0 = phi i32* [ undef, %entry ], [ %7, %bb3 ]		; <i32*> [#uses=1]
	%arr1.1_base = phi i8* [ %bitcast, %entry ], [ %arr1.0.base, %bb3 ]		; <i8*> [#uses=2]
	%arr1.1_bound = phi i8* [ %bitcast1, %entry ], [ %arr1.0.bound, %bb3 ]		; <i8*> [#uses=2]
	%safe.phi_node3 = phi i32 [ 1, %entry ], [ %safe.ptr12, %bb3 ]		; <i32> [#uses=1]
	%arr1.1 = phi i32** [ %.sub8, %entry ], [ %arr1.0, %bb3 ]		; <i32**> [#uses=2]
	%12 = icmp slt i32 %i.1, %mm		; <i1> [#uses=1]
	br i1 %12, label %bb, label %bb7

bb7:		; preds = %bb6, %bb3
	%ptr2.2_base = phi i8* [ %ptr2.0.lcssa_base, %bb3 ], [ %ptr2.1_base, %bb6 ]		; <i8*> [#uses=0]
	%ptr2.2_bound = phi i8* [ %ptr2.0.lcssa_bound, %bb3 ], [ %ptr2.1_bound, %bb6 ]		; <i8*> [#uses=0]
	%safe.phi_node7 = phi i32 [ %safe.phi_node9, %bb3 ], [ %safe.phi_node, %bb6 ]		; <i32> [#uses=0]
	%ptr2.2 = phi i32* [ %ptr2.0.lcssa, %bb3 ], [ %ptr2.1, %bb6 ]		; <i32*> [#uses=1]
	%ptr1.1_base = phi i8* [ %base.load10, %bb3 ], [ %ptr1.0_base, %bb6 ]		; <i8*> [#uses=0]
	%ptr1.1_bound = phi i8* [ %bound.load11, %bb3 ], [ %ptr1.0_bound, %bb6 ]		; <i8*> [#uses=0]
	%safe.phi_node8 = phi i32 [ %safe.ptr.load, %bb3 ], [ %safe.phi_node2, %bb6 ]		; <i32> [#uses=0]
	%ptr1.1 = phi i32* [ %7, %bb3 ], [ %ptr1.0, %bb6 ]		; <i32*> [#uses=1]
	%13 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str1, i32 0, i32 0), i32* %ptr1.1) nounwind		; <i32> [#uses=0]
	%14 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str1, i32 0, i32 0), i32* %ptr2.2) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
