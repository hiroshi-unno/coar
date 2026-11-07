; ModuleID = 'rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.c'
source_filename = "rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.src = private unnamed_addr constant [79 x i8] c"rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.c\00", align 1
@0 = private unnamed_addr constant { i16, i16, [6 x i8] } { i16 0, i16 11, [6 x i8] c"'int'\00" }

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !15, !DIExpression(), !16)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !17
  store i32 %4, ptr %2, align 4, !dbg !16
  %5 = load i32, ptr %2, align 4, !dbg !18
  %6 = icmp slt i32 %5, 1073741824, !dbg !20
  br i1 %6, label %7, label %8, !dbg !21

7:                                                ; preds = %0
  store i32 0, ptr %1, align 4, !dbg !22
  br label %23, !dbg !22

8:                                                ; preds = %0
    #dbg_declare(ptr %3, !23, !DIExpression(), !24)
  %9 = load i32, ptr %2, align 4, !dbg !25
  br i1 true, label %10, label %13, !dbg !26, !nosanitize !14

10:                                               ; preds = %8
  %11 = lshr i32 %9, 30, !dbg !26, !nosanitize !14
  %12 = icmp eq i32 %11, 0, !dbg !26, !nosanitize !14
  br label %13, !dbg !26, !nosanitize !14

13:                                               ; preds = %10, %8
  %14 = phi i1 [ true, %8 ], [ %12, %10 ], !dbg !26, !nosanitize !14
  br i1 %14, label %16, label %15, !dbg !26, !nosanitize !14

15:                                               ; preds = %13
  call void @llvm.ubsantrap(i8 20) #3, !dbg !26, !nosanitize !14
  unreachable, !dbg !26, !nosanitize !14

16:                                               ; preds = %13
  %17 = shl i32 %9, 1, !dbg !26
  store i32 %17, ptr %3, align 4, !dbg !24
  br label %18, !dbg !27

18:                                               ; preds = %21, %16
  %19 = load i32, ptr %3, align 4, !dbg !28
  %20 = icmp sgt i32 %19, 0, !dbg !29
  br i1 %20, label %21, label %22, !dbg !27

21:                                               ; preds = %18
  br label %18, !dbg !27, !llvm.loop !30

22:                                               ; preds = %18
  store i32 0, ptr %1, align 4, !dbg !32
  br label %23, !dbg !32

23:                                               ; preds = %22, %7
  %24 = load i32, ptr %1, align 4, !dbg !33
  ret i32 %24, !dbg !33
}

declare i32 @__VERIFIER_nondet_int() #1

; Function Attrs: cold noreturn nounwind
declare void @llvm.ubsantrap(i8 immarg) #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { cold noreturn nounwind }
attributes #3 = { noreturn nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.c", directory: "/w", checksumkind: CSK_MD5, checksum: "c94213f38ddd11475b580e8c3592bee8")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!10 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 5, type: !11, scopeLine: 5, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{!13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "x", scope: !10, file: !1, line: 6, type: !13)
!16 = !DILocation(line: 6, column: 7, scope: !10)
!17 = !DILocation(line: 6, column: 11, scope: !10)
!18 = !DILocation(line: 7, column: 7, scope: !19)
!19 = distinct !DILexicalBlock(scope: !10, file: !1, line: 7, column: 7)
!20 = !DILocation(line: 7, column: 9, scope: !19)
!21 = !DILocation(line: 7, column: 7, scope: !10)
!22 = !DILocation(line: 7, column: 23, scope: !19)
!23 = !DILocalVariable(name: "y", scope: !10, file: !1, line: 8, type: !13)
!24 = !DILocation(line: 8, column: 7, scope: !10)
!25 = !DILocation(line: 8, column: 11, scope: !10)
!26 = !DILocation(line: 8, column: 13, scope: !10)
!27 = !DILocation(line: 9, column: 3, scope: !10)
!28 = !DILocation(line: 9, column: 10, scope: !10)
!29 = !DILocation(line: 9, column: 12, scope: !10)
!30 = distinct !{!30, !27, !31}
!31 = !DILocation(line: 9, column: 19, scope: !10)
!32 = !DILocation(line: 10, column: 3, scope: !10)
!33 = !DILocation(line: 11, column: 1, scope: !10)
