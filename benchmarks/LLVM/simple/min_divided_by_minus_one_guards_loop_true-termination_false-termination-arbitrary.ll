; ModuleID = 'min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.c'
source_filename = "min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !15, !DIExpression(), !16)
  %5 = call i32 @__VERIFIER_nondet_int(), !dbg !17
  store i32 %5, ptr %2, align 4, !dbg !16
    #dbg_declare(ptr %3, !18, !DIExpression(), !19)
  %6 = call i32 @__VERIFIER_nondet_int(), !dbg !20
  store i32 %6, ptr %3, align 4, !dbg !19
  %7 = load i32, ptr %3, align 4, !dbg !21
  %8 = icmp ne i32 %7, -1, !dbg !23
  br i1 %8, label %9, label %10, !dbg !24

9:                                                ; preds = %0
  store i32 0, ptr %1, align 4, !dbg !25
  br label %23, !dbg !25

10:                                               ; preds = %0
    #dbg_declare(ptr %4, !26, !DIExpression(), !27)
  %11 = load i32, ptr %2, align 4, !dbg !28
  %12 = load i32, ptr %3, align 4, !dbg !29
  %13 = sdiv i32 %11, %12, !dbg !30
  store i32 %13, ptr %4, align 4, !dbg !27
  %14 = load i32, ptr %2, align 4, !dbg !31
  %15 = icmp eq i32 %14, -2147483648, !dbg !33
  br i1 %15, label %16, label %22, !dbg !34

16:                                               ; preds = %10
  br label %17, !dbg !35

17:                                               ; preds = %20, %16
  %18 = load i32, ptr %4, align 4, !dbg !36
  %19 = icmp sgt i32 %18, 0, !dbg !37
  br i1 %19, label %20, label %21, !dbg !35

20:                                               ; preds = %17
  br label %17, !dbg !35, !llvm.loop !38

21:                                               ; preds = %17
  br label %22, !dbg !35

22:                                               ; preds = %21, %10
  store i32 0, ptr %1, align 4, !dbg !40
  br label %23, !dbg !40

23:                                               ; preds = %22, %9
  %24 = load i32, ptr %1, align 4, !dbg !41
  ret i32 %24, !dbg !41
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.c", directory: "/w", checksumkind: CSK_MD5, checksum: "01d20719fb75e7a1516e5337a8366911")
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
!18 = !DILocalVariable(name: "y", scope: !10, file: !1, line: 7, type: !13)
!19 = !DILocation(line: 7, column: 7, scope: !10)
!20 = !DILocation(line: 7, column: 11, scope: !10)
!21 = !DILocation(line: 8, column: 7, scope: !22)
!22 = distinct !DILexicalBlock(scope: !10, file: !1, line: 8, column: 7)
!23 = !DILocation(line: 8, column: 9, scope: !22)
!24 = !DILocation(line: 8, column: 7, scope: !10)
!25 = !DILocation(line: 8, column: 16, scope: !22)
!26 = !DILocalVariable(name: "q", scope: !10, file: !1, line: 9, type: !13)
!27 = !DILocation(line: 9, column: 7, scope: !10)
!28 = !DILocation(line: 9, column: 11, scope: !10)
!29 = !DILocation(line: 9, column: 15, scope: !10)
!30 = !DILocation(line: 9, column: 13, scope: !10)
!31 = !DILocation(line: 10, column: 7, scope: !32)
!32 = distinct !DILexicalBlock(scope: !10, file: !1, line: 10, column: 7)
!33 = !DILocation(line: 10, column: 9, scope: !32)
!34 = !DILocation(line: 10, column: 7, scope: !10)
!35 = !DILocation(line: 11, column: 5, scope: !32)
!36 = !DILocation(line: 11, column: 12, scope: !32)
!37 = !DILocation(line: 11, column: 14, scope: !32)
!38 = distinct !{!38, !35, !39}
!39 = !DILocation(line: 11, column: 21, scope: !32)
!40 = !DILocation(line: 12, column: 3, scope: !10)
!41 = !DILocation(line: 13, column: 1, scope: !10)
