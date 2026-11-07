; ModuleID = 'passes/loopvar.c'
source_filename = "passes/loopvar.c"
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
  store i32 0, ptr %2, align 4, !dbg !16
    #dbg_declare(ptr %3, !17, !DIExpression(), !19)
  store i32 0, ptr %3, align 4, !dbg !19
  br label %5, !dbg !20

5:                                                ; preds = %16, %0
  %6 = load i32, ptr %3, align 4, !dbg !21
  %7 = icmp slt i32 %6, 3, !dbg !23
  br i1 %7, label %8, label %19, !dbg !24

8:                                                ; preds = %5
    #dbg_declare(ptr %4, !25, !DIExpression(), !27)
  %9 = call i32 @__VERIFIER_nondet_int(), !dbg !28
  %10 = icmp ne i32 %9, 0, !dbg !28
  br i1 %10, label %11, label %12, !dbg !30

11:                                               ; preds = %8
  store i32 1, ptr %4, align 4, !dbg !31
  br label %12, !dbg !32

12:                                               ; preds = %11, %8
  %13 = load i32, ptr %4, align 4, !dbg !33
  %14 = load i32, ptr %2, align 4, !dbg !34
  %15 = add nsw i32 %14, %13, !dbg !34
  store i32 %15, ptr %2, align 4, !dbg !34
  br label %16, !dbg !35

16:                                               ; preds = %12
  %17 = load i32, ptr %3, align 4, !dbg !36
  %18 = add nsw i32 %17, 1, !dbg !36
  store i32 %18, ptr %3, align 4, !dbg !36
  br label %5, !dbg !37, !llvm.loop !38

19:                                               ; preds = %5
  %20 = load i32, ptr %2, align 4, !dbg !40
  ret i32 %20, !dbg !41
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "passes/loopvar.c", directory: "/w", checksumkind: CSK_MD5, checksum: "e5d32e05f049338dfa8cc0bebb9d0ef2")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!10 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 2, type: !11, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{!13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "s", scope: !10, file: !1, line: 3, type: !13)
!16 = !DILocation(line: 3, column: 7, scope: !10)
!17 = !DILocalVariable(name: "i", scope: !18, file: !1, line: 4, type: !13)
!18 = distinct !DILexicalBlock(scope: !10, file: !1, line: 4, column: 3)
!19 = !DILocation(line: 4, column: 12, scope: !18)
!20 = !DILocation(line: 4, column: 8, scope: !18)
!21 = !DILocation(line: 4, column: 19, scope: !22)
!22 = distinct !DILexicalBlock(scope: !18, file: !1, line: 4, column: 3)
!23 = !DILocation(line: 4, column: 21, scope: !22)
!24 = !DILocation(line: 4, column: 3, scope: !18)
!25 = !DILocalVariable(name: "x", scope: !26, file: !1, line: 5, type: !13)
!26 = distinct !DILexicalBlock(scope: !22, file: !1, line: 4, column: 31)
!27 = !DILocation(line: 5, column: 9, scope: !26)
!28 = !DILocation(line: 6, column: 9, scope: !29)
!29 = distinct !DILexicalBlock(scope: !26, file: !1, line: 6, column: 9)
!30 = !DILocation(line: 6, column: 9, scope: !26)
!31 = !DILocation(line: 6, column: 36, scope: !29)
!32 = !DILocation(line: 6, column: 34, scope: !29)
!33 = !DILocation(line: 7, column: 10, scope: !26)
!34 = !DILocation(line: 7, column: 7, scope: !26)
!35 = !DILocation(line: 8, column: 3, scope: !26)
!36 = !DILocation(line: 4, column: 27, scope: !22)
!37 = !DILocation(line: 4, column: 3, scope: !22)
!38 = distinct !{!38, !24, !39}
!39 = !DILocation(line: 8, column: 3, scope: !18)
!40 = !DILocation(line: 9, column: 10, scope: !10)
!41 = !DILocation(line: 9, column: 3, scope: !10)
