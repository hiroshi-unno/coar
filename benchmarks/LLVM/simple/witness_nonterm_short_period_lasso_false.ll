; ModuleID = 'witness_nonterm_short_period_lasso_false.c'
source_filename = "witness_nonterm_short_period_lasso_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !15, !DIExpression(), !16)
  store i32 0, ptr %2, align 4, !dbg !16
    #dbg_declare(ptr %3, !17, !DIExpression(), !18)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !19
  store i32 %4, ptr %3, align 4, !dbg !18
  br label %5, !dbg !20

5:                                                ; preds = %14, %0
  %6 = load i32, ptr %3, align 4, !dbg !21
  %7 = icmp sgt i32 %6, 0, !dbg !22
  br i1 %7, label %8, label %15, !dbg !20

8:                                                ; preds = %5
  %9 = load i32, ptr %2, align 4, !dbg !23
  %10 = add nsw i32 %9, 1, !dbg !25
  store i32 %10, ptr %2, align 4, !dbg !26
  %11 = load i32, ptr %2, align 4, !dbg !27
  %12 = icmp eq i32 %11, 4, !dbg !29
  br i1 %12, label %13, label %14, !dbg !30

13:                                               ; preds = %8
  store i32 0, ptr %2, align 4, !dbg !31
  br label %14, !dbg !33

14:                                               ; preds = %13, %8
  br label %5, !dbg !20, !llvm.loop !34

15:                                               ; preds = %5
  ret i32 0, !dbg !36
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "witness_nonterm_short_period_lasso_false.c", directory: ".", checksumkind: CSK_MD5, checksum: "9e474a0ef249863aee244dd28ef13c04")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!10 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 2, type: !11, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{!13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "i", scope: !10, file: !1, line: 3, type: !13)
!16 = !DILocation(line: 3, column: 7, scope: !10)
!17 = !DILocalVariable(name: "k", scope: !10, file: !1, line: 4, type: !13)
!18 = !DILocation(line: 4, column: 7, scope: !10)
!19 = !DILocation(line: 4, column: 11, scope: !10)
!20 = !DILocation(line: 5, column: 3, scope: !10)
!21 = !DILocation(line: 5, column: 10, scope: !10)
!22 = !DILocation(line: 5, column: 12, scope: !10)
!23 = !DILocation(line: 6, column: 9, scope: !24)
!24 = distinct !DILexicalBlock(scope: !10, file: !1, line: 5, column: 17)
!25 = !DILocation(line: 6, column: 11, scope: !24)
!26 = !DILocation(line: 6, column: 7, scope: !24)
!27 = !DILocation(line: 7, column: 9, scope: !28)
!28 = distinct !DILexicalBlock(scope: !24, file: !1, line: 7, column: 9)
!29 = !DILocation(line: 7, column: 11, scope: !28)
!30 = !DILocation(line: 7, column: 9, scope: !24)
!31 = !DILocation(line: 8, column: 9, scope: !32)
!32 = distinct !DILexicalBlock(scope: !28, file: !1, line: 7, column: 17)
!33 = !DILocation(line: 9, column: 5, scope: !32)
!34 = distinct !{!34, !20, !35}
!35 = !DILocation(line: 10, column: 3, scope: !10)
!36 = !DILocation(line: 11, column: 3, scope: !10)
