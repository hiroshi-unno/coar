; ModuleID = 'witness_nonterm_lasso_false.c'
source_filename = "witness_nonterm_lasso_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !15, !DIExpression(), !16)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !17
  store i32 %3, ptr %2, align 4, !dbg !16
  br label %4, !dbg !18

4:                                                ; preds = %13, %0
  %5 = load i32, ptr %2, align 4, !dbg !19
  %6 = icmp sgt i32 %5, 0, !dbg !20
  br i1 %6, label %7, label %14, !dbg !18

7:                                                ; preds = %4
  %8 = load i32, ptr %2, align 4, !dbg !21
  %9 = icmp ne i32 %8, 5, !dbg !24
  br i1 %9, label %10, label %13, !dbg !25

10:                                               ; preds = %7
  %11 = load i32, ptr %2, align 4, !dbg !26
  %12 = sub nsw i32 %11, 1, !dbg !28
  store i32 %12, ptr %2, align 4, !dbg !29
  br label %13, !dbg !30

13:                                               ; preds = %10, %7
  br label %4, !dbg !18, !llvm.loop !31

14:                                               ; preds = %4
  ret i32 0, !dbg !33
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "witness_nonterm_lasso_false.c", directory: ".", checksumkind: CSK_MD5, checksum: "a88f16983870ee67a3611e463205cb2c")
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
!17 = !DILocation(line: 3, column: 11, scope: !10)
!18 = !DILocation(line: 4, column: 3, scope: !10)
!19 = !DILocation(line: 4, column: 10, scope: !10)
!20 = !DILocation(line: 4, column: 12, scope: !10)
!21 = !DILocation(line: 5, column: 9, scope: !22)
!22 = distinct !DILexicalBlock(scope: !23, file: !1, line: 5, column: 9)
!23 = distinct !DILexicalBlock(scope: !10, file: !1, line: 4, column: 17)
!24 = !DILocation(line: 5, column: 11, scope: !22)
!25 = !DILocation(line: 5, column: 9, scope: !23)
!26 = !DILocation(line: 6, column: 11, scope: !27)
!27 = distinct !DILexicalBlock(scope: !22, file: !1, line: 5, column: 17)
!28 = !DILocation(line: 6, column: 13, scope: !27)
!29 = !DILocation(line: 6, column: 9, scope: !27)
!30 = !DILocation(line: 7, column: 5, scope: !27)
!31 = distinct !{!31, !18, !32}
!32 = !DILocation(line: 8, column: 3, scope: !10)
!33 = !DILocation(line: 9, column: 3, scope: !10)
