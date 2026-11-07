; ModuleID = 'witness_nonterm_recurrent_false.c'
source_filename = "witness_nonterm_recurrent_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !15, !DIExpression(), !17)
  %3 = call i32 @__VERIFIER_nondet_uint(), !dbg !18
  store i32 %3, ptr %2, align 4, !dbg !17
  %4 = load i32, ptr %2, align 4, !dbg !19
  %5 = urem i32 %4, 2, !dbg !21
  %6 = icmp eq i32 %5, 1, !dbg !22
  br i1 %6, label %7, label %15, !dbg !23

7:                                                ; preds = %0
  br label %8, !dbg !24

8:                                                ; preds = %11, %7
  %9 = load i32, ptr %2, align 4, !dbg !26
  %10 = icmp ne i32 %9, 0, !dbg !27
  br i1 %10, label %11, label %14, !dbg !24

11:                                               ; preds = %8
  %12 = load i32, ptr %2, align 4, !dbg !28
  %13 = add i32 %12, 2, !dbg !30
  store i32 %13, ptr %2, align 4, !dbg !31
  br label %8, !dbg !24, !llvm.loop !32

14:                                               ; preds = %8
  br label %15, !dbg !34

15:                                               ; preds = %14, %0
  ret i32 0, !dbg !35
}

declare i32 @__VERIFIER_nondet_uint() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "witness_nonterm_recurrent_false.c", directory: ".", checksumkind: CSK_MD5, checksum: "e1d460f43e076916fe416aaf04537438")
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
!15 = !DILocalVariable(name: "x", scope: !10, file: !1, line: 3, type: !16)
!16 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!17 = !DILocation(line: 3, column: 16, scope: !10)
!18 = !DILocation(line: 3, column: 20, scope: !10)
!19 = !DILocation(line: 4, column: 7, scope: !20)
!20 = distinct !DILexicalBlock(scope: !10, file: !1, line: 4, column: 7)
!21 = !DILocation(line: 4, column: 9, scope: !20)
!22 = !DILocation(line: 4, column: 13, scope: !20)
!23 = !DILocation(line: 4, column: 7, scope: !10)
!24 = !DILocation(line: 5, column: 5, scope: !25)
!25 = distinct !DILexicalBlock(scope: !20, file: !1, line: 4, column: 19)
!26 = !DILocation(line: 5, column: 12, scope: !25)
!27 = !DILocation(line: 5, column: 14, scope: !25)
!28 = !DILocation(line: 6, column: 11, scope: !29)
!29 = distinct !DILexicalBlock(scope: !25, file: !1, line: 5, column: 20)
!30 = !DILocation(line: 6, column: 13, scope: !29)
!31 = !DILocation(line: 6, column: 9, scope: !29)
!32 = distinct !{!32, !24, !33}
!33 = !DILocation(line: 7, column: 5, scope: !25)
!34 = !DILocation(line: 8, column: 3, scope: !25)
!35 = !DILocation(line: 9, column: 3, scope: !10)
