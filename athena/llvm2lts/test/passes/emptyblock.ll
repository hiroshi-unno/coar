; ModuleID = 'passes/emptyblock.c'
source_filename = "passes/emptyblock.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local void @rec(i32 noundef %0, i32 noundef %1) #0 !dbg !10 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !15, !DIExpression(), !16)
  store i32 %1, ptr %4, align 4
    #dbg_declare(ptr %4, !17, !DIExpression(), !18)
  %5 = load i32, ptr %3, align 4, !dbg !19
  %6 = icmp sle i32 %5, 23, !dbg !21
  br i1 %6, label %7, label %17, !dbg !22

7:                                                ; preds = %2
  %8 = load i32, ptr %3, align 4, !dbg !23
  %9 = icmp sge i32 %8, -42, !dbg !25
  br i1 %9, label %10, label %16, !dbg !26

10:                                               ; preds = %7
  %11 = load i32, ptr %4, align 4, !dbg !27
  %12 = mul nsw i32 2, %11, !dbg !29
  %13 = sub nsw i32 %12, 2, !dbg !30
  %14 = load i32, ptr %3, align 4, !dbg !31
  %15 = add nsw i32 %14, 1, !dbg !32
  call void @rec(i32 noundef %13, i32 noundef %15), !dbg !33
  br label %16, !dbg !34

16:                                               ; preds = %10, %7
  br label %17, !dbg !35

17:                                               ; preds = %16, %2
  ret void, !dbg !36
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !37 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !40, !DIExpression(), !41)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !42
  store i32 %3, ptr %2, align 4, !dbg !41
  %4 = load i32, ptr %2, align 4, !dbg !43
  %5 = load i32, ptr %2, align 4, !dbg !44
  %6 = add nsw i32 %5, 1, !dbg !45
  call void @rec(i32 noundef %4, i32 noundef %6), !dbg !46
  ret i32 0, !dbg !47
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "passes/emptyblock.c", directory: "/w", checksumkind: CSK_MD5, checksum: "36b3af5365e3db2094752e36a31f4b4b")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!10 = distinct !DISubprogram(name: "rec", scope: !1, file: !1, line: 2, type: !11, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{null, !13, !13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "x", arg: 1, scope: !10, file: !1, line: 2, type: !13)
!16 = !DILocation(line: 2, column: 14, scope: !10)
!17 = !DILocalVariable(name: "y", arg: 2, scope: !10, file: !1, line: 2, type: !13)
!18 = !DILocation(line: 2, column: 21, scope: !10)
!19 = !DILocation(line: 4, column: 7, scope: !20)
!20 = distinct !DILexicalBlock(scope: !10, file: !1, line: 4, column: 7)
!21 = !DILocation(line: 4, column: 9, scope: !20)
!22 = !DILocation(line: 4, column: 7, scope: !10)
!23 = !DILocation(line: 5, column: 9, scope: !24)
!24 = distinct !DILexicalBlock(scope: !20, file: !1, line: 5, column: 9)
!25 = !DILocation(line: 5, column: 11, scope: !24)
!26 = !DILocation(line: 5, column: 9, scope: !20)
!27 = !DILocation(line: 6, column: 15, scope: !28)
!28 = distinct !DILexicalBlock(scope: !24, file: !1, line: 5, column: 19)
!29 = !DILocation(line: 6, column: 13, scope: !28)
!30 = !DILocation(line: 6, column: 17, scope: !28)
!31 = !DILocation(line: 6, column: 22, scope: !28)
!32 = !DILocation(line: 6, column: 24, scope: !28)
!33 = !DILocation(line: 6, column: 7, scope: !28)
!34 = !DILocation(line: 7, column: 5, scope: !28)
!35 = !DILocation(line: 5, column: 15, scope: !24)
!36 = !DILocation(line: 8, column: 3, scope: !10)
!37 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 10, type: !38, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!38 = !DISubroutineType(types: !39)
!39 = !{!13}
!40 = !DILocalVariable(name: "n", scope: !37, file: !1, line: 12, type: !13)
!41 = !DILocation(line: 12, column: 7, scope: !37)
!42 = !DILocation(line: 12, column: 11, scope: !37)
!43 = !DILocation(line: 13, column: 7, scope: !37)
!44 = !DILocation(line: 13, column: 10, scope: !37)
!45 = !DILocation(line: 13, column: 12, scope: !37)
!46 = !DILocation(line: 13, column: 3, scope: !37)
!47 = !DILocation(line: 14, column: 3, scope: !37)
