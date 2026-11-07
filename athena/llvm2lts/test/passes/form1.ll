; ModuleID = 'passes/form1.c'
source_filename = "passes/form1.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @g(i32 noundef %0, i32 noundef %1) #0 !dbg !10 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 %0, ptr %4, align 4
    #dbg_declare(ptr %4, !15, !DIExpression(), !16)
  store i32 %1, ptr %5, align 4
    #dbg_declare(ptr %5, !17, !DIExpression(), !18)
  %8 = load i32, ptr %4, align 4, !dbg !19
  %9 = icmp sle i32 %8, 0, !dbg !21
  br i1 %9, label %10, label %11, !dbg !22

10:                                               ; preds = %2
  store i32 0, ptr %3, align 4, !dbg !23
  br label %19, !dbg !23

11:                                               ; preds = %2
    #dbg_declare(ptr %6, !24, !DIExpression(), !25)
  %12 = load i32, ptr %4, align 4, !dbg !26
  %13 = sub nsw i32 %12, 1, !dbg !27
  %14 = load i32, ptr %5, align 4, !dbg !28
  %15 = call i32 @g(i32 noundef %13, i32 noundef %14), !dbg !29
  store i32 %15, ptr %6, align 4, !dbg !25
    #dbg_declare(ptr %7, !30, !DIExpression(), !31)
  %16 = load i32, ptr %5, align 4, !dbg !32
  %17 = sdiv i32 100, %16, !dbg !33
  store i32 %17, ptr %7, align 4, !dbg !31
  %18 = load i32, ptr %6, align 4, !dbg !34
  store i32 %18, ptr %3, align 4, !dbg !35
  br label %19, !dbg !35

19:                                               ; preds = %11, %10
  %20 = load i32, ptr %3, align 4, !dbg !36
  ret i32 %20, !dbg !36
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !37 {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %2 = call i32 @__VERIFIER_nondet_int(), !dbg !40
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !41
  %4 = call i32 @g(i32 noundef %2, i32 noundef %3), !dbg !42
  ret i32 %4, !dbg !43
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "passes/form1.c", directory: "/w", checksumkind: CSK_MD5, checksum: "d11257c73bea094c8a91de0172c3542d")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!10 = distinct !DISubprogram(name: "g", scope: !1, file: !1, line: 2, type: !11, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{!13, !13, !13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "n", arg: 1, scope: !10, file: !1, line: 2, type: !13)
!16 = !DILocation(line: 2, column: 11, scope: !10)
!17 = !DILocalVariable(name: "d", arg: 2, scope: !10, file: !1, line: 2, type: !13)
!18 = !DILocation(line: 2, column: 18, scope: !10)
!19 = !DILocation(line: 3, column: 7, scope: !20)
!20 = distinct !DILexicalBlock(scope: !10, file: !1, line: 3, column: 7)
!21 = !DILocation(line: 3, column: 9, scope: !20)
!22 = !DILocation(line: 3, column: 7, scope: !10)
!23 = !DILocation(line: 3, column: 15, scope: !20)
!24 = !DILocalVariable(name: "r", scope: !10, file: !1, line: 4, type: !13)
!25 = !DILocation(line: 4, column: 7, scope: !10)
!26 = !DILocation(line: 4, column: 13, scope: !10)
!27 = !DILocation(line: 4, column: 15, scope: !10)
!28 = !DILocation(line: 4, column: 20, scope: !10)
!29 = !DILocation(line: 4, column: 11, scope: !10)
!30 = !DILocalVariable(name: "unused", scope: !10, file: !1, line: 5, type: !13)
!31 = !DILocation(line: 5, column: 7, scope: !10)
!32 = !DILocation(line: 5, column: 22, scope: !10)
!33 = !DILocation(line: 5, column: 20, scope: !10)
!34 = !DILocation(line: 6, column: 10, scope: !10)
!35 = !DILocation(line: 6, column: 3, scope: !10)
!36 = !DILocation(line: 7, column: 1, scope: !10)
!37 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 8, type: !38, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0)
!38 = !DISubroutineType(types: !39)
!39 = !{!13}
!40 = !DILocation(line: 8, column: 27, scope: !37)
!41 = !DILocation(line: 8, column: 52, scope: !37)
!42 = !DILocation(line: 8, column: 25, scope: !37)
!43 = !DILocation(line: 8, column: 18, scope: !37)
