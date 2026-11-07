; ModuleID = 'passes/mutual.c'
source_filename = "passes/mutual.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @even(i32 noundef %0) #0 !dbg !10 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !15, !DIExpression(), !16)
  %4 = load i32, ptr %3, align 4, !dbg !17
  %5 = icmp eq i32 %4, 0, !dbg !19
  br i1 %5, label %6, label %7, !dbg !20

6:                                                ; preds = %1
  store i32 1, ptr %2, align 4, !dbg !21
  br label %11, !dbg !21

7:                                                ; preds = %1
  %8 = load i32, ptr %3, align 4, !dbg !22
  %9 = sub nsw i32 %8, 1, !dbg !23
  %10 = call i32 @odd(i32 noundef %9), !dbg !24
  store i32 %10, ptr %2, align 4, !dbg !25
  br label %11, !dbg !25

11:                                               ; preds = %7, %6
  %12 = load i32, ptr %2, align 4, !dbg !26
  ret i32 %12, !dbg !26
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @odd(i32 noundef %0) #0 !dbg !27 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !28, !DIExpression(), !29)
  %4 = load i32, ptr %3, align 4, !dbg !30
  %5 = icmp eq i32 %4, 0, !dbg !32
  br i1 %5, label %6, label %7, !dbg !33

6:                                                ; preds = %1
  store i32 0, ptr %2, align 4, !dbg !34
  br label %11, !dbg !34

7:                                                ; preds = %1
  %8 = load i32, ptr %3, align 4, !dbg !35
  %9 = sub nsw i32 %8, 1, !dbg !36
  %10 = call i32 @even(i32 noundef %9), !dbg !37
  store i32 %10, ptr %2, align 4, !dbg !38
  br label %11, !dbg !38

11:                                               ; preds = %7, %6
  %12 = load i32, ptr %2, align 4, !dbg !39
  ret i32 %12, !dbg !39
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !40 {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %2 = call i32 @__VERIFIER_nondet_int(), !dbg !43
  %3 = call i32 @even(i32 noundef %2), !dbg !44
  ret i32 %3, !dbg !45
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "passes/mutual.c", directory: "/w", checksumkind: CSK_MD5, checksum: "65b0307dd599a26700edfb8ab0ae98fb")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!10 = distinct !DISubprogram(name: "even", scope: !1, file: !1, line: 3, type: !11, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{!13, !13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "n", arg: 1, scope: !10, file: !1, line: 3, type: !13)
!16 = !DILocation(line: 3, column: 14, scope: !10)
!17 = !DILocation(line: 3, column: 23, scope: !18)
!18 = distinct !DILexicalBlock(scope: !10, file: !1, line: 3, column: 23)
!19 = !DILocation(line: 3, column: 25, scope: !18)
!20 = !DILocation(line: 3, column: 23, scope: !10)
!21 = !DILocation(line: 3, column: 31, scope: !18)
!22 = !DILocation(line: 3, column: 52, scope: !10)
!23 = !DILocation(line: 3, column: 54, scope: !10)
!24 = !DILocation(line: 3, column: 48, scope: !10)
!25 = !DILocation(line: 3, column: 41, scope: !10)
!26 = !DILocation(line: 3, column: 60, scope: !10)
!27 = distinct !DISubprogram(name: "odd", scope: !1, file: !1, line: 4, type: !11, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!28 = !DILocalVariable(name: "n", arg: 1, scope: !27, file: !1, line: 4, type: !13)
!29 = !DILocation(line: 4, column: 13, scope: !27)
!30 = !DILocation(line: 4, column: 22, scope: !31)
!31 = distinct !DILexicalBlock(scope: !27, file: !1, line: 4, column: 22)
!32 = !DILocation(line: 4, column: 24, scope: !31)
!33 = !DILocation(line: 4, column: 22, scope: !27)
!34 = !DILocation(line: 4, column: 30, scope: !31)
!35 = !DILocation(line: 4, column: 52, scope: !27)
!36 = !DILocation(line: 4, column: 54, scope: !27)
!37 = !DILocation(line: 4, column: 47, scope: !27)
!38 = !DILocation(line: 4, column: 40, scope: !27)
!39 = !DILocation(line: 4, column: 60, scope: !27)
!40 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 5, type: !41, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0)
!41 = !DISubroutineType(types: !42)
!42 = !{!13}
!43 = !DILocation(line: 5, column: 30, scope: !40)
!44 = !DILocation(line: 5, column: 25, scope: !40)
!45 = !DILocation(line: 5, column: 18, scope: !40)
