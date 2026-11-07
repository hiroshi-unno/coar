; ModuleID = 'recursive_negation_alternates_false-termination.c'
source_filename = "recursive_negation_alternates_false-termination.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @f(i32 noundef %0) #0 !dbg !10 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !16, !DIExpression(), !17)
  %4 = load i32, ptr %3, align 4, !dbg !18
  %5 = icmp slt i32 %4, 0, !dbg !20
  br i1 %5, label %6, label %10, !dbg !21

6:                                                ; preds = %1
  %7 = load i32, ptr %3, align 4, !dbg !22
  %8 = sub nsw i32 0, %7, !dbg !23
  %9 = call i32 @f(i32 noundef %8), !dbg !24
  store i32 %9, ptr %2, align 4, !dbg !25
  br label %18, !dbg !25

10:                                               ; preds = %1
  %11 = load i32, ptr %3, align 4, !dbg !26
  %12 = icmp eq i32 %11, 0, !dbg !28
  br i1 %12, label %13, label %14, !dbg !29

13:                                               ; preds = %10
  store i32 0, ptr %2, align 4, !dbg !30
  br label %18, !dbg !30

14:                                               ; preds = %10
  %15 = load i32, ptr %3, align 4, !dbg !31
  %16 = sub nsw i32 0, %15, !dbg !32
  %17 = call i32 @f(i32 noundef %16), !dbg !33
  store i32 %17, ptr %2, align 4, !dbg !34
  br label %18, !dbg !34

18:                                               ; preds = %14, %13, %6
  %19 = load i32, ptr %2, align 4, !dbg !35
  ret i32 %19, !dbg !35
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !36 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !39, !DIExpression(), !40)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !41
  store i32 %4, ptr %2, align 4, !dbg !40
    #dbg_declare(ptr %3, !42, !DIExpression(), !43)
  %5 = load i32, ptr %2, align 4, !dbg !44
  %6 = call i32 @f(i32 noundef %5), !dbg !45
  store i32 %6, ptr %3, align 4, !dbg !43
  ret i32 0, !dbg !46
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.1 (1ubuntu1~24.04.2)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "recursive_negation_alternates_false-termination.c", directory: "/home/opam/coar", checksumkind: CSK_MD5, checksum: "41d3e476587c575945aa0ac06298ef42")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.1 (1ubuntu1~24.04.2)"}
!10 = distinct !DISubprogram(name: "f", scope: !11, file: !11, line: 6, type: !12, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !15)
!11 = !DIFile(filename: "recursive_negation_alternates_false-termination.c", directory: "", checksumkind: CSK_MD5, checksum: "41d3e476587c575945aa0ac06298ef42")
!12 = !DISubroutineType(types: !13)
!13 = !{!14, !14}
!14 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!15 = !{}
!16 = !DILocalVariable(name: "m", arg: 1, scope: !10, file: !11, line: 6, type: !14)
!17 = !DILocation(line: 6, column: 11, scope: !10)
!18 = !DILocation(line: 6, column: 20, scope: !19)
!19 = distinct !DILexicalBlock(scope: !10, file: !11, line: 6, column: 20)
!20 = !DILocation(line: 6, column: 22, scope: !19)
!21 = !DILocation(line: 6, column: 20, scope: !10)
!22 = !DILocation(line: 6, column: 37, scope: !19)
!23 = !DILocation(line: 6, column: 36, scope: !19)
!24 = !DILocation(line: 6, column: 34, scope: !19)
!25 = !DILocation(line: 6, column: 27, scope: !19)
!26 = !DILocation(line: 6, column: 45, scope: !27)
!27 = distinct !DILexicalBlock(scope: !10, file: !11, line: 6, column: 45)
!28 = !DILocation(line: 6, column: 47, scope: !27)
!29 = !DILocation(line: 6, column: 45, scope: !10)
!30 = !DILocation(line: 6, column: 53, scope: !27)
!31 = !DILocation(line: 6, column: 73, scope: !10)
!32 = !DILocation(line: 6, column: 72, scope: !10)
!33 = !DILocation(line: 6, column: 70, scope: !10)
!34 = !DILocation(line: 6, column: 63, scope: !10)
!35 = !DILocation(line: 6, column: 77, scope: !10)
!36 = distinct !DISubprogram(name: "main", scope: !11, file: !11, line: 7, type: !37, scopeLine: 7, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !15)
!37 = !DISubroutineType(types: !38)
!38 = !{!14}
!39 = !DILocalVariable(name: "m", scope: !36, file: !11, line: 7, type: !14)
!40 = !DILocation(line: 7, column: 18, scope: !36)
!41 = !DILocation(line: 7, column: 22, scope: !36)
!42 = !DILocalVariable(name: "r", scope: !36, file: !11, line: 7, type: !14)
!43 = !DILocation(line: 7, column: 51, scope: !36)
!44 = !DILocation(line: 7, column: 57, scope: !36)
!45 = !DILocation(line: 7, column: 55, scope: !36)
!46 = !DILocation(line: 7, column: 61, scope: !36)
