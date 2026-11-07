; ModuleID = 'ptr2arr/cut_true.c'
source_filename = "ptr2arr/cut_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local void @__ptr2arr_assume(i32 noundef %0) #0 !dbg !10 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !15, !DIExpression(), !16)
  %3 = load i32, ptr %2, align 4, !dbg !17
  %4 = icmp ne i32 %3, 0, !dbg !17
  br i1 %4, label %6, label %5, !dbg !19

5:                                                ; preds = %1
  call void @_Exit(i32 noundef 0) #3, !dbg !20
  unreachable, !dbg !20

6:                                                ; preds = %1
  ret void, !dbg !21
}

; Function Attrs: noreturn
declare void @_Exit(i32 noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !22 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !25, !DIExpression(), !26)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !27
  store i32 %3, ptr %2, align 4, !dbg !26
  %4 = load i32, ptr %2, align 4, !dbg !28
  %5 = icmp sge i32 %4, 0, !dbg !29
  %6 = zext i1 %5 to i32, !dbg !29
  call void @__ptr2arr_assume(i32 noundef %6), !dbg !30
  br label %7, !dbg !31

7:                                                ; preds = %10, %0
  %8 = load i32, ptr %2, align 4, !dbg !32
  %9 = icmp ne i32 %8, 0, !dbg !33
  br i1 %9, label %10, label %13, !dbg !31

10:                                               ; preds = %7
  %11 = load i32, ptr %2, align 4, !dbg !34
  %12 = add nsw i32 %11, -1, !dbg !34
  store i32 %12, ptr %2, align 4, !dbg !34
  br label %7, !dbg !31, !llvm.loop !35

13:                                               ; preds = %7
  ret i32 0, !dbg !36
}

declare i32 @__VERIFIER_nondet_int() #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "ptr2arr/cut_true.c", directory: "/t", checksumkind: CSK_MD5, checksum: "ad08cc346457bf6b054fa0436fb64f58")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!10 = distinct !DISubprogram(name: "__ptr2arr_assume", scope: !1, file: !1, line: 6, type: !11, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!11 = !DISubroutineType(types: !12)
!12 = !{null, !13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{}
!15 = !DILocalVariable(name: "c", arg: 1, scope: !10, file: !1, line: 6, type: !13)
!16 = !DILocation(line: 6, column: 27, scope: !10)
!17 = !DILocation(line: 6, column: 37, scope: !18)
!18 = distinct !DILexicalBlock(scope: !10, file: !1, line: 6, column: 36)
!19 = !DILocation(line: 6, column: 36, scope: !10)
!20 = !DILocation(line: 6, column: 40, scope: !18)
!21 = !DILocation(line: 6, column: 50, scope: !10)
!22 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 7, type: !23, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !14)
!23 = !DISubroutineType(types: !24)
!24 = !{!13}
!25 = !DILocalVariable(name: "x", scope: !22, file: !1, line: 8, type: !13)
!26 = !DILocation(line: 8, column: 7, scope: !22)
!27 = !DILocation(line: 8, column: 11, scope: !22)
!28 = !DILocation(line: 9, column: 20, scope: !22)
!29 = !DILocation(line: 9, column: 22, scope: !22)
!30 = !DILocation(line: 9, column: 3, scope: !22)
!31 = !DILocation(line: 10, column: 3, scope: !22)
!32 = !DILocation(line: 10, column: 10, scope: !22)
!33 = !DILocation(line: 10, column: 12, scope: !22)
!34 = !DILocation(line: 10, column: 19, scope: !22)
!35 = distinct !{!35, !31, !34}
!36 = !DILocation(line: 11, column: 3, scope: !22)
