; ModuleID = 'termination/hoist_true.c'
source_filename = "termination/hoist_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@bound = dso_local global [4 x i32] zeroinitializer, align 16, !dbg !0

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !17 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !21
  store i32 %3, ptr getelementptr inbounds ([4 x i32], ptr @bound, i64 0, i64 1), align 4, !dbg !22
    #dbg_declare(ptr %2, !23, !DIExpression(), !24)
  store i32 0, ptr %2, align 4, !dbg !24
  br label %4, !dbg !25

4:                                                ; preds = %14, %0
  %5 = load i32, ptr %2, align 4, !dbg !26
  %6 = load i32, ptr getelementptr inbounds ([4 x i32], ptr @bound, i64 0, i64 1), align 4, !dbg !27
  %7 = icmp slt i32 %5, %6, !dbg !28
  br i1 %7, label %8, label %15, !dbg !25

8:                                                ; preds = %4
  %9 = load i32, ptr %2, align 4, !dbg !29
  %10 = add nsw i32 %9, 1, !dbg !29
  store i32 %10, ptr %2, align 4, !dbg !29
  %11 = load i32, ptr %2, align 4, !dbg !31
  %12 = icmp eq i32 %11, 5, !dbg !33
  br i1 %12, label %13, label %14, !dbg !34

13:                                               ; preds = %8
  store i32 1, ptr %1, align 4, !dbg !35
  br label %16, !dbg !35

14:                                               ; preds = %8
  br label %4, !dbg !25, !llvm.loop !36

15:                                               ; preds = %4
  store i32 0, ptr %1, align 4, !dbg !38
  br label %16, !dbg !38

16:                                               ; preds = %15, %13
  %17 = load i32, ptr %1, align 4, !dbg !39
  ret i32 %17, !dbg !39
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!9, !10, !11, !12, !13, !14, !15}
!llvm.ident = !{!16}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "bound", scope: !2, file: !3, line: 2, type: !5, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C11, file: !3, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !4, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "termination/hoist_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "d26f533ef44483f2fb3dae9c28f3c59e")
!4 = !{!0}
!5 = !DICompositeType(tag: DW_TAG_array_type, baseType: !6, size: 128, elements: !7)
!6 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!7 = !{!8}
!8 = !DISubrange(count: 4)
!9 = !{i32 7, !"Dwarf Version", i32 5}
!10 = !{i32 2, !"Debug Info Version", i32 3}
!11 = !{i32 1, !"wchar_size", i32 4}
!12 = !{i32 8, !"PIC Level", i32 2}
!13 = !{i32 7, !"PIE Level", i32 2}
!14 = !{i32 7, !"uwtable", i32 2}
!15 = !{i32 7, !"frame-pointer", i32 2}
!16 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!17 = distinct !DISubprogram(name: "main", scope: !3, file: !3, line: 3, type: !18, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !20)
!18 = !DISubroutineType(types: !19)
!19 = !{!6}
!20 = !{}
!21 = !DILocation(line: 4, column: 14, scope: !17)
!22 = !DILocation(line: 4, column: 12, scope: !17)
!23 = !DILocalVariable(name: "a", scope: !17, file: !3, line: 5, type: !6)
!24 = !DILocation(line: 5, column: 7, scope: !17)
!25 = !DILocation(line: 6, column: 3, scope: !17)
!26 = !DILocation(line: 6, column: 10, scope: !17)
!27 = !DILocation(line: 6, column: 14, scope: !17)
!28 = !DILocation(line: 6, column: 12, scope: !17)
!29 = !DILocation(line: 7, column: 6, scope: !30)
!30 = distinct !DILexicalBlock(scope: !17, file: !3, line: 6, column: 24)
!31 = !DILocation(line: 8, column: 9, scope: !32)
!32 = distinct !DILexicalBlock(scope: !30, file: !3, line: 8, column: 9)
!33 = !DILocation(line: 8, column: 11, scope: !32)
!34 = !DILocation(line: 8, column: 9, scope: !30)
!35 = !DILocation(line: 8, column: 17, scope: !32)
!36 = distinct !{!36, !25, !37}
!37 = !DILocation(line: 9, column: 3, scope: !17)
!38 = !DILocation(line: 10, column: 3, scope: !17)
!39 = !DILocation(line: 11, column: 1, scope: !17)
