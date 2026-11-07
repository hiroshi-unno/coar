; ModuleID = 'witness_violation_two_errors_false.c'
source_filename = "witness_violation_two_errors_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !27 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #3, !dbg !30
  unreachable, !dbg !30
}

; Function Attrs: nocallback noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !31 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !38
  store i32 %3, ptr %2, align 4, !dbg !37
  %4 = load i32, ptr %2, align 4, !dbg !39
  %5 = icmp sgt i32 %4, 10, !dbg !41
  br i1 %5, label %6, label %10, !dbg !42

6:                                                ; preds = %0
  %7 = load i32, ptr %2, align 4, !dbg !43
  %8 = icmp slt i32 %7, 5, !dbg !44
  br i1 %8, label %9, label %10, !dbg !45

9:                                                ; preds = %6
  call void @reach_error(), !dbg !46
  br label %10, !dbg !46

10:                                               ; preds = %9, %6, %0
  %11 = load i32, ptr %2, align 4, !dbg !47
  %12 = icmp eq i32 %11, 7, !dbg !49
  br i1 %12, label %13, label %14, !dbg !50

13:                                               ; preds = %10
  call void @reach_error(), !dbg !51
  br label %14, !dbg !51

14:                                               ; preds = %13, %10
  ret i32 0, !dbg !52
}

declare i32 @__VERIFIER_nondet_int() #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 2, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "witness_violation_two_errors_false.c", directory: ".", checksumkind: CSK_MD5, checksum: "6b25fe14d6f42397ba75f90be25276c1")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 2, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 2, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!18 = !{!0, !7, !12}
!19 = !{i32 7, !"Dwarf Version", i32 5}
!20 = !{i32 2, !"Debug Info Version", i32 3}
!21 = !{i32 1, !"wchar_size", i32 4}
!22 = !{i32 8, !"PIC Level", i32 2}
!23 = !{i32 7, !"PIE Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!27 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 2, type: !28, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17)
!28 = !DISubroutineType(types: !29)
!29 = !{null}
!30 = !DILocation(line: 2, column: 26, scope: !27)
!31 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 4, type: !32, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{!34}
!34 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!35 = !{}
!36 = !DILocalVariable(name: "x", scope: !31, file: !2, line: 5, type: !34)
!37 = !DILocation(line: 5, column: 7, scope: !31)
!38 = !DILocation(line: 5, column: 11, scope: !31)
!39 = !DILocation(line: 6, column: 7, scope: !40)
!40 = distinct !DILexicalBlock(scope: !31, file: !2, line: 6, column: 7)
!41 = !DILocation(line: 6, column: 9, scope: !40)
!42 = !DILocation(line: 6, column: 14, scope: !40)
!43 = !DILocation(line: 6, column: 17, scope: !40)
!44 = !DILocation(line: 6, column: 19, scope: !40)
!45 = !DILocation(line: 6, column: 7, scope: !31)
!46 = !DILocation(line: 6, column: 24, scope: !40)
!47 = !DILocation(line: 7, column: 7, scope: !48)
!48 = distinct !DILexicalBlock(scope: !31, file: !2, line: 7, column: 7)
!49 = !DILocation(line: 7, column: 9, scope: !48)
!50 = !DILocation(line: 7, column: 7, scope: !31)
!51 = !DILocation(line: 7, column: 15, scope: !48)
!52 = !DILocation(line: 8, column: 3, scope: !31)
