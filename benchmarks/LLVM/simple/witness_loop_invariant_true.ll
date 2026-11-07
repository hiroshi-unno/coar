; ModuleID = 'witness_loop_invariant_true.c'
source_filename = "witness_loop_invariant_true.c"
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
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !38
  store i32 %4, ptr %2, align 4, !dbg !37
  %5 = load i32, ptr %2, align 4, !dbg !39
  %6 = icmp sgt i32 %5, 100, !dbg !41
  br i1 %6, label %7, label %8, !dbg !42

7:                                                ; preds = %0
  store i32 0, ptr %1, align 4, !dbg !43
  br label %21, !dbg !43

8:                                                ; preds = %0
    #dbg_declare(ptr %3, !44, !DIExpression(), !45)
  store i32 0, ptr %3, align 4, !dbg !45
  br label %9, !dbg !46

9:                                                ; preds = %13, %8
  %10 = load i32, ptr %3, align 4, !dbg !47
  %11 = load i32, ptr %2, align 4, !dbg !48
  %12 = icmp slt i32 %10, %11, !dbg !49
  br i1 %12, label %13, label %16, !dbg !46

13:                                               ; preds = %9
  %14 = load i32, ptr %3, align 4, !dbg !50
  %15 = add nsw i32 %14, 1, !dbg !52
  store i32 %15, ptr %3, align 4, !dbg !53
  br label %9, !dbg !46, !llvm.loop !54

16:                                               ; preds = %9
  %17 = load i32, ptr %3, align 4, !dbg !56
  %18 = icmp sgt i32 %17, 100, !dbg !58
  br i1 %18, label %19, label %20, !dbg !59

19:                                               ; preds = %16
  call void @reach_error(), !dbg !60
  br label %20, !dbg !60

20:                                               ; preds = %19, %16
  store i32 0, ptr %1, align 4, !dbg !61
  br label %21, !dbg !61

21:                                               ; preds = %20, %7
  %22 = load i32, ptr %1, align 4, !dbg !62
  ret i32 %22, !dbg !62
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
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "witness_loop_invariant_true.c", directory: ".", checksumkind: CSK_MD5, checksum: "8f535d2133985de5ff59042fecb7d99d")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !14, isLocal: true, isDefinition: true)
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
!27 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 3, type: !28, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17)
!28 = !DISubroutineType(types: !29)
!29 = !{null}
!30 = !DILocation(line: 3, column: 26, scope: !27)
!31 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 5, type: !32, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{!34}
!34 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!35 = !{}
!36 = !DILocalVariable(name: "n", scope: !31, file: !2, line: 6, type: !34)
!37 = !DILocation(line: 6, column: 7, scope: !31)
!38 = !DILocation(line: 6, column: 11, scope: !31)
!39 = !DILocation(line: 7, column: 7, scope: !40)
!40 = distinct !DILexicalBlock(scope: !31, file: !2, line: 7, column: 7)
!41 = !DILocation(line: 7, column: 9, scope: !40)
!42 = !DILocation(line: 7, column: 7, scope: !31)
!43 = !DILocation(line: 7, column: 16, scope: !40)
!44 = !DILocalVariable(name: "i", scope: !31, file: !2, line: 8, type: !34)
!45 = !DILocation(line: 8, column: 7, scope: !31)
!46 = !DILocation(line: 9, column: 3, scope: !31)
!47 = !DILocation(line: 9, column: 10, scope: !31)
!48 = !DILocation(line: 9, column: 14, scope: !31)
!49 = !DILocation(line: 9, column: 12, scope: !31)
!50 = !DILocation(line: 10, column: 9, scope: !51)
!51 = distinct !DILexicalBlock(scope: !31, file: !2, line: 9, column: 17)
!52 = !DILocation(line: 10, column: 11, scope: !51)
!53 = !DILocation(line: 10, column: 7, scope: !51)
!54 = distinct !{!54, !46, !55}
!55 = !DILocation(line: 11, column: 3, scope: !31)
!56 = !DILocation(line: 12, column: 7, scope: !57)
!57 = distinct !DILexicalBlock(scope: !31, file: !2, line: 12, column: 7)
!58 = !DILocation(line: 12, column: 9, scope: !57)
!59 = !DILocation(line: 12, column: 7, scope: !31)
!60 = !DILocation(line: 12, column: 16, scope: !57)
!61 = !DILocation(line: 13, column: 3, scope: !31)
!62 = !DILocation(line: 14, column: 1, scope: !31)
