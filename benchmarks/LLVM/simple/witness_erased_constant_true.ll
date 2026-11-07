; ModuleID = 'witness_erased_constant_true.c'
source_filename = "witness_erased_constant_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@k = dso_local global i32 5, align 4, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !30 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #3, !dbg !33
  unreachable, !dbg !33
}

; Function Attrs: nocallback noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !34 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !38, !DIExpression(), !39)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !40
  store i32 %4, ptr %2, align 4, !dbg !39
  %5 = load i32, ptr %2, align 4, !dbg !41
  %6 = icmp sgt i32 %5, 100, !dbg !43
  br i1 %6, label %7, label %8, !dbg !44

7:                                                ; preds = %0
  store i32 0, ptr %1, align 4, !dbg !45
  br label %22, !dbg !45

8:                                                ; preds = %0
    #dbg_declare(ptr %3, !46, !DIExpression(), !47)
  store i32 0, ptr %3, align 4, !dbg !47
  br label %9, !dbg !48

9:                                                ; preds = %13, %8
  %10 = load i32, ptr %3, align 4, !dbg !49
  %11 = load i32, ptr %2, align 4, !dbg !50
  %12 = icmp slt i32 %10, %11, !dbg !51
  br i1 %12, label %13, label %17, !dbg !48

13:                                               ; preds = %9
  %14 = load i32, ptr %3, align 4, !dbg !52
  %15 = load i32, ptr @k, align 4, !dbg !54
  %16 = add nsw i32 %14, %15, !dbg !55
  store i32 %16, ptr %3, align 4, !dbg !56
  br label %9, !dbg !48, !llvm.loop !57

17:                                               ; preds = %9
  %18 = load i32, ptr %3, align 4, !dbg !59
  %19 = icmp sgt i32 %18, 104, !dbg !61
  br i1 %19, label %20, label %21, !dbg !62

20:                                               ; preds = %17
  call void @reach_error(), !dbg !63
  br label %21, !dbg !63

21:                                               ; preds = %20, %17
  store i32 0, ptr %1, align 4, !dbg !64
  br label %22, !dbg !64

22:                                               ; preds = %21, %7
  %23 = load i32, ptr %1, align 4, !dbg !65
  ret i32 %23, !dbg !65
}

declare i32 @__VERIFIER_nondet_int() #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!22, !23, !24, !25, !26, !27, !28}
!llvm.ident = !{!29}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 2, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "witness_erased_constant_true.c", directory: ".", checksumkind: CSK_MD5, checksum: "bab29ede38967cbf951b6898867f4740")
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
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "k", scope: !19, file: !2, line: 4, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!22 = !{i32 7, !"Dwarf Version", i32 5}
!23 = !{i32 2, !"Debug Info Version", i32 3}
!24 = !{i32 1, !"wchar_size", i32 4}
!25 = !{i32 8, !"PIC Level", i32 2}
!26 = !{i32 7, !"PIE Level", i32 2}
!27 = !{i32 7, !"uwtable", i32 2}
!28 = !{i32 7, !"frame-pointer", i32 2}
!29 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!30 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 2, type: !31, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19)
!31 = !DISubroutineType(types: !32)
!32 = !{null}
!33 = !DILocation(line: 2, column: 26, scope: !30)
!34 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 5, type: !35, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !37)
!35 = !DISubroutineType(types: !36)
!36 = !{!21}
!37 = !{}
!38 = !DILocalVariable(name: "n", scope: !34, file: !2, line: 6, type: !21)
!39 = !DILocation(line: 6, column: 7, scope: !34)
!40 = !DILocation(line: 6, column: 11, scope: !34)
!41 = !DILocation(line: 7, column: 7, scope: !42)
!42 = distinct !DILexicalBlock(scope: !34, file: !2, line: 7, column: 7)
!43 = !DILocation(line: 7, column: 9, scope: !42)
!44 = !DILocation(line: 7, column: 7, scope: !34)
!45 = !DILocation(line: 7, column: 16, scope: !42)
!46 = !DILocalVariable(name: "i", scope: !34, file: !2, line: 8, type: !21)
!47 = !DILocation(line: 8, column: 7, scope: !34)
!48 = !DILocation(line: 9, column: 3, scope: !34)
!49 = !DILocation(line: 9, column: 10, scope: !34)
!50 = !DILocation(line: 9, column: 14, scope: !34)
!51 = !DILocation(line: 9, column: 12, scope: !34)
!52 = !DILocation(line: 10, column: 9, scope: !53)
!53 = distinct !DILexicalBlock(scope: !34, file: !2, line: 9, column: 17)
!54 = !DILocation(line: 10, column: 13, scope: !53)
!55 = !DILocation(line: 10, column: 11, scope: !53)
!56 = !DILocation(line: 10, column: 7, scope: !53)
!57 = distinct !{!57, !48, !58}
!58 = !DILocation(line: 11, column: 3, scope: !34)
!59 = !DILocation(line: 12, column: 7, scope: !60)
!60 = distinct !DILexicalBlock(scope: !34, file: !2, line: 12, column: 7)
!61 = !DILocation(line: 12, column: 9, scope: !60)
!62 = !DILocation(line: 12, column: 7, scope: !34)
!63 = !DILocation(line: 12, column: 16, scope: !60)
!64 = !DILocation(line: 13, column: 3, scope: !34)
!65 = !DILocation(line: 14, column: 1, scope: !34)
