; ModuleID = 'witness_resolved_assert_helper_true.c'
source_filename = "witness_resolved_assert_helper_true.c"
target datalayout = "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-i128:128-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !28 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !31
  unreachable, !dbg !31
}

; Function Attrs: nocallback noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !32 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !37, !DIExpression(), !38)
  %3 = load i32, ptr %2, align 4, !dbg !39
  %4 = icmp ne i32 %3, 0, !dbg !41
  br i1 %4, label %7, label %5, !dbg !42

5:                                                ; preds = %1
  br label %6, !dbg !43

6:                                                ; preds = %5
    #dbg_label(!44, !46)
  call void @reach_error(), !dbg !47
  call void @abort() #5, !dbg !49
  unreachable, !dbg !49

7:                                                ; preds = %1
  ret void, !dbg !50
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !51 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !54, !DIExpression(), !55)
  %5 = call i32 @__VERIFIER_nondet_int(), !dbg !56
  store i32 %5, ptr %2, align 4, !dbg !55
  %6 = load i32, ptr %2, align 4, !dbg !57
  %7 = icmp sgt i32 %6, 100, !dbg !59
  br i1 %7, label %11, label %8, !dbg !60

8:                                                ; preds = %0
  %9 = load i32, ptr %2, align 4, !dbg !61
  %10 = icmp slt i32 %9, 0, !dbg !62
  br i1 %10, label %11, label %12, !dbg !63

11:                                               ; preds = %8, %0
  store i32 0, ptr %1, align 4, !dbg !64
  br label %26, !dbg !64

12:                                               ; preds = %8
    #dbg_declare(ptr %3, !65, !DIExpression(), !66)
  store i32 0, ptr %3, align 4, !dbg !66
    #dbg_declare(ptr %4, !67, !DIExpression(), !68)
  store i32 0, ptr %4, align 4, !dbg !68
  br label %13, !dbg !69

13:                                               ; preds = %17, %12
  %14 = load i32, ptr %3, align 4, !dbg !70
  %15 = load i32, ptr %2, align 4, !dbg !71
  %16 = icmp slt i32 %14, %15, !dbg !72
  br i1 %16, label %17, label %22, !dbg !69

17:                                               ; preds = %13
  %18 = load i32, ptr %4, align 4, !dbg !73
  %19 = add nsw i32 %18, 2, !dbg !75
  store i32 %19, ptr %4, align 4, !dbg !76
  %20 = load i32, ptr %3, align 4, !dbg !77
  %21 = add nsw i32 %20, 1, !dbg !78
  store i32 %21, ptr %3, align 4, !dbg !79
  br label %13, !dbg !69, !llvm.loop !80

22:                                               ; preds = %13
  %23 = load i32, ptr %4, align 4, !dbg !82
  %24 = icmp sge i32 %23, 0, !dbg !83
  %25 = zext i1 %24 to i32, !dbg !83
  call void @__VERIFIER_assert(i32 noundef %25), !dbg !84
  store i32 0, ptr %1, align 4, !dbg !85
  br label %26, !dbg !85

26:                                               ; preds = %22, %11
  %27 = load i32, ptr %1, align 4, !dbg !86
  ret i32 %27, !dbg !86
}

declare i32 @__VERIFIER_nondet_int() #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback noreturn nounwind }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25, !26}
!llvm.ident = !{!27}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "witness_resolved_assert_helper_true.c", directory: ".", checksumkind: CSK_MD5, checksum: "30c0999663186696ef23996a79452c3b")
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
!19 = !{i32 1, !"NumRegisterParameters", i32 0}
!20 = !{i32 7, !"Dwarf Version", i32 5}
!21 = !{i32 2, !"Debug Info Version", i32 3}
!22 = !{i32 1, !"wchar_size", i32 4}
!23 = !{i32 8, !"PIC Level", i32 2}
!24 = !{i32 7, !"PIE Level", i32 2}
!25 = !{i32 7, !"uwtable", i32 2}
!26 = !{i32 7, !"frame-pointer", i32 2}
!27 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!28 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 3, type: !29, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17)
!29 = !DISubroutineType(types: !30)
!30 = !{null}
!31 = !DILocation(line: 3, column: 26, scope: !28)
!32 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !33, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !36)
!33 = !DISubroutineType(types: !34)
!34 = !{null, !35}
!35 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!36 = !{}
!37 = !DILocalVariable(name: "cond", arg: 1, scope: !32, file: !2, line: 5, type: !35)
!38 = !DILocation(line: 5, column: 28, scope: !32)
!39 = !DILocation(line: 5, column: 42, scope: !40)
!40 = distinct !DILexicalBlock(scope: !32, file: !2, line: 5, column: 40)
!41 = !DILocation(line: 5, column: 41, scope: !40)
!42 = !DILocation(line: 5, column: 40, scope: !32)
!43 = !DILocation(line: 5, column: 49, scope: !40)
!44 = !DILabel(scope: !45, name: "ERROR", file: !2, line: 5)
!45 = distinct !DILexicalBlock(scope: !40, file: !2, line: 5, column: 49)
!46 = !DILocation(line: 5, column: 51, scope: !45)
!47 = !DILocation(line: 5, column: 59, scope: !48)
!48 = distinct !DILexicalBlock(scope: !45, file: !2, line: 5, column: 58)
!49 = !DILocation(line: 5, column: 73, scope: !48)
!50 = !DILocation(line: 5, column: 85, scope: !32)
!51 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 6, type: !52, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !36)
!52 = !DISubroutineType(types: !53)
!53 = !{!35}
!54 = !DILocalVariable(name: "n", scope: !51, file: !2, line: 7, type: !35)
!55 = !DILocation(line: 7, column: 7, scope: !51)
!56 = !DILocation(line: 7, column: 11, scope: !51)
!57 = !DILocation(line: 8, column: 7, scope: !58)
!58 = distinct !DILexicalBlock(scope: !51, file: !2, line: 8, column: 7)
!59 = !DILocation(line: 8, column: 9, scope: !58)
!60 = !DILocation(line: 8, column: 15, scope: !58)
!61 = !DILocation(line: 8, column: 18, scope: !58)
!62 = !DILocation(line: 8, column: 20, scope: !58)
!63 = !DILocation(line: 8, column: 7, scope: !51)
!64 = !DILocation(line: 8, column: 25, scope: !58)
!65 = !DILocalVariable(name: "i", scope: !51, file: !2, line: 9, type: !35)
!66 = !DILocation(line: 9, column: 7, scope: !51)
!67 = !DILocalVariable(name: "x", scope: !51, file: !2, line: 9, type: !35)
!68 = !DILocation(line: 9, column: 14, scope: !51)
!69 = !DILocation(line: 10, column: 3, scope: !51)
!70 = !DILocation(line: 10, column: 10, scope: !51)
!71 = !DILocation(line: 10, column: 14, scope: !51)
!72 = !DILocation(line: 10, column: 12, scope: !51)
!73 = !DILocation(line: 11, column: 9, scope: !74)
!74 = distinct !DILexicalBlock(scope: !51, file: !2, line: 10, column: 17)
!75 = !DILocation(line: 11, column: 11, scope: !74)
!76 = !DILocation(line: 11, column: 7, scope: !74)
!77 = !DILocation(line: 12, column: 9, scope: !74)
!78 = !DILocation(line: 12, column: 11, scope: !74)
!79 = !DILocation(line: 12, column: 7, scope: !74)
!80 = distinct !{!80, !69, !81}
!81 = !DILocation(line: 13, column: 3, scope: !51)
!82 = !DILocation(line: 14, column: 21, scope: !51)
!83 = !DILocation(line: 14, column: 23, scope: !51)
!84 = !DILocation(line: 14, column: 3, scope: !51)
!85 = !DILocation(line: 15, column: 3, scope: !51)
!86 = !DILocation(line: 16, column: 1, scope: !51)
