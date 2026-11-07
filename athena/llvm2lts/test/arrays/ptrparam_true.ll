; ModuleID = 'ptrparam_true.c'
source_filename = "ptrparam_true.c"
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

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !31 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %3 = load i32, ptr %2, align 4, !dbg !38
  %4 = icmp ne i32 %3, 0, !dbg !38
  br i1 %4, label %6, label %5, !dbg !40

5:                                                ; preds = %1
  call void @reach_error(), !dbg !41
  call void @abort() #4, !dbg !43
  unreachable, !dbg !43

6:                                                ; preds = %1
  ret void, !dbg !44
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local void @fill(ptr noundef %0, i32 noundef %1, i32 noundef %2) #0 !dbg !45 {
  %4 = alloca ptr, align 8
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
    #dbg_declare(ptr %4, !49, !DIExpression(), !50)
  store i32 %1, ptr %5, align 4
    #dbg_declare(ptr %5, !51, !DIExpression(), !52)
  store i32 %2, ptr %6, align 4
    #dbg_declare(ptr %6, !53, !DIExpression(), !54)
    #dbg_declare(ptr %7, !55, !DIExpression(), !57)
  store i32 0, ptr %7, align 4, !dbg !57
  br label %8, !dbg !58

8:                                                ; preds = %18, %3
  %9 = load i32, ptr %7, align 4, !dbg !59
  %10 = load i32, ptr %5, align 4, !dbg !61
  %11 = icmp slt i32 %9, %10, !dbg !62
  br i1 %11, label %12, label %21, !dbg !63

12:                                               ; preds = %8
  %13 = load i32, ptr %6, align 4, !dbg !64
  %14 = load ptr, ptr %4, align 8, !dbg !65
  %15 = load i32, ptr %7, align 4, !dbg !66
  %16 = sext i32 %15 to i64, !dbg !65
  %17 = getelementptr inbounds i32, ptr %14, i64 %16, !dbg !65
  store i32 %13, ptr %17, align 4, !dbg !67
  br label %18, !dbg !65

18:                                               ; preds = %12
  %19 = load i32, ptr %7, align 4, !dbg !68
  %20 = add nsw i32 %19, 1, !dbg !68
  store i32 %20, ptr %7, align 4, !dbg !68
  br label %8, !dbg !69, !llvm.loop !70

21:                                               ; preds = %8
  ret void, !dbg !72
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @sum(ptr noundef %0, i32 noundef %1) #0 !dbg !73 {
  %3 = alloca ptr, align 8
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !76, !DIExpression(), !77)
  store i32 %1, ptr %4, align 4
    #dbg_declare(ptr %4, !78, !DIExpression(), !79)
    #dbg_declare(ptr %5, !80, !DIExpression(), !81)
  store i32 0, ptr %5, align 4, !dbg !81
    #dbg_declare(ptr %6, !82, !DIExpression(), !84)
  store i32 0, ptr %6, align 4, !dbg !84
  br label %7, !dbg !85

7:                                                ; preds = %19, %2
  %8 = load i32, ptr %6, align 4, !dbg !86
  %9 = load i32, ptr %4, align 4, !dbg !88
  %10 = icmp slt i32 %8, %9, !dbg !89
  br i1 %10, label %11, label %22, !dbg !90

11:                                               ; preds = %7
  %12 = load ptr, ptr %3, align 8, !dbg !91
  %13 = load i32, ptr %6, align 4, !dbg !92
  %14 = sext i32 %13 to i64, !dbg !91
  %15 = getelementptr inbounds i32, ptr %12, i64 %14, !dbg !91
  %16 = load i32, ptr %15, align 4, !dbg !91
  %17 = load i32, ptr %5, align 4, !dbg !93
  %18 = add nsw i32 %17, %16, !dbg !93
  store i32 %18, ptr %5, align 4, !dbg !93
  br label %19, !dbg !94

19:                                               ; preds = %11
  %20 = load i32, ptr %6, align 4, !dbg !95
  %21 = add nsw i32 %20, 1, !dbg !95
  store i32 %21, ptr %6, align 4, !dbg !95
  br label %7, !dbg !96, !llvm.loop !97

22:                                               ; preds = %7
  %23 = load i32, ptr %5, align 4, !dbg !99
  ret i32 %23, !dbg !100
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !101 {
  %1 = alloca i32, align 4
  %2 = alloca [3 x i32], align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !104, !DIExpression(), !108)
  %3 = getelementptr inbounds [3 x i32], ptr %2, i64 0, i64 0, !dbg !109
  call void @fill(ptr noundef %3, i32 noundef 3, i32 noundef 2), !dbg !110
  %4 = getelementptr inbounds [3 x i32], ptr %2, i64 0, i64 0, !dbg !111
  %5 = call i32 @sum(ptr noundef %4, i32 noundef 3), !dbg !112
  %6 = icmp eq i32 %5, 6, !dbg !113
  %7 = zext i1 %6 to i32, !dbg !113
  call void @__VERIFIER_assert(i32 noundef %7), !dbg !114
  ret i32 0, !dbg !115
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn }
attributes #4 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "ptrparam_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "6f451b27751c7bb0499b9c2378ea3e79")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!18 = !{!0, !7, !12}
!19 = !{i32 7, !"Dwarf Version", i32 5}
!20 = !{i32 2, !"Debug Info Version", i32 3}
!21 = !{i32 1, !"wchar_size", i32 4}
!22 = !{i32 8, !"PIC Level", i32 2}
!23 = !{i32 7, !"PIE Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!27 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !28, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !17)
!28 = !DISubroutineType(types: !29)
!29 = !{null}
!30 = !DILocation(line: 4, column: 22, scope: !27)
!31 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !32, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{null, !34}
!34 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!35 = !{}
!36 = !DILocalVariable(name: "cond", arg: 1, scope: !31, file: !2, line: 5, type: !34)
!37 = !DILocation(line: 5, column: 28, scope: !31)
!38 = !DILocation(line: 5, column: 41, scope: !39)
!39 = distinct !DILexicalBlock(scope: !31, file: !2, line: 5, column: 40)
!40 = !DILocation(line: 5, column: 40, scope: !31)
!41 = !DILocation(line: 5, column: 49, scope: !42)
!42 = distinct !DILexicalBlock(scope: !39, file: !2, line: 5, column: 47)
!43 = !DILocation(line: 5, column: 64, scope: !42)
!44 = !DILocation(line: 5, column: 75, scope: !31)
!45 = distinct !DISubprogram(name: "fill", scope: !2, file: !2, line: 6, type: !46, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{null, !48, !34, !34}
!48 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !34, size: 64)
!49 = !DILocalVariable(name: "p", arg: 1, scope: !45, file: !2, line: 6, type: !48)
!50 = !DILocation(line: 6, column: 16, scope: !45)
!51 = !DILocalVariable(name: "n", arg: 2, scope: !45, file: !2, line: 6, type: !34)
!52 = !DILocation(line: 6, column: 23, scope: !45)
!53 = !DILocalVariable(name: "v", arg: 3, scope: !45, file: !2, line: 6, type: !34)
!54 = !DILocation(line: 6, column: 30, scope: !45)
!55 = !DILocalVariable(name: "i", scope: !56, file: !2, line: 6, type: !34)
!56 = distinct !DILexicalBlock(scope: !45, file: !2, line: 6, column: 35)
!57 = !DILocation(line: 6, column: 44, scope: !56)
!58 = !DILocation(line: 6, column: 40, scope: !56)
!59 = !DILocation(line: 6, column: 51, scope: !60)
!60 = distinct !DILexicalBlock(scope: !56, file: !2, line: 6, column: 35)
!61 = !DILocation(line: 6, column: 55, scope: !60)
!62 = !DILocation(line: 6, column: 53, scope: !60)
!63 = !DILocation(line: 6, column: 35, scope: !56)
!64 = !DILocation(line: 6, column: 70, scope: !60)
!65 = !DILocation(line: 6, column: 63, scope: !60)
!66 = !DILocation(line: 6, column: 65, scope: !60)
!67 = !DILocation(line: 6, column: 68, scope: !60)
!68 = !DILocation(line: 6, column: 59, scope: !60)
!69 = !DILocation(line: 6, column: 35, scope: !60)
!70 = distinct !{!70, !63, !71}
!71 = !DILocation(line: 6, column: 70, scope: !56)
!72 = !DILocation(line: 6, column: 73, scope: !45)
!73 = distinct !DISubprogram(name: "sum", scope: !2, file: !2, line: 7, type: !74, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!74 = !DISubroutineType(types: !75)
!75 = !{!34, !48, !34}
!76 = !DILocalVariable(name: "p", arg: 1, scope: !73, file: !2, line: 7, type: !48)
!77 = !DILocation(line: 7, column: 14, scope: !73)
!78 = !DILocalVariable(name: "n", arg: 2, scope: !73, file: !2, line: 7, type: !34)
!79 = !DILocation(line: 7, column: 21, scope: !73)
!80 = !DILocalVariable(name: "s", scope: !73, file: !2, line: 7, type: !34)
!81 = !DILocation(line: 7, column: 30, scope: !73)
!82 = !DILocalVariable(name: "i", scope: !83, file: !2, line: 7, type: !34)
!83 = distinct !DILexicalBlock(scope: !73, file: !2, line: 7, column: 37)
!84 = !DILocation(line: 7, column: 46, scope: !83)
!85 = !DILocation(line: 7, column: 42, scope: !83)
!86 = !DILocation(line: 7, column: 53, scope: !87)
!87 = distinct !DILexicalBlock(scope: !83, file: !2, line: 7, column: 37)
!88 = !DILocation(line: 7, column: 57, scope: !87)
!89 = !DILocation(line: 7, column: 55, scope: !87)
!90 = !DILocation(line: 7, column: 37, scope: !83)
!91 = !DILocation(line: 7, column: 70, scope: !87)
!92 = !DILocation(line: 7, column: 72, scope: !87)
!93 = !DILocation(line: 7, column: 67, scope: !87)
!94 = !DILocation(line: 7, column: 65, scope: !87)
!95 = !DILocation(line: 7, column: 61, scope: !87)
!96 = !DILocation(line: 7, column: 37, scope: !87)
!97 = distinct !{!97, !90, !98}
!98 = !DILocation(line: 7, column: 73, scope: !83)
!99 = !DILocation(line: 7, column: 83, scope: !73)
!100 = !DILocation(line: 7, column: 76, scope: !73)
!101 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 8, type: !102, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!102 = !DISubroutineType(types: !103)
!103 = !{!34}
!104 = !DILocalVariable(name: "a", scope: !101, file: !2, line: 9, type: !105)
!105 = !DICompositeType(tag: DW_TAG_array_type, baseType: !34, size: 96, elements: !106)
!106 = !{!107}
!107 = !DISubrange(count: 3)
!108 = !DILocation(line: 9, column: 7, scope: !101)
!109 = !DILocation(line: 10, column: 8, scope: !101)
!110 = !DILocation(line: 10, column: 3, scope: !101)
!111 = !DILocation(line: 11, column: 25, scope: !101)
!112 = !DILocation(line: 11, column: 21, scope: !101)
!113 = !DILocation(line: 11, column: 31, scope: !101)
!114 = !DILocation(line: 11, column: 3, scope: !101)
!115 = !DILocation(line: 12, column: 3, scope: !101)
