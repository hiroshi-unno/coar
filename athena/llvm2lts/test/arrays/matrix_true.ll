; ModuleID = 'matrix_true.c'
source_filename = "matrix_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@m = dso_local global [2 x [3 x i32]] zeroinitializer, align 16, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !33 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #3, !dbg !36
  unreachable, !dbg !36
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !37 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !41, !DIExpression(), !42)
  %3 = load i32, ptr %2, align 4, !dbg !43
  %4 = icmp ne i32 %3, 0, !dbg !43
  br i1 %4, label %6, label %5, !dbg !45

5:                                                ; preds = %1
  call void @reach_error(), !dbg !46
  call void @abort() #4, !dbg !48
  unreachable, !dbg !48

6:                                                ; preds = %1
  ret void, !dbg !49
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !50 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !53, !DIExpression(), !55)
  store i32 0, ptr %2, align 4, !dbg !55
  br label %4, !dbg !56

4:                                                ; preds = %25, %0
  %5 = load i32, ptr %2, align 4, !dbg !57
  %6 = icmp slt i32 %5, 2, !dbg !59
  br i1 %6, label %7, label %28, !dbg !60

7:                                                ; preds = %4
    #dbg_declare(ptr %3, !61, !DIExpression(), !63)
  store i32 0, ptr %3, align 4, !dbg !63
  br label %8, !dbg !64

8:                                                ; preds = %21, %7
  %9 = load i32, ptr %3, align 4, !dbg !65
  %10 = icmp slt i32 %9, 3, !dbg !67
  br i1 %10, label %11, label %24, !dbg !68

11:                                               ; preds = %8
  %12 = load i32, ptr %2, align 4, !dbg !69
  %13 = load i32, ptr %3, align 4, !dbg !70
  %14 = add nsw i32 %12, %13, !dbg !71
  %15 = load i32, ptr %2, align 4, !dbg !72
  %16 = sext i32 %15 to i64, !dbg !73
  %17 = getelementptr inbounds [2 x [3 x i32]], ptr @m, i64 0, i64 %16, !dbg !73
  %18 = load i32, ptr %3, align 4, !dbg !74
  %19 = sext i32 %18 to i64, !dbg !73
  %20 = getelementptr inbounds [3 x i32], ptr %17, i64 0, i64 %19, !dbg !73
  store i32 %14, ptr %20, align 4, !dbg !75
  br label %21, !dbg !73

21:                                               ; preds = %11
  %22 = load i32, ptr %3, align 4, !dbg !76
  %23 = add nsw i32 %22, 1, !dbg !76
  store i32 %23, ptr %3, align 4, !dbg !76
  br label %8, !dbg !77, !llvm.loop !78

24:                                               ; preds = %8
  br label %25, !dbg !79

25:                                               ; preds = %24
  %26 = load i32, ptr %2, align 4, !dbg !80
  %27 = add nsw i32 %26, 1, !dbg !80
  store i32 %27, ptr %2, align 4, !dbg !80
  br label %4, !dbg !81, !llvm.loop !82

28:                                               ; preds = %4
  %29 = load i32, ptr getelementptr inbounds ([3 x i32], ptr getelementptr inbounds ([2 x [3 x i32]], ptr @m, i64 0, i64 1), i64 0, i64 2), align 4, !dbg !84
  %30 = icmp eq i32 %29, 3, !dbg !85
  %31 = zext i1 %30 to i32, !dbg !85
  call void @__VERIFIER_assert(i32 noundef %31), !dbg !86
  ret i32 0, !dbg !87
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn }
attributes #4 = { noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!25, !26, !27, !28, !29, !30, !31}
!llvm.ident = !{!32}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "matrix_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "ad55125affbc3153bd6fc252b88b53c1")
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
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "m", scope: !19, file: !2, line: 6, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DICompositeType(tag: DW_TAG_array_type, baseType: !22, size: 192, elements: !23)
!22 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!23 = !{!6, !24}
!24 = !DISubrange(count: 3)
!25 = !{i32 7, !"Dwarf Version", i32 5}
!26 = !{i32 2, !"Debug Info Version", i32 3}
!27 = !{i32 1, !"wchar_size", i32 4}
!28 = !{i32 8, !"PIC Level", i32 2}
!29 = !{i32 7, !"PIE Level", i32 2}
!30 = !{i32 7, !"uwtable", i32 2}
!31 = !{i32 7, !"frame-pointer", i32 2}
!32 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!33 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !34, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !19)
!34 = !DISubroutineType(types: !35)
!35 = !{null}
!36 = !DILocation(line: 4, column: 22, scope: !33)
!37 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !38, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !40)
!38 = !DISubroutineType(types: !39)
!39 = !{null, !22}
!40 = !{}
!41 = !DILocalVariable(name: "cond", arg: 1, scope: !37, file: !2, line: 5, type: !22)
!42 = !DILocation(line: 5, column: 28, scope: !37)
!43 = !DILocation(line: 5, column: 41, scope: !44)
!44 = distinct !DILexicalBlock(scope: !37, file: !2, line: 5, column: 40)
!45 = !DILocation(line: 5, column: 40, scope: !37)
!46 = !DILocation(line: 5, column: 49, scope: !47)
!47 = distinct !DILexicalBlock(scope: !44, file: !2, line: 5, column: 47)
!48 = !DILocation(line: 5, column: 64, scope: !47)
!49 = !DILocation(line: 5, column: 75, scope: !37)
!50 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 7, type: !51, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !40)
!51 = !DISubroutineType(types: !52)
!52 = !{!22}
!53 = !DILocalVariable(name: "i", scope: !54, file: !2, line: 8, type: !22)
!54 = distinct !DILexicalBlock(scope: !50, file: !2, line: 8, column: 3)
!55 = !DILocation(line: 8, column: 12, scope: !54)
!56 = !DILocation(line: 8, column: 8, scope: !54)
!57 = !DILocation(line: 8, column: 19, scope: !58)
!58 = distinct !DILexicalBlock(scope: !54, file: !2, line: 8, column: 3)
!59 = !DILocation(line: 8, column: 21, scope: !58)
!60 = !DILocation(line: 8, column: 3, scope: !54)
!61 = !DILocalVariable(name: "j", scope: !62, file: !2, line: 9, type: !22)
!62 = distinct !DILexicalBlock(scope: !58, file: !2, line: 9, column: 5)
!63 = !DILocation(line: 9, column: 14, scope: !62)
!64 = !DILocation(line: 9, column: 10, scope: !62)
!65 = !DILocation(line: 9, column: 21, scope: !66)
!66 = distinct !DILexicalBlock(scope: !62, file: !2, line: 9, column: 5)
!67 = !DILocation(line: 9, column: 23, scope: !66)
!68 = !DILocation(line: 9, column: 5, scope: !62)
!69 = !DILocation(line: 9, column: 43, scope: !66)
!70 = !DILocation(line: 9, column: 47, scope: !66)
!71 = !DILocation(line: 9, column: 45, scope: !66)
!72 = !DILocation(line: 9, column: 35, scope: !66)
!73 = !DILocation(line: 9, column: 33, scope: !66)
!74 = !DILocation(line: 9, column: 38, scope: !66)
!75 = !DILocation(line: 9, column: 41, scope: !66)
!76 = !DILocation(line: 9, column: 29, scope: !66)
!77 = !DILocation(line: 9, column: 5, scope: !66)
!78 = distinct !{!78, !68, !79}
!79 = !DILocation(line: 9, column: 47, scope: !62)
!80 = !DILocation(line: 8, column: 27, scope: !58)
!81 = !DILocation(line: 8, column: 3, scope: !58)
!82 = distinct !{!82, !60, !83}
!83 = !DILocation(line: 9, column: 47, scope: !54)
!84 = !DILocation(line: 10, column: 21, scope: !50)
!85 = !DILocation(line: 10, column: 29, scope: !50)
!86 = !DILocation(line: 10, column: 3, scope: !50)
!87 = !DILocation(line: 11, column: 3, scope: !50)
