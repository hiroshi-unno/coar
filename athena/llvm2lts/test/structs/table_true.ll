; ModuleID = 'table_true.c'
source_filename = "table_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.entry = type { i16, i64 }

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@table = dso_local global [3 x %struct.entry] [%struct.entry { i16 1, i64 10 }, %struct.entry { i16 2, i64 20 }, %struct.entry { i16 3, i64 30 }], align 16, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !38 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !41
  unreachable, !dbg !41
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !42 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !47, !DIExpression(), !48)
  %3 = load i32, ptr %2, align 4, !dbg !49
  %4 = icmp ne i32 %3, 0, !dbg !49
  br i1 %4, label %6, label %5, !dbg !51

5:                                                ; preds = %1
  call void @reach_error(), !dbg !52
  call void @abort() #5, !dbg !54
  unreachable, !dbg !54

6:                                                ; preds = %1
  ret void, !dbg !55
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !56 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !59, !DIExpression(), !60)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !61
  store i32 %3, ptr %2, align 4, !dbg !60
  %4 = load i32, ptr %2, align 4, !dbg !62
  %5 = icmp slt i32 %4, 0, !dbg !64
  br i1 %5, label %9, label %6, !dbg !65

6:                                                ; preds = %0
  %7 = load i32, ptr %2, align 4, !dbg !66
  %8 = icmp sge i32 %7, 3, !dbg !67
  br i1 %8, label %9, label %10, !dbg !68

9:                                                ; preds = %6, %0
  store i32 0, ptr %1, align 4, !dbg !69
  br label %26, !dbg !69

10:                                               ; preds = %6
  %11 = load i32, ptr %2, align 4, !dbg !70
  %12 = sext i32 %11 to i64, !dbg !71
  %13 = getelementptr inbounds [3 x %struct.entry], ptr @table, i64 0, i64 %12, !dbg !71
  %14 = getelementptr inbounds %struct.entry, ptr %13, i32 0, i32 1, !dbg !72
  %15 = load i64, ptr %14, align 8, !dbg !72
  %16 = load i32, ptr %2, align 4, !dbg !73
  %17 = sext i32 %16 to i64, !dbg !74
  %18 = getelementptr inbounds [3 x %struct.entry], ptr @table, i64 0, i64 %17, !dbg !74
  %19 = getelementptr inbounds %struct.entry, ptr %18, i32 0, i32 0, !dbg !75
  %20 = load i16, ptr %19, align 16, !dbg !75
  %21 = sext i16 %20 to i32, !dbg !74
  %22 = mul nsw i32 10, %21, !dbg !76
  %23 = sext i32 %22 to i64, !dbg !77
  %24 = icmp eq i64 %15, %23, !dbg !78
  %25 = zext i1 %24 to i32, !dbg !78
  call void @__VERIFIER_assert(i32 noundef %25), !dbg !79
  store i32 0, ptr %1, align 4, !dbg !80
  br label %26, !dbg !80

26:                                               ; preds = %10, %9
  %27 = load i32, ptr %1, align 4, !dbg !81
  ret i32 %27, !dbg !81
}

declare i32 @__VERIFIER_nondet_int() #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!30, !31, !32, !33, !34, !35, !36}
!llvm.ident = !{!37}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "table_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "20eef401ada5de22519d9033214e7fd9")
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
!18 = distinct !DIGlobalVariable(name: "table", scope: !19, file: !2, line: 7, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DICompositeType(tag: DW_TAG_array_type, baseType: !22, size: 384, elements: !28)
!22 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "entry", file: !2, line: 6, size: 128, elements: !23)
!23 = !{!24, !26}
!24 = !DIDerivedType(tag: DW_TAG_member, name: "key", scope: !22, file: !2, line: 6, baseType: !25, size: 16)
!25 = !DIBasicType(name: "short", size: 16, encoding: DW_ATE_signed)
!26 = !DIDerivedType(tag: DW_TAG_member, name: "val", scope: !22, file: !2, line: 6, baseType: !27, size: 64, offset: 64)
!27 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!28 = !{!29}
!29 = !DISubrange(count: 3)
!30 = !{i32 7, !"Dwarf Version", i32 5}
!31 = !{i32 2, !"Debug Info Version", i32 3}
!32 = !{i32 1, !"wchar_size", i32 4}
!33 = !{i32 8, !"PIC Level", i32 2}
!34 = !{i32 7, !"PIE Level", i32 2}
!35 = !{i32 7, !"uwtable", i32 2}
!36 = !{i32 7, !"frame-pointer", i32 2}
!37 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!38 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !39, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !19)
!39 = !DISubroutineType(types: !40)
!40 = !{null}
!41 = !DILocation(line: 4, column: 22, scope: !38)
!42 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !43, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !46)
!43 = !DISubroutineType(types: !44)
!44 = !{null, !45}
!45 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!46 = !{}
!47 = !DILocalVariable(name: "cond", arg: 1, scope: !42, file: !2, line: 5, type: !45)
!48 = !DILocation(line: 5, column: 28, scope: !42)
!49 = !DILocation(line: 5, column: 41, scope: !50)
!50 = distinct !DILexicalBlock(scope: !42, file: !2, line: 5, column: 40)
!51 = !DILocation(line: 5, column: 40, scope: !42)
!52 = !DILocation(line: 5, column: 49, scope: !53)
!53 = distinct !DILexicalBlock(scope: !50, file: !2, line: 5, column: 47)
!54 = !DILocation(line: 5, column: 64, scope: !53)
!55 = !DILocation(line: 5, column: 75, scope: !42)
!56 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 8, type: !57, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !46)
!57 = !DISubroutineType(types: !58)
!58 = !{!45}
!59 = !DILocalVariable(name: "k", scope: !56, file: !2, line: 9, type: !45)
!60 = !DILocation(line: 9, column: 7, scope: !56)
!61 = !DILocation(line: 9, column: 11, scope: !56)
!62 = !DILocation(line: 10, column: 7, scope: !63)
!63 = distinct !DILexicalBlock(scope: !56, file: !2, line: 10, column: 7)
!64 = !DILocation(line: 10, column: 9, scope: !63)
!65 = !DILocation(line: 10, column: 13, scope: !63)
!66 = !DILocation(line: 10, column: 16, scope: !63)
!67 = !DILocation(line: 10, column: 18, scope: !63)
!68 = !DILocation(line: 10, column: 7, scope: !56)
!69 = !DILocation(line: 10, column: 24, scope: !63)
!70 = !DILocation(line: 11, column: 27, scope: !56)
!71 = !DILocation(line: 11, column: 21, scope: !56)
!72 = !DILocation(line: 11, column: 30, scope: !56)
!73 = !DILocation(line: 11, column: 48, scope: !56)
!74 = !DILocation(line: 11, column: 42, scope: !56)
!75 = !DILocation(line: 11, column: 51, scope: !56)
!76 = !DILocation(line: 11, column: 40, scope: !56)
!77 = !DILocation(line: 11, column: 37, scope: !56)
!78 = !DILocation(line: 11, column: 34, scope: !56)
!79 = !DILocation(line: 11, column: 3, scope: !56)
!80 = !DILocation(line: 12, column: 3, scope: !56)
!81 = !DILocation(line: 13, column: 1, scope: !56)
