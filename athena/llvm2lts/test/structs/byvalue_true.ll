; ModuleID = 'byvalue_true.c'
source_filename = "byvalue_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.P = type { i32, i32 }
%struct.R = type { [5 x i32] }
%struct.S = type { i8, i32 }

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@__const.main.p = private unnamed_addr constant %struct.P { i32 1, i32 2 }, align 4
@__const.main.rr = private unnamed_addr constant %struct.R { [5 x i32] [i32 0, i32 0, i32 7, i32 0, i32 0] }, align 4
@__const.main.s = private unnamed_addr constant %struct.S { i8 1, i32 5 }, align 4

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !27 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !30
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
  call void @abort() #5, !dbg !43
  unreachable, !dbg !43

6:                                                ; preds = %1
  ret void, !dbg !44
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @swap(i64 %0) #0 !dbg !45 {
  %2 = alloca %struct.P, align 4
  %3 = alloca %struct.P, align 4
  store i64 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !52, !DIExpression(), !53)
    #dbg_declare(ptr %2, !54, !DIExpression(), !55)
  %4 = getelementptr inbounds %struct.P, ptr %2, i32 0, i32 0, !dbg !56
  %5 = getelementptr inbounds %struct.P, ptr %3, i32 0, i32 1, !dbg !57
  %6 = load i32, ptr %5, align 4, !dbg !57
  store i32 %6, ptr %4, align 4, !dbg !56
  %7 = getelementptr inbounds %struct.P, ptr %2, i32 0, i32 1, !dbg !56
  %8 = getelementptr inbounds %struct.P, ptr %3, i32 0, i32 0, !dbg !58
  %9 = load i32, ptr %8, align 4, !dbg !58
  store i32 %9, ptr %7, align 4, !dbg !56
  %10 = load i64, ptr %2, align 4, !dbg !59
  ret i64 %10, !dbg !59
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @third(ptr noundef byval(%struct.R) align 8 %0) #0 !dbg !60 {
    #dbg_declare(ptr %0, !69, !DIExpression(), !70)
  %2 = getelementptr inbounds %struct.R, ptr %0, i32 0, i32 0, !dbg !71
  %3 = getelementptr inbounds [5 x i32], ptr %2, i64 0, i64 2, !dbg !72
  %4 = load i32, ptr %3, align 8, !dbg !72
  ret i32 %4, !dbg !73
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @geti(i64 %0) #0 !dbg !74 {
  %2 = alloca %struct.S, align 4
  store i64 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !81, !DIExpression(), !82)
  %3 = getelementptr inbounds %struct.S, ptr %2, i32 0, i32 1, !dbg !83
  %4 = load i32, ptr %3, align 4, !dbg !83
  %5 = getelementptr inbounds %struct.S, ptr %2, i32 0, i32 0, !dbg !84
  %6 = load i8, ptr %5, align 4, !dbg !84
  %7 = sext i8 %6 to i32, !dbg !85
  %8 = add nsw i32 %4, %7, !dbg !86
  ret i32 %8, !dbg !87
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !88 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.P, align 4
  %3 = alloca %struct.P, align 4
  %4 = alloca %struct.R, align 8
  %5 = alloca %struct.S, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !91, !DIExpression(), !92)
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %2, ptr align 4 @__const.main.p, i64 8, i1 false), !dbg !92
    #dbg_declare(ptr %3, !93, !DIExpression(), !94)
  %6 = load i64, ptr %2, align 4, !dbg !95
  %7 = call i64 @swap(i64 %6), !dbg !95
  store i64 %7, ptr %3, align 4, !dbg !95
    #dbg_declare(ptr %4, !96, !DIExpression(), !97)
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %4, ptr align 4 @__const.main.rr, i64 20, i1 false), !dbg !97
    #dbg_declare(ptr %5, !98, !DIExpression(), !99)
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %5, ptr align 4 @__const.main.s, i64 8, i1 false), !dbg !99
  %8 = getelementptr inbounds %struct.P, ptr %3, i32 0, i32 0, !dbg !100
  %9 = load i32, ptr %8, align 4, !dbg !100
  %10 = icmp eq i32 %9, 2, !dbg !101
  br i1 %10, label %11, label %22, !dbg !102

11:                                               ; preds = %0
  %12 = getelementptr inbounds %struct.P, ptr %3, i32 0, i32 1, !dbg !103
  %13 = load i32, ptr %12, align 4, !dbg !103
  %14 = icmp eq i32 %13, 1, !dbg !104
  br i1 %14, label %15, label %22, !dbg !105

15:                                               ; preds = %11
  %16 = call i32 @third(ptr noundef byval(%struct.R) align 8 %4), !dbg !106
  %17 = icmp eq i32 %16, 7, !dbg !107
  br i1 %17, label %18, label %22, !dbg !108

18:                                               ; preds = %15
  %19 = load i64, ptr %5, align 4, !dbg !109
  %20 = call i32 @geti(i64 %19), !dbg !109
  %21 = icmp eq i32 %20, 6, !dbg !110
  br label %22

22:                                               ; preds = %18, %15, %11, %0
  %23 = phi i1 [ false, %15 ], [ false, %11 ], [ false, %0 ], [ %21, %18 ], !dbg !111
  %24 = zext i1 %23 to i32, !dbg !108
  call void @__VERIFIER_assert(i32 noundef %24), !dbg !112
  ret i32 0, !dbg !113
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "byvalue_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "18ba6f99bb8f6f21aa4ed35aadf763d1")
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
!45 = distinct !DISubprogram(name: "swap", scope: !2, file: !2, line: 9, type: !46, scopeLine: 9, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{!48, !48}
!48 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "P", file: !2, line: 6, size: 64, elements: !49)
!49 = !{!50, !51}
!50 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !48, file: !2, line: 6, baseType: !34, size: 32)
!51 = !DIDerivedType(tag: DW_TAG_member, name: "y", scope: !48, file: !2, line: 6, baseType: !34, size: 32, offset: 32)
!52 = !DILocalVariable(name: "p", arg: 1, scope: !45, file: !2, line: 9, type: !48)
!53 = !DILocation(line: 9, column: 24, scope: !45)
!54 = !DILocalVariable(name: "r", scope: !45, file: !2, line: 9, type: !48)
!55 = !DILocation(line: 9, column: 38, scope: !45)
!56 = !DILocation(line: 9, column: 42, scope: !45)
!57 = !DILocation(line: 9, column: 46, scope: !45)
!58 = !DILocation(line: 9, column: 51, scope: !45)
!59 = !DILocation(line: 9, column: 56, scope: !45)
!60 = distinct !DISubprogram(name: "third", scope: !2, file: !2, line: 10, type: !61, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!61 = !DISubroutineType(types: !62)
!62 = !{!34, !63}
!63 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "R", file: !2, line: 7, size: 160, elements: !64)
!64 = !{!65}
!65 = !DIDerivedType(tag: DW_TAG_member, name: "a", scope: !63, file: !2, line: 7, baseType: !66, size: 160)
!66 = !DICompositeType(tag: DW_TAG_array_type, baseType: !34, size: 160, elements: !67)
!67 = !{!68}
!68 = !DISubrange(count: 5)
!69 = !DILocalVariable(name: "r", arg: 1, scope: !60, file: !2, line: 10, type: !63)
!70 = !DILocation(line: 10, column: 20, scope: !60)
!71 = !DILocation(line: 10, column: 34, scope: !60)
!72 = !DILocation(line: 10, column: 32, scope: !60)
!73 = !DILocation(line: 10, column: 25, scope: !60)
!74 = distinct !DISubprogram(name: "geti", scope: !2, file: !2, line: 11, type: !75, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!75 = !DISubroutineType(types: !76)
!76 = !{!34, !77}
!77 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "S", file: !2, line: 8, size: 64, elements: !78)
!78 = !{!79, !80}
!79 = !DIDerivedType(tag: DW_TAG_member, name: "c", scope: !77, file: !2, line: 8, baseType: !4, size: 8)
!80 = !DIDerivedType(tag: DW_TAG_member, name: "i", scope: !77, file: !2, line: 8, baseType: !34, size: 32, offset: 32)
!81 = !DILocalVariable(name: "s", arg: 1, scope: !74, file: !2, line: 11, type: !77)
!82 = !DILocation(line: 11, column: 19, scope: !74)
!83 = !DILocation(line: 11, column: 33, scope: !74)
!84 = !DILocation(line: 11, column: 39, scope: !74)
!85 = !DILocation(line: 11, column: 37, scope: !74)
!86 = !DILocation(line: 11, column: 35, scope: !74)
!87 = !DILocation(line: 11, column: 24, scope: !74)
!88 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 12, type: !89, scopeLine: 12, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!89 = !DISubroutineType(types: !90)
!90 = !{!34}
!91 = !DILocalVariable(name: "p", scope: !88, file: !2, line: 13, type: !48)
!92 = !DILocation(line: 13, column: 12, scope: !88)
!93 = !DILocalVariable(name: "r", scope: !88, file: !2, line: 14, type: !48)
!94 = !DILocation(line: 14, column: 12, scope: !88)
!95 = !DILocation(line: 14, column: 16, scope: !88)
!96 = !DILocalVariable(name: "rr", scope: !88, file: !2, line: 15, type: !63)
!97 = !DILocation(line: 15, column: 12, scope: !88)
!98 = !DILocalVariable(name: "s", scope: !88, file: !2, line: 16, type: !77)
!99 = !DILocation(line: 16, column: 12, scope: !88)
!100 = !DILocation(line: 17, column: 23, scope: !88)
!101 = !DILocation(line: 17, column: 25, scope: !88)
!102 = !DILocation(line: 17, column: 30, scope: !88)
!103 = !DILocation(line: 17, column: 35, scope: !88)
!104 = !DILocation(line: 17, column: 37, scope: !88)
!105 = !DILocation(line: 17, column: 42, scope: !88)
!106 = !DILocation(line: 17, column: 45, scope: !88)
!107 = !DILocation(line: 17, column: 55, scope: !88)
!108 = !DILocation(line: 17, column: 60, scope: !88)
!109 = !DILocation(line: 17, column: 63, scope: !88)
!110 = !DILocation(line: 17, column: 71, scope: !88)
!111 = !DILocation(line: 0, scope: !88)
!112 = !DILocation(line: 17, column: 3, scope: !88)
!113 = !DILocation(line: 18, column: 3, scope: !88)
