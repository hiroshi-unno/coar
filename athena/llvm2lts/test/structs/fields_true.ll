; ModuleID = 'fields_true.c'
source_filename = "fields_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.outer = type { i64, %struct.inner }
%struct.inner = type { [3 x i32], i8 }
%struct.node = type { i32, i32 }

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@g = dso_local global %struct.outer zeroinitializer, align 8, !dbg !17
@nodes = dso_local global [4 x %struct.node] zeroinitializer, align 16, !dbg !21

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !49 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #6, !dbg !52
  unreachable, !dbg !52
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !53 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !57, !DIExpression(), !58)
  %3 = load i32, ptr %2, align 4, !dbg !59
  %4 = icmp ne i32 %3, 0, !dbg !59
  br i1 %4, label %6, label %5, !dbg !61

5:                                                ; preds = %1
  call void @reach_error(), !dbg !62
  call void @abort() #7, !dbg !64
  unreachable, !dbg !64

6:                                                ; preds = %1
  ret void, !dbg !65
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !66 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.outer, align 8
  %3 = alloca %struct.outer, align 8
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !69, !DIExpression(), !70)
  call void @llvm.memset.p0.i64(ptr align 8 %2, i8 0, i64 24, i1 false), !dbg !70
    #dbg_declare(ptr %3, !71, !DIExpression(), !72)
    #dbg_declare(ptr %4, !73, !DIExpression(), !74)
  %5 = call i32 @__VERIFIER_nondet_int(), !dbg !75
  store i32 %5, ptr %4, align 4, !dbg !74
  %6 = load i32, ptr %4, align 4, !dbg !76
  %7 = icmp slt i32 %6, 0, !dbg !78
  br i1 %7, label %11, label %8, !dbg !79

8:                                                ; preds = %0
  %9 = load i32, ptr %4, align 4, !dbg !80
  %10 = icmp sge i32 %9, 3, !dbg !81
  br i1 %10, label %11, label %12, !dbg !82

11:                                               ; preds = %8, %0
  store i32 0, ptr %1, align 4, !dbg !83
  br label %55, !dbg !83

12:                                               ; preds = %8
  %13 = getelementptr inbounds %struct.outer, ptr %2, i32 0, i32 1, !dbg !84
  %14 = getelementptr inbounds %struct.inner, ptr %13, i32 0, i32 0, !dbg !85
  %15 = load i32, ptr %4, align 4, !dbg !86
  %16 = sext i32 %15 to i64, !dbg !87
  %17 = getelementptr inbounds [3 x i32], ptr %14, i64 0, i64 %16, !dbg !87
  store i32 9, ptr %17, align 4, !dbg !88
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %3, ptr align 8 %2, i64 24, i1 false), !dbg !89
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 @g, ptr align 8 %3, i64 24, i1 false), !dbg !90
  %18 = load i32, ptr %4, align 4, !dbg !91
  %19 = sext i32 %18 to i64, !dbg !92
  %20 = getelementptr inbounds [4 x %struct.node], ptr @nodes, i64 0, i64 %19, !dbg !92
  %21 = getelementptr inbounds %struct.node, ptr %20, i32 0, i32 0, !dbg !93
  store i32 4, ptr %21, align 8, !dbg !94
  %22 = load i32, ptr %4, align 4, !dbg !95
  %23 = add nsw i32 %22, 1, !dbg !96
  %24 = load i32, ptr %4, align 4, !dbg !97
  %25 = sext i32 %24 to i64, !dbg !98
  %26 = getelementptr inbounds [4 x %struct.node], ptr @nodes, i64 0, i64 %25, !dbg !98
  %27 = getelementptr inbounds %struct.node, ptr %26, i32 0, i32 1, !dbg !99
  store i32 %23, ptr %27, align 4, !dbg !100
  %28 = load i32, ptr %4, align 4, !dbg !101
  %29 = sext i32 %28 to i64, !dbg !102
  %30 = getelementptr inbounds [3 x i32], ptr getelementptr inbounds (%struct.outer, ptr @g, i32 0, i32 1), i64 0, i64 %29, !dbg !102
  %31 = load i32, ptr %30, align 4, !dbg !102
  %32 = icmp eq i32 %31, 9, !dbg !103
  br i1 %32, label %33, label %52, !dbg !104

33:                                               ; preds = %12
  %34 = getelementptr inbounds %struct.outer, ptr %3, i32 0, i32 0, !dbg !105
  %35 = load i64, ptr %34, align 8, !dbg !105
  %36 = icmp eq i64 %35, 0, !dbg !106
  br i1 %36, label %37, label %52, !dbg !107

37:                                               ; preds = %33
  %38 = load i32, ptr %4, align 4, !dbg !108
  %39 = sext i32 %38 to i64, !dbg !109
  %40 = getelementptr inbounds [4 x %struct.node], ptr @nodes, i64 0, i64 %39, !dbg !109
  %41 = getelementptr inbounds %struct.node, ptr %40, i32 0, i32 0, !dbg !110
  %42 = load i32, ptr %41, align 8, !dbg !110
  %43 = load i32, ptr %4, align 4, !dbg !111
  %44 = sext i32 %43 to i64, !dbg !112
  %45 = getelementptr inbounds [4 x %struct.node], ptr @nodes, i64 0, i64 %44, !dbg !112
  %46 = getelementptr inbounds %struct.node, ptr %45, i32 0, i32 1, !dbg !113
  %47 = load i32, ptr %46, align 4, !dbg !113
  %48 = add nsw i32 %42, %47, !dbg !114
  %49 = load i32, ptr %4, align 4, !dbg !115
  %50 = add nsw i32 %49, 5, !dbg !116
  %51 = icmp eq i32 %48, %50, !dbg !117
  br label %52

52:                                               ; preds = %37, %33, %12
  %53 = phi i1 [ false, %33 ], [ false, %12 ], [ %51, %37 ], !dbg !118
  %54 = zext i1 %53 to i32, !dbg !107
  call void @__VERIFIER_assert(i32 noundef %54), !dbg !119
  store i32 0, ptr %1, align 4, !dbg !120
  br label %55, !dbg !120

55:                                               ; preds = %52, %11
  %56 = load i32, ptr %1, align 4, !dbg !121
  ret i32 %56, !dbg !121
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #3

declare i32 @__VERIFIER_nondet_int() #4

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #5

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #4 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { noreturn }
attributes #7 = { noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!41, !42, !43, !44, !45, !46, !47}
!llvm.ident = !{!48}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "fields_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "8080103f7965b0101b4f30e5d0613e0e")
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
!18 = distinct !DIGlobalVariable(name: "g", scope: !19, file: !2, line: 8, type: !29, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17, !21}
!21 = !DIGlobalVariableExpression(var: !22, expr: !DIExpression())
!22 = distinct !DIGlobalVariable(name: "nodes", scope: !19, file: !2, line: 9, type: !23, isLocal: false, isDefinition: true)
!23 = !DICompositeType(tag: DW_TAG_array_type, baseType: !24, size: 256, elements: !10)
!24 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "node", file: !2, line: 9, size: 64, elements: !25)
!25 = !{!26, !28}
!26 = !DIDerivedType(tag: DW_TAG_member, name: "val", scope: !24, file: !2, line: 9, baseType: !27, size: 32)
!27 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!28 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !24, file: !2, line: 9, baseType: !27, size: 32, offset: 32)
!29 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "outer", file: !2, line: 7, size: 192, elements: !30)
!30 = !{!31, !33}
!31 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !29, file: !2, line: 7, baseType: !32, size: 64)
!32 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!33 = !DIDerivedType(tag: DW_TAG_member, name: "in", scope: !29, file: !2, line: 7, baseType: !34, size: 128, offset: 64)
!34 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "inner", file: !2, line: 6, size: 128, elements: !35)
!35 = !{!36, !40}
!36 = !DIDerivedType(tag: DW_TAG_member, name: "v", scope: !34, file: !2, line: 6, baseType: !37, size: 96)
!37 = !DICompositeType(tag: DW_TAG_array_type, baseType: !27, size: 96, elements: !38)
!38 = !{!39}
!39 = !DISubrange(count: 3)
!40 = !DIDerivedType(tag: DW_TAG_member, name: "tag", scope: !34, file: !2, line: 6, baseType: !4, size: 8, offset: 96)
!41 = !{i32 7, !"Dwarf Version", i32 5}
!42 = !{i32 2, !"Debug Info Version", i32 3}
!43 = !{i32 1, !"wchar_size", i32 4}
!44 = !{i32 8, !"PIC Level", i32 2}
!45 = !{i32 7, !"PIE Level", i32 2}
!46 = !{i32 7, !"uwtable", i32 2}
!47 = !{i32 7, !"frame-pointer", i32 2}
!48 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!49 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !50, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !19)
!50 = !DISubroutineType(types: !51)
!51 = !{null}
!52 = !DILocation(line: 4, column: 22, scope: !49)
!53 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !54, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !56)
!54 = !DISubroutineType(types: !55)
!55 = !{null, !27}
!56 = !{}
!57 = !DILocalVariable(name: "cond", arg: 1, scope: !53, file: !2, line: 5, type: !27)
!58 = !DILocation(line: 5, column: 28, scope: !53)
!59 = !DILocation(line: 5, column: 41, scope: !60)
!60 = distinct !DILexicalBlock(scope: !53, file: !2, line: 5, column: 40)
!61 = !DILocation(line: 5, column: 40, scope: !53)
!62 = !DILocation(line: 5, column: 49, scope: !63)
!63 = distinct !DILexicalBlock(scope: !60, file: !2, line: 5, column: 47)
!64 = !DILocation(line: 5, column: 64, scope: !63)
!65 = !DILocation(line: 5, column: 75, scope: !53)
!66 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 10, type: !67, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !56)
!67 = !DISubroutineType(types: !68)
!68 = !{!27}
!69 = !DILocalVariable(name: "o", scope: !66, file: !2, line: 11, type: !29)
!70 = !DILocation(line: 11, column: 16, scope: !66)
!71 = !DILocalVariable(name: "o2", scope: !66, file: !2, line: 12, type: !29)
!72 = !DILocation(line: 12, column: 16, scope: !66)
!73 = !DILocalVariable(name: "k", scope: !66, file: !2, line: 13, type: !27)
!74 = !DILocation(line: 13, column: 7, scope: !66)
!75 = !DILocation(line: 13, column: 11, scope: !66)
!76 = !DILocation(line: 14, column: 7, scope: !77)
!77 = distinct !DILexicalBlock(scope: !66, file: !2, line: 14, column: 7)
!78 = !DILocation(line: 14, column: 9, scope: !77)
!79 = !DILocation(line: 14, column: 13, scope: !77)
!80 = !DILocation(line: 14, column: 16, scope: !77)
!81 = !DILocation(line: 14, column: 18, scope: !77)
!82 = !DILocation(line: 14, column: 7, scope: !66)
!83 = !DILocation(line: 14, column: 24, scope: !77)
!84 = !DILocation(line: 15, column: 5, scope: !66)
!85 = !DILocation(line: 15, column: 8, scope: !66)
!86 = !DILocation(line: 15, column: 10, scope: !66)
!87 = !DILocation(line: 15, column: 3, scope: !66)
!88 = !DILocation(line: 15, column: 13, scope: !66)
!89 = !DILocation(line: 16, column: 8, scope: !66)
!90 = !DILocation(line: 17, column: 7, scope: !66)
!91 = !DILocation(line: 18, column: 9, scope: !66)
!92 = !DILocation(line: 18, column: 3, scope: !66)
!93 = !DILocation(line: 18, column: 12, scope: !66)
!94 = !DILocation(line: 18, column: 16, scope: !66)
!95 = !DILocation(line: 19, column: 19, scope: !66)
!96 = !DILocation(line: 19, column: 21, scope: !66)
!97 = !DILocation(line: 19, column: 9, scope: !66)
!98 = !DILocation(line: 19, column: 3, scope: !66)
!99 = !DILocation(line: 19, column: 12, scope: !66)
!100 = !DILocation(line: 19, column: 17, scope: !66)
!101 = !DILocation(line: 20, column: 28, scope: !66)
!102 = !DILocation(line: 20, column: 21, scope: !66)
!103 = !DILocation(line: 20, column: 31, scope: !66)
!104 = !DILocation(line: 20, column: 36, scope: !66)
!105 = !DILocation(line: 20, column: 42, scope: !66)
!106 = !DILocation(line: 20, column: 45, scope: !66)
!107 = !DILocation(line: 20, column: 50, scope: !66)
!108 = !DILocation(line: 20, column: 59, scope: !66)
!109 = !DILocation(line: 20, column: 53, scope: !66)
!110 = !DILocation(line: 20, column: 62, scope: !66)
!111 = !DILocation(line: 20, column: 74, scope: !66)
!112 = !DILocation(line: 20, column: 68, scope: !66)
!113 = !DILocation(line: 20, column: 77, scope: !66)
!114 = !DILocation(line: 20, column: 66, scope: !66)
!115 = !DILocation(line: 20, column: 85, scope: !66)
!116 = !DILocation(line: 20, column: 87, scope: !66)
!117 = !DILocation(line: 20, column: 82, scope: !66)
!118 = !DILocation(line: 0, scope: !66)
!119 = !DILocation(line: 20, column: 3, scope: !66)
!120 = !DILocation(line: 21, column: 3, scope: !66)
!121 = !DILocation(line: 22, column: 1, scope: !66)
