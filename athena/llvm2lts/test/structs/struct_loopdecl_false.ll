; ModuleID = 'struct_loopdecl_false.c'
source_filename = "struct_loopdecl_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.P = type { i32, i32 }

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
define dso_local i32 @main() #0 !dbg !45 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca %struct.P, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !48, !DIExpression(), !50)
  store i32 0, ptr %2, align 4, !dbg !50
  br label %4, !dbg !51

4:                                                ; preds = %18, %0
  %5 = load i32, ptr %2, align 4, !dbg !52
  %6 = icmp slt i32 %5, 2, !dbg !54
  br i1 %6, label %7, label %21, !dbg !55

7:                                                ; preds = %4
    #dbg_declare(ptr %3, !56, !DIExpression(), !62)
  %8 = load i32, ptr %2, align 4, !dbg !63
  %9 = icmp eq i32 %8, 0, !dbg !65
  br i1 %9, label %10, label %12, !dbg !66

10:                                               ; preds = %7
  %11 = getelementptr inbounds %struct.P, ptr %3, i32 0, i32 1, !dbg !67
  store i32 1, ptr %11, align 4, !dbg !68
  br label %17, !dbg !69

12:                                               ; preds = %7
  %13 = getelementptr inbounds %struct.P, ptr %3, i32 0, i32 1, !dbg !70
  %14 = load i32, ptr %13, align 4, !dbg !70
  %15 = icmp eq i32 %14, 1, !dbg !71
  %16 = zext i1 %15 to i32, !dbg !71
  call void @__VERIFIER_assert(i32 noundef %16), !dbg !72
  br label %17

17:                                               ; preds = %12, %10
  br label %18, !dbg !73

18:                                               ; preds = %17
  %19 = load i32, ptr %2, align 4, !dbg !74
  %20 = add nsw i32 %19, 1, !dbg !74
  store i32 %20, ptr %2, align 4, !dbg !74
  br label %4, !dbg !75, !llvm.loop !76

21:                                               ; preds = %4
  ret i32 0, !dbg !78
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
!2 = !DIFile(filename: "struct_loopdecl_false.c", directory: "/w", checksumkind: CSK_MD5, checksum: "f6dfe272f86d5c9f933f6818e5ef5a43")
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
!45 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 7, type: !46, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{!34}
!48 = !DILocalVariable(name: "i", scope: !49, file: !2, line: 8, type: !34)
!49 = distinct !DILexicalBlock(scope: !45, file: !2, line: 8, column: 3)
!50 = !DILocation(line: 8, column: 12, scope: !49)
!51 = !DILocation(line: 8, column: 8, scope: !49)
!52 = !DILocation(line: 8, column: 19, scope: !53)
!53 = distinct !DILexicalBlock(scope: !49, file: !2, line: 8, column: 3)
!54 = !DILocation(line: 8, column: 21, scope: !53)
!55 = !DILocation(line: 8, column: 3, scope: !49)
!56 = !DILocalVariable(name: "p", scope: !57, file: !2, line: 9, type: !58)
!57 = distinct !DILexicalBlock(scope: !53, file: !2, line: 8, column: 31)
!58 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "P", file: !2, line: 6, size: 64, elements: !59)
!59 = !{!60, !61}
!60 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !58, file: !2, line: 6, baseType: !34, size: 32)
!61 = !DIDerivedType(tag: DW_TAG_member, name: "y", scope: !58, file: !2, line: 6, baseType: !34, size: 32, offset: 32)
!62 = !DILocation(line: 9, column: 14, scope: !57)
!63 = !DILocation(line: 10, column: 9, scope: !64)
!64 = distinct !DILexicalBlock(scope: !57, file: !2, line: 10, column: 9)
!65 = !DILocation(line: 10, column: 11, scope: !64)
!66 = !DILocation(line: 10, column: 9, scope: !57)
!67 = !DILocation(line: 10, column: 19, scope: !64)
!68 = !DILocation(line: 10, column: 21, scope: !64)
!69 = !DILocation(line: 10, column: 17, scope: !64)
!70 = !DILocation(line: 11, column: 30, scope: !64)
!71 = !DILocation(line: 11, column: 32, scope: !64)
!72 = !DILocation(line: 11, column: 10, scope: !64)
!73 = !DILocation(line: 12, column: 3, scope: !57)
!74 = !DILocation(line: 8, column: 27, scope: !53)
!75 = !DILocation(line: 8, column: 3, scope: !53)
!76 = distinct !{!76, !55, !77}
!77 = !DILocation(line: 12, column: 3, scope: !49)
!78 = !DILocation(line: 13, column: 3, scope: !45)
