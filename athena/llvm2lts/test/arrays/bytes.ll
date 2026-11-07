; ModuleID = 'bytes.c'
source_filename = "bytes.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !29 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !32
  unreachable, !dbg !32
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !33 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !38, !DIExpression(), !39)
  %3 = load i32, ptr %2, align 4, !dbg !40
  %4 = icmp ne i32 %3, 0, !dbg !40
  br i1 %4, label %6, label %5, !dbg !42

5:                                                ; preds = %1
  call void @reach_error(), !dbg !43
  call void @abort() #5, !dbg !45
  unreachable, !dbg !45

6:                                                ; preds = %1
  ret void, !dbg !46
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !47 {
  %1 = alloca i32, align 4
  %2 = alloca [2 x i32], align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !50, !DIExpression(), !52)
  call void @llvm.memset.p0.i64(ptr align 4 %2, i8 0, i64 8, i1 false), !dbg !52
  %3 = getelementptr inbounds [2 x i32], ptr %2, i64 0, i64 0, !dbg !53
  %4 = getelementptr inbounds i8, ptr %3, i64 1, !dbg !53
  store i8 1, ptr %4, align 1, !dbg !54
  %5 = getelementptr inbounds [2 x i32], ptr %2, i64 0, i64 0, !dbg !55
  %6 = load i32, ptr %5, align 4, !dbg !55
  %7 = icmp eq i32 %6, 256, !dbg !56
  %8 = zext i1 %7 to i32, !dbg !56
  call void @__VERIFIER_assert(i32 noundef %8), !dbg !57
  ret i32 0, !dbg !58
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!21, !22, !23, !24, !25, !26, !27}
!llvm.ident = !{!28}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "bytes.c", directory: "/w", checksumkind: CSK_MD5, checksum: "33a8665d5ef00776f2754e8f35472277")
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
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, retainedTypes: !18, globals: !20, splitDebugInlining: false, nameTableKind: None)
!18 = !{!19}
!19 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !4, size: 64)
!20 = !{!0, !7, !12}
!21 = !{i32 7, !"Dwarf Version", i32 5}
!22 = !{i32 2, !"Debug Info Version", i32 3}
!23 = !{i32 1, !"wchar_size", i32 4}
!24 = !{i32 8, !"PIC Level", i32 2}
!25 = !{i32 7, !"PIE Level", i32 2}
!26 = !{i32 7, !"uwtable", i32 2}
!27 = !{i32 7, !"frame-pointer", i32 2}
!28 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!29 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !30, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !17)
!30 = !DISubroutineType(types: !31)
!31 = !{null}
!32 = !DILocation(line: 4, column: 22, scope: !29)
!33 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !34, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !37)
!34 = !DISubroutineType(types: !35)
!35 = !{null, !36}
!36 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!37 = !{}
!38 = !DILocalVariable(name: "cond", arg: 1, scope: !33, file: !2, line: 5, type: !36)
!39 = !DILocation(line: 5, column: 28, scope: !33)
!40 = !DILocation(line: 5, column: 41, scope: !41)
!41 = distinct !DILexicalBlock(scope: !33, file: !2, line: 5, column: 40)
!42 = !DILocation(line: 5, column: 40, scope: !33)
!43 = !DILocation(line: 5, column: 49, scope: !44)
!44 = distinct !DILexicalBlock(scope: !41, file: !2, line: 5, column: 47)
!45 = !DILocation(line: 5, column: 64, scope: !44)
!46 = !DILocation(line: 5, column: 75, scope: !33)
!47 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 6, type: !48, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !37)
!48 = !DISubroutineType(types: !49)
!49 = !{!36}
!50 = !DILocalVariable(name: "a", scope: !47, file: !2, line: 7, type: !51)
!51 = !DICompositeType(tag: DW_TAG_array_type, baseType: !36, size: 64, elements: !5)
!52 = !DILocation(line: 7, column: 7, scope: !47)
!53 = !DILocation(line: 8, column: 3, scope: !47)
!54 = !DILocation(line: 8, column: 18, scope: !47)
!55 = !DILocation(line: 9, column: 21, scope: !47)
!56 = !DILocation(line: 9, column: 26, scope: !47)
!57 = !DILocation(line: 9, column: 3, scope: !47)
!58 = !DILocation(line: 10, column: 3, scope: !47)
