; ModuleID = 'ptr2arr/region_true.c'
source_filename = "ptr2arr/region_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@p2a_mem0 = dso_local global [100 x i32] zeroinitializer, align 16, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !33 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #2, !dbg !36
  unreachable, !dbg !36
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__p2a_arbitrary_p2a_mem0() #0 !dbg !37 {
  ret void, !dbg !38
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !39 {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  call void @__p2a_arbitrary_p2a_mem0(), !dbg !42
  store i32 7, ptr getelementptr inbounds ([100 x i32], ptr @p2a_mem0, i64 0, i64 1), align 4, !dbg !43
  %2 = load i32, ptr getelementptr inbounds ([100 x i32], ptr @p2a_mem0, i64 0, i64 1), align 4, !dbg !44
  %3 = icmp ne i32 %2, 7, !dbg !46
  br i1 %3, label %4, label %5, !dbg !47

4:                                                ; preds = %0
  call void @reach_error(), !dbg !48
  br label %5, !dbg !48

5:                                                ; preds = %4, %0
  ret i32 0, !dbg !49
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!25, !26, !27, !28, !29, !30, !31}
!llvm.ident = !{!32}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 5, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "ptr2arr/region_true.c", directory: "/t", checksumkind: CSK_MD5, checksum: "8d732478223112d2269958a3aee10fc9")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 5, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 5, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "p2a_mem0", scope: !19, file: !2, line: 6, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DICompositeType(tag: DW_TAG_array_type, baseType: !22, size: 3200, elements: !23)
!22 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!23 = !{!24}
!24 = !DISubrange(count: 100)
!25 = !{i32 7, !"Dwarf Version", i32 5}
!26 = !{i32 2, !"Debug Info Version", i32 3}
!27 = !{i32 1, !"wchar_size", i32 4}
!28 = !{i32 8, !"PIC Level", i32 2}
!29 = !{i32 7, !"PIE Level", i32 2}
!30 = !{i32 7, !"uwtable", i32 2}
!31 = !{i32 7, !"frame-pointer", i32 2}
!32 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!33 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 5, type: !34, scopeLine: 5, spFlags: DISPFlagDefinition, unit: !19)
!34 = !DISubroutineType(types: !35)
!35 = !{null}
!36 = !DILocation(line: 5, column: 22, scope: !33)
!37 = distinct !DISubprogram(name: "__p2a_arbitrary_p2a_mem0", scope: !2, file: !2, line: 7, type: !34, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19)
!38 = !DILocation(line: 7, column: 39, scope: !37)
!39 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 8, type: !40, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19)
!40 = !DISubroutineType(types: !41)
!41 = !{!22}
!42 = !DILocation(line: 9, column: 3, scope: !39)
!43 = !DILocation(line: 10, column: 15, scope: !39)
!44 = !DILocation(line: 11, column: 7, scope: !45)
!45 = distinct !DILexicalBlock(scope: !39, file: !2, line: 11, column: 7)
!46 = !DILocation(line: 11, column: 19, scope: !45)
!47 = !DILocation(line: 11, column: 7, scope: !39)
!48 = !DILocation(line: 11, column: 25, scope: !45)
!49 = !DILocation(line: 12, column: 3, scope: !39)
