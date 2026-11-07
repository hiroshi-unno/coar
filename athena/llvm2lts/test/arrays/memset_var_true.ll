; ModuleID = 'memset_var_true.c'
source_filename = "memset_var_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !27 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #5, !dbg !30
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
  call void @abort() #6, !dbg !43
  unreachable, !dbg !43

6:                                                ; preds = %1
  ret void, !dbg !44
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !45 {
  %1 = alloca i32, align 4
  %2 = alloca [10 x i32], align 16
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !48, !DIExpression(), !52)
    #dbg_declare(ptr %3, !53, !DIExpression(), !54)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !55
  store i32 %4, ptr %3, align 4, !dbg !54
  %5 = load i32, ptr %3, align 4, !dbg !56
  %6 = icmp slt i32 %5, 1, !dbg !58
  br i1 %6, label %10, label %7, !dbg !59

7:                                                ; preds = %0
  %8 = load i32, ptr %3, align 4, !dbg !60
  %9 = icmp sgt i32 %8, 10, !dbg !61
  br i1 %9, label %10, label %11, !dbg !62

10:                                               ; preds = %7, %0
  store i32 0, ptr %1, align 4, !dbg !63
  br label %23, !dbg !63

11:                                               ; preds = %7
  %12 = getelementptr inbounds [10 x i32], ptr %2, i64 0, i64 0, !dbg !64
  %13 = load i32, ptr %3, align 4, !dbg !65
  %14 = sext i32 %13 to i64, !dbg !65
  %15 = mul i64 %14, 4, !dbg !66
  call void @llvm.memset.p0.i64(ptr align 16 %12, i8 0, i64 %15, i1 false), !dbg !64
  %16 = load i32, ptr %3, align 4, !dbg !67
  %17 = sub nsw i32 %16, 1, !dbg !68
  %18 = sext i32 %17 to i64, !dbg !69
  %19 = getelementptr inbounds [10 x i32], ptr %2, i64 0, i64 %18, !dbg !69
  %20 = load i32, ptr %19, align 4, !dbg !69
  %21 = icmp eq i32 %20, 0, !dbg !70
  %22 = zext i1 %21 to i32, !dbg !70
  call void @__VERIFIER_assert(i32 noundef %22), !dbg !71
  store i32 0, ptr %1, align 4, !dbg !72
  br label %23, !dbg !72

23:                                               ; preds = %11, %10
  %24 = load i32, ptr %1, align 4, !dbg !73
  ret i32 %24, !dbg !73
}

declare i32 @__VERIFIER_nondet_int() #3

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #4

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #5 = { noreturn }
attributes #6 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "memset_var_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "145d074634ae511509e4efe5d40e1aea")
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
!45 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 6, type: !46, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{!34}
!48 = !DILocalVariable(name: "a", scope: !45, file: !2, line: 7, type: !49)
!49 = !DICompositeType(tag: DW_TAG_array_type, baseType: !34, size: 320, elements: !50)
!50 = !{!51}
!51 = !DISubrange(count: 10)
!52 = !DILocation(line: 7, column: 7, scope: !45)
!53 = !DILocalVariable(name: "n", scope: !45, file: !2, line: 8, type: !34)
!54 = !DILocation(line: 8, column: 7, scope: !45)
!55 = !DILocation(line: 8, column: 11, scope: !45)
!56 = !DILocation(line: 9, column: 7, scope: !57)
!57 = distinct !DILexicalBlock(scope: !45, file: !2, line: 9, column: 7)
!58 = !DILocation(line: 9, column: 9, scope: !57)
!59 = !DILocation(line: 9, column: 13, scope: !57)
!60 = !DILocation(line: 9, column: 16, scope: !57)
!61 = !DILocation(line: 9, column: 18, scope: !57)
!62 = !DILocation(line: 9, column: 7, scope: !45)
!63 = !DILocation(line: 9, column: 24, scope: !57)
!64 = !DILocation(line: 10, column: 3, scope: !45)
!65 = !DILocation(line: 10, column: 26, scope: !45)
!66 = !DILocation(line: 10, column: 28, scope: !45)
!67 = !DILocation(line: 11, column: 23, scope: !45)
!68 = !DILocation(line: 11, column: 25, scope: !45)
!69 = !DILocation(line: 11, column: 21, scope: !45)
!70 = !DILocation(line: 11, column: 30, scope: !45)
!71 = !DILocation(line: 11, column: 3, scope: !45)
!72 = !DILocation(line: 12, column: 3, scope: !45)
!73 = !DILocation(line: 13, column: 1, scope: !45)
