; ModuleID = 'local_init_true.c'
source_filename = "local_init_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@__const.main.a = private unnamed_addr constant [5 x i32] [i32 1, i32 2, i32 3, i32 4, i32 5], align 16

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !27 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #6, !dbg !30
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
  call void @abort() #7, !dbg !43
  unreachable, !dbg !43

6:                                                ; preds = %1
  ret void, !dbg !44
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !45 {
  %1 = alloca i32, align 4
  %2 = alloca [5 x i32], align 16
  %3 = alloca [6 x i32], align 16
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !48, !DIExpression(), !52)
  call void @llvm.memcpy.p0.p0.i64(ptr align 16 %2, ptr align 16 @__const.main.a, i64 20, i1 false), !dbg !52
    #dbg_declare(ptr %3, !53, !DIExpression(), !57)
  call void @llvm.memset.p0.i64(ptr align 16 %3, i8 0, i64 24, i1 false), !dbg !57
    #dbg_declare(ptr %4, !58, !DIExpression(), !59)
  %5 = call i32 @__VERIFIER_nondet_int(), !dbg !60
  store i32 %5, ptr %4, align 4, !dbg !59
  %6 = load i32, ptr %4, align 4, !dbg !61
  %7 = icmp slt i32 %6, 0, !dbg !63
  br i1 %7, label %11, label %8, !dbg !64

8:                                                ; preds = %0
  %9 = load i32, ptr %4, align 4, !dbg !65
  %10 = icmp sge i32 %9, 5, !dbg !66
  br i1 %10, label %11, label %12, !dbg !67

11:                                               ; preds = %8, %0
  store i32 0, ptr %1, align 4, !dbg !68
  br label %29, !dbg !68

12:                                               ; preds = %8
  %13 = load i32, ptr %4, align 4, !dbg !69
  %14 = sext i32 %13 to i64, !dbg !70
  %15 = getelementptr inbounds [5 x i32], ptr %2, i64 0, i64 %14, !dbg !70
  %16 = load i32, ptr %15, align 4, !dbg !70
  %17 = load i32, ptr %4, align 4, !dbg !71
  %18 = add nsw i32 %17, 1, !dbg !72
  %19 = icmp eq i32 %16, %18, !dbg !73
  br i1 %19, label %20, label %26, !dbg !74

20:                                               ; preds = %12
  %21 = load i32, ptr %4, align 4, !dbg !75
  %22 = sext i32 %21 to i64, !dbg !76
  %23 = getelementptr inbounds [6 x i32], ptr %3, i64 0, i64 %22, !dbg !76
  %24 = load i32, ptr %23, align 4, !dbg !76
  %25 = icmp eq i32 %24, 0, !dbg !77
  br label %26

26:                                               ; preds = %20, %12
  %27 = phi i1 [ false, %12 ], [ %25, %20 ], !dbg !78
  %28 = zext i1 %27 to i32, !dbg !74
  call void @__VERIFIER_assert(i32 noundef %28), !dbg !79
  store i32 0, ptr %1, align 4, !dbg !80
  br label %29, !dbg !80

29:                                               ; preds = %26, %11
  %30 = load i32, ptr %1, align 4, !dbg !81
  ret i32 %30, !dbg !81
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #3

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #4

declare i32 @__VERIFIER_nondet_int() #5

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #5 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #6 = { noreturn }
attributes #7 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "local_init_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "3aaf5cb729d5e513891779f142da986e")
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
!49 = !DICompositeType(tag: DW_TAG_array_type, baseType: !34, size: 160, elements: !50)
!50 = !{!51}
!51 = !DISubrange(count: 5)
!52 = !DILocation(line: 7, column: 7, scope: !45)
!53 = !DILocalVariable(name: "b", scope: !45, file: !2, line: 8, type: !54)
!54 = !DICompositeType(tag: DW_TAG_array_type, baseType: !34, size: 192, elements: !55)
!55 = !{!56}
!56 = !DISubrange(count: 6)
!57 = !DILocation(line: 8, column: 7, scope: !45)
!58 = !DILocalVariable(name: "k", scope: !45, file: !2, line: 9, type: !34)
!59 = !DILocation(line: 9, column: 7, scope: !45)
!60 = !DILocation(line: 9, column: 11, scope: !45)
!61 = !DILocation(line: 10, column: 7, scope: !62)
!62 = distinct !DILexicalBlock(scope: !45, file: !2, line: 10, column: 7)
!63 = !DILocation(line: 10, column: 9, scope: !62)
!64 = !DILocation(line: 10, column: 13, scope: !62)
!65 = !DILocation(line: 10, column: 16, scope: !62)
!66 = !DILocation(line: 10, column: 18, scope: !62)
!67 = !DILocation(line: 10, column: 7, scope: !45)
!68 = !DILocation(line: 10, column: 24, scope: !62)
!69 = !DILocation(line: 11, column: 23, scope: !45)
!70 = !DILocation(line: 11, column: 21, scope: !45)
!71 = !DILocation(line: 11, column: 29, scope: !45)
!72 = !DILocation(line: 11, column: 31, scope: !45)
!73 = !DILocation(line: 11, column: 26, scope: !45)
!74 = !DILocation(line: 11, column: 35, scope: !45)
!75 = !DILocation(line: 11, column: 40, scope: !45)
!76 = !DILocation(line: 11, column: 38, scope: !45)
!77 = !DILocation(line: 11, column: 43, scope: !45)
!78 = !DILocation(line: 0, scope: !45)
!79 = !DILocation(line: 11, column: 3, scope: !45)
!80 = !DILocation(line: 12, column: 3, scope: !45)
!81 = !DILocation(line: 13, column: 1, scope: !45)
