; ModuleID = 'ptr2arr/printf_true.c'
source_filename = "ptr2arr/printf_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@.str.3 = private unnamed_addr constant [6 x i8] c"x=%d\0A\00", align 1, !dbg !17
@.str.4 = private unnamed_addr constant [6 x i8] c"hello\00", align 1, !dbg !22

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !34 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #3, !dbg !37
  unreachable, !dbg !37
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !38 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !43, !DIExpression(), !44)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !45
  store i32 %4, ptr %2, align 4, !dbg !44
  %5 = load i32, ptr %2, align 4, !dbg !46
  %6 = icmp slt i32 %5, 0, !dbg !48
  br i1 %6, label %10, label %7, !dbg !49

7:                                                ; preds = %0
  %8 = load i32, ptr %2, align 4, !dbg !50
  %9 = icmp sgt i32 %8, 10, !dbg !51
  br i1 %9, label %10, label %11, !dbg !52

10:                                               ; preds = %7, %0
  store i32 0, ptr %1, align 4, !dbg !53
  br label %23, !dbg !53

11:                                               ; preds = %7
  %12 = load i32, ptr %2, align 4, !dbg !54
  %13 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, i32 noundef %12), !dbg !55
  %14 = call i32 @puts(ptr noundef @.str.4), !dbg !56
    #dbg_declare(ptr %3, !57, !DIExpression(), !58)
  %15 = call i32 @putchar(i32 noundef 97), !dbg !59
  store i32 %15, ptr %3, align 4, !dbg !58
  %16 = load i32, ptr %2, align 4, !dbg !60
  %17 = icmp sgt i32 %16, 10, !dbg !62
  br i1 %17, label %18, label %19, !dbg !63

18:                                               ; preds = %11
  call void @reach_error(), !dbg !64
  br label %19, !dbg !64

19:                                               ; preds = %18, %11
  %20 = load i32, ptr %3, align 4, !dbg !65
  %21 = load i32, ptr %3, align 4, !dbg !66
  %22 = sub nsw i32 %20, %21, !dbg !67
  store i32 %22, ptr %1, align 4, !dbg !68
  br label %23, !dbg !68

23:                                               ; preds = %19, %10
  %24 = load i32, ptr %1, align 4, !dbg !69
  ret i32 %24, !dbg !69
}

declare i32 @__VERIFIER_nondet_int() #2

declare i32 @printf(ptr noundef, ...) #2

declare i32 @puts(ptr noundef) #2

declare i32 @putchar(i32 noundef) #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn }

!llvm.dbg.cu = !{!24}
!llvm.module.flags = !{!26, !27, !28, !29, !30, !31, !32}
!llvm.ident = !{!33}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 8, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "ptr2arr/printf_true.c", directory: "/t", checksumkind: CSK_MD5, checksum: "9dcd993685c3977205d7619a10233bf2")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 8, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 8, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(scope: null, file: !2, line: 12, type: !19, isLocal: true, isDefinition: true)
!19 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 48, elements: !20)
!20 = !{!21}
!21 = !DISubrange(count: 6)
!22 = !DIGlobalVariableExpression(var: !23, expr: !DIExpression())
!23 = distinct !DIGlobalVariable(scope: null, file: !2, line: 13, type: !19, isLocal: true, isDefinition: true)
!24 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !25, splitDebugInlining: false, nameTableKind: None)
!25 = !{!0, !7, !12, !17, !22}
!26 = !{i32 7, !"Dwarf Version", i32 5}
!27 = !{i32 2, !"Debug Info Version", i32 3}
!28 = !{i32 1, !"wchar_size", i32 4}
!29 = !{i32 8, !"PIC Level", i32 2}
!30 = !{i32 7, !"PIE Level", i32 2}
!31 = !{i32 7, !"uwtable", i32 2}
!32 = !{i32 7, !"frame-pointer", i32 2}
!33 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!34 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 8, type: !35, scopeLine: 8, spFlags: DISPFlagDefinition, unit: !24)
!35 = !DISubroutineType(types: !36)
!36 = !{null}
!37 = !DILocation(line: 8, column: 22, scope: !34)
!38 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 9, type: !39, scopeLine: 9, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !24, retainedNodes: !42)
!39 = !DISubroutineType(types: !40)
!40 = !{!41}
!41 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!42 = !{}
!43 = !DILocalVariable(name: "x", scope: !38, file: !2, line: 10, type: !41)
!44 = !DILocation(line: 10, column: 7, scope: !38)
!45 = !DILocation(line: 10, column: 11, scope: !38)
!46 = !DILocation(line: 11, column: 7, scope: !47)
!47 = distinct !DILexicalBlock(scope: !38, file: !2, line: 11, column: 7)
!48 = !DILocation(line: 11, column: 9, scope: !47)
!49 = !DILocation(line: 11, column: 13, scope: !47)
!50 = !DILocation(line: 11, column: 16, scope: !47)
!51 = !DILocation(line: 11, column: 18, scope: !47)
!52 = !DILocation(line: 11, column: 7, scope: !38)
!53 = !DILocation(line: 11, column: 24, scope: !47)
!54 = !DILocation(line: 12, column: 20, scope: !38)
!55 = !DILocation(line: 12, column: 3, scope: !38)
!56 = !DILocation(line: 13, column: 3, scope: !38)
!57 = !DILocalVariable(name: "r", scope: !38, file: !2, line: 14, type: !41)
!58 = !DILocation(line: 14, column: 7, scope: !38)
!59 = !DILocation(line: 14, column: 11, scope: !38)
!60 = !DILocation(line: 15, column: 7, scope: !61)
!61 = distinct !DILexicalBlock(scope: !38, file: !2, line: 15, column: 7)
!62 = !DILocation(line: 15, column: 9, scope: !61)
!63 = !DILocation(line: 15, column: 7, scope: !38)
!64 = !DILocation(line: 15, column: 15, scope: !61)
!65 = !DILocation(line: 16, column: 10, scope: !38)
!66 = !DILocation(line: 16, column: 14, scope: !38)
!67 = !DILocation(line: 16, column: 12, scope: !38)
!68 = !DILocation(line: 16, column: 3, scope: !38)
!69 = !DILocation(line: 17, column: 1, scope: !38)
