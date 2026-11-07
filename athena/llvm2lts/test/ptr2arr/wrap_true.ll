; ModuleID = 'ptr2arr/wrap_true.c'
source_filename = "ptr2arr/wrap_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

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
define dso_local zeroext i8 @__p2a_wrap_u8(i8 noundef zeroext %0) #0 !dbg !31 {
  %2 = alloca i8, align 1
  store i8 %0, ptr %2, align 1
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %3 = load i8, ptr %2, align 1, !dbg !38
  ret i8 %3, !dbg !39
}

; Function Attrs: noinline nounwind uwtable
define dso_local signext i8 @__p2a_wrap_s8(i8 noundef signext %0) #0 !dbg !40 {
  %2 = alloca i8, align 1
  store i8 %0, ptr %2, align 1
    #dbg_declare(ptr %2, !44, !DIExpression(), !45)
  %3 = load i8, ptr %2, align 1, !dbg !46
  ret i8 %3, !dbg !47
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !48 {
  %1 = alloca i32, align 4
  %2 = alloca i8, align 1
  %3 = alloca i8, align 1
  %4 = alloca i8, align 1
  %5 = alloca i32, align 4
  %6 = alloca i8, align 1
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !52, !DIExpression(), !53)
  %7 = call zeroext i8 @__VERIFIER_nondet_uchar(), !dbg !54
  store i8 %7, ptr %2, align 1, !dbg !53
  %8 = load i8, ptr %2, align 1, !dbg !55
  %9 = zext i8 %8 to i32, !dbg !55
  %10 = icmp ne i32 %9, 255, !dbg !57
  br i1 %10, label %11, label %12, !dbg !58

11:                                               ; preds = %0
  store i32 0, ptr %1, align 4, !dbg !59
  br label %37, !dbg !59

12:                                               ; preds = %0
    #dbg_declare(ptr %3, !60, !DIExpression(), !61)
  %13 = load i8, ptr %2, align 1, !dbg !62
  %14 = zext i8 %13 to i32, !dbg !62
  %15 = add nsw i32 %14, 1, !dbg !63
  %16 = trunc i32 %15 to i8, !dbg !62
  %17 = call zeroext i8 @__p2a_wrap_u8(i8 noundef zeroext %16), !dbg !64
  store i8 %17, ptr %3, align 1, !dbg !61
  %18 = load i8, ptr %3, align 1, !dbg !65
  %19 = zext i8 %18 to i32, !dbg !65
  %20 = icmp ne i32 %19, 0, !dbg !67
  br i1 %20, label %21, label %22, !dbg !68

21:                                               ; preds = %12
  call void @reach_error(), !dbg !69
  br label %22, !dbg !69

22:                                               ; preds = %21, %12
    #dbg_declare(ptr %4, !70, !DIExpression(), !71)
  %23 = call zeroext i8 @__p2a_wrap_u8(i8 noundef zeroext -1), !dbg !72
  store i8 %23, ptr %4, align 1, !dbg !71
  %24 = load i8, ptr %4, align 1, !dbg !73
  %25 = zext i8 %24 to i32, !dbg !73
  %26 = icmp ne i32 %25, 255, !dbg !75
  br i1 %26, label %27, label %28, !dbg !76

27:                                               ; preds = %22
  call void @reach_error(), !dbg !77
  br label %28, !dbg !77

28:                                               ; preds = %27, %22
    #dbg_declare(ptr %5, !78, !DIExpression(), !79)
  store i32 200, ptr %5, align 4, !dbg !79
    #dbg_declare(ptr %6, !80, !DIExpression(), !81)
  %29 = load i32, ptr %5, align 4, !dbg !82
  %30 = trunc i32 %29 to i8, !dbg !82
  %31 = call signext i8 @__p2a_wrap_s8(i8 noundef signext %30), !dbg !83
  store i8 %31, ptr %6, align 1, !dbg !81
  %32 = load i8, ptr %6, align 1, !dbg !84
  %33 = sext i8 %32 to i32, !dbg !84
  %34 = icmp ne i32 %33, -56, !dbg !86
  br i1 %34, label %35, label %36, !dbg !87

35:                                               ; preds = %28
  call void @reach_error(), !dbg !88
  br label %36, !dbg !88

36:                                               ; preds = %35, %28
  store i32 0, ptr %1, align 4, !dbg !89
  br label %37, !dbg !89

37:                                               ; preds = %36, %11
  %38 = load i32, ptr %1, align 4, !dbg !90
  ret i32 %38, !dbg !90
}

declare zeroext i8 @__VERIFIER_nondet_uchar() #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 7, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "ptr2arr/wrap_true.c", directory: "/t", checksumkind: CSK_MD5, checksum: "973e608965750dfa42cc65d7bcb2a55a")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 7, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 7, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!18 = !{!0, !7, !12}
!19 = !{i32 7, !"Dwarf Version", i32 5}
!20 = !{i32 2, !"Debug Info Version", i32 3}
!21 = !{i32 1, !"wchar_size", i32 4}
!22 = !{i32 8, !"PIC Level", i32 2}
!23 = !{i32 7, !"PIE Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!27 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 7, type: !28, scopeLine: 7, spFlags: DISPFlagDefinition, unit: !17)
!28 = !DISubroutineType(types: !29)
!29 = !{null}
!30 = !DILocation(line: 7, column: 22, scope: !27)
!31 = distinct !DISubprogram(name: "__p2a_wrap_u8", scope: !2, file: !2, line: 8, type: !32, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{!34, !34}
!34 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!35 = !{}
!36 = !DILocalVariable(name: "v", arg: 1, scope: !31, file: !2, line: 8, type: !34)
!37 = !DILocation(line: 8, column: 43, scope: !31)
!38 = !DILocation(line: 8, column: 55, scope: !31)
!39 = !DILocation(line: 8, column: 48, scope: !31)
!40 = distinct !DISubprogram(name: "__p2a_wrap_s8", scope: !2, file: !2, line: 9, type: !41, scopeLine: 9, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!41 = !DISubroutineType(types: !42)
!42 = !{!43, !43}
!43 = !DIBasicType(name: "signed char", size: 8, encoding: DW_ATE_signed_char)
!44 = !DILocalVariable(name: "v", arg: 1, scope: !40, file: !2, line: 9, type: !43)
!45 = !DILocation(line: 9, column: 39, scope: !40)
!46 = !DILocation(line: 9, column: 51, scope: !40)
!47 = !DILocation(line: 9, column: 44, scope: !40)
!48 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 10, type: !49, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!49 = !DISubroutineType(types: !50)
!50 = !{!51}
!51 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!52 = !DILocalVariable(name: "x", scope: !48, file: !2, line: 11, type: !34)
!53 = !DILocation(line: 11, column: 17, scope: !48)
!54 = !DILocation(line: 11, column: 21, scope: !48)
!55 = !DILocation(line: 12, column: 7, scope: !56)
!56 = distinct !DILexicalBlock(scope: !48, file: !2, line: 12, column: 7)
!57 = !DILocation(line: 12, column: 9, scope: !56)
!58 = !DILocation(line: 12, column: 7, scope: !48)
!59 = !DILocation(line: 12, column: 17, scope: !56)
!60 = !DILocalVariable(name: "y", scope: !48, file: !2, line: 13, type: !34)
!61 = !DILocation(line: 13, column: 17, scope: !48)
!62 = !DILocation(line: 13, column: 35, scope: !48)
!63 = !DILocation(line: 13, column: 37, scope: !48)
!64 = !DILocation(line: 13, column: 21, scope: !48)
!65 = !DILocation(line: 14, column: 7, scope: !66)
!66 = distinct !DILexicalBlock(scope: !48, file: !2, line: 14, column: 7)
!67 = !DILocation(line: 14, column: 9, scope: !66)
!68 = !DILocation(line: 14, column: 7, scope: !48)
!69 = !DILocation(line: 14, column: 15, scope: !66)
!70 = !DILocalVariable(name: "z", scope: !48, file: !2, line: 15, type: !34)
!71 = !DILocation(line: 15, column: 17, scope: !48)
!72 = !DILocation(line: 15, column: 21, scope: !48)
!73 = !DILocation(line: 16, column: 7, scope: !74)
!74 = distinct !DILexicalBlock(scope: !48, file: !2, line: 16, column: 7)
!75 = !DILocation(line: 16, column: 9, scope: !74)
!76 = !DILocation(line: 16, column: 7, scope: !48)
!77 = !DILocation(line: 16, column: 17, scope: !74)
!78 = !DILocalVariable(name: "w", scope: !48, file: !2, line: 17, type: !51)
!79 = !DILocation(line: 17, column: 7, scope: !48)
!80 = !DILocalVariable(name: "s", scope: !48, file: !2, line: 18, type: !43)
!81 = !DILocation(line: 18, column: 15, scope: !48)
!82 = !DILocation(line: 18, column: 33, scope: !48)
!83 = !DILocation(line: 18, column: 19, scope: !48)
!84 = !DILocation(line: 19, column: 7, scope: !85)
!85 = distinct !DILexicalBlock(scope: !48, file: !2, line: 19, column: 7)
!86 = !DILocation(line: 19, column: 9, scope: !85)
!87 = !DILocation(line: 19, column: 7, scope: !48)
!88 = !DILocation(line: 19, column: 17, scope: !85)
!89 = !DILocation(line: 20, column: 3, scope: !48)
!90 = !DILocation(line: 21, column: 1, scope: !48)
