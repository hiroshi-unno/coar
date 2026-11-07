; ModuleID = 'passes/ptrparam.c'
source_filename = "passes/ptrparam.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @get(ptr noundef %0, i32 noundef %1) #0 !dbg !10 {
  %3 = alloca ptr, align 8
  %4 = alloca i32, align 4
  store ptr %0, ptr %3, align 8
    #dbg_declare(ptr %3, !16, !DIExpression(), !17)
  store i32 %1, ptr %4, align 4
    #dbg_declare(ptr %4, !18, !DIExpression(), !19)
  %5 = load ptr, ptr %3, align 8, !dbg !20
  %6 = load i32, ptr %4, align 4, !dbg !21
  %7 = sext i32 %6 to i64, !dbg !20
  %8 = getelementptr inbounds i32, ptr %5, i64 %7, !dbg !20
  %9 = load i32, ptr %8, align 4, !dbg !20
  ret i32 %9, !dbg !22
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !23 {
  %1 = alloca i32, align 4
  %2 = alloca [2 x i32], align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !26, !DIExpression(), !30)
  call void @llvm.memset.p0.i64(ptr align 4 %2, i8 0, i64 8, i1 false), !dbg !30
  %3 = getelementptr inbounds [2 x i32], ptr %2, i64 0, i64 0, !dbg !31
  %4 = call i32 @get(ptr noundef %3, i32 noundef 1), !dbg !32
  ret i32 %4, !dbg !33
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nounwind willreturn memory(argmem: write) }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "passes/ptrparam.c", directory: "/w", checksumkind: CSK_MD5, checksum: "eeed081a5f9d8da666a211b46957524b")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!10 = distinct !DISubprogram(name: "get", scope: !1, file: !1, line: 1, type: !11, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !15)
!11 = !DISubroutineType(types: !12)
!12 = !{!13, !14, !13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !13, size: 64)
!15 = !{}
!16 = !DILocalVariable(name: "p", arg: 1, scope: !10, file: !1, line: 1, type: !14)
!17 = !DILocation(line: 1, column: 14, scope: !10)
!18 = !DILocalVariable(name: "i", arg: 2, scope: !10, file: !1, line: 1, type: !13)
!19 = !DILocation(line: 1, column: 21, scope: !10)
!20 = !DILocation(line: 1, column: 33, scope: !10)
!21 = !DILocation(line: 1, column: 35, scope: !10)
!22 = !DILocation(line: 1, column: 26, scope: !10)
!23 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 2, type: !24, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !15)
!24 = !DISubroutineType(types: !25)
!25 = !{!13}
!26 = !DILocalVariable(name: "a", scope: !23, file: !1, line: 2, type: !27)
!27 = !DICompositeType(tag: DW_TAG_array_type, baseType: !13, size: 64, elements: !28)
!28 = !{!29}
!29 = !DISubrange(count: 2)
!30 = !DILocation(line: 2, column: 22, scope: !23)
!31 = !DILocation(line: 2, column: 48, scope: !23)
!32 = !DILocation(line: 2, column: 44, scope: !23)
!33 = !DILocation(line: 2, column: 37, scope: !23)
