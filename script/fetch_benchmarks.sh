#!/bin/bash
# Fetch, or build from a submodule, the benchmark corpora this repository uses but does not ship.
#
# A corpus that exists elsewhere is not redistributed here: it is either a git submodule pinned at
# a commit, or it is fetched by this script from a pinned archive with a checksum.  Some corpora
# are read by scripts and configurations at a path of this tree's own (a directory per expected
# verdict, a split for training, a fixed file name), so this script also *materialises* them:
# it places the upstream files at those paths, as a copy or a symbolic link, and applies the small
# local patch a corpus needs.  Each such corpus has a manifest, script/fetch/<name>.manifest, one
# line per file:
#
#   source <TAB> destination <TAB> sha256
#
# where the source is a path inside the archive or the submodule ('-' when unpacking the archive
# already puts the file at its destination), the destination is a path from the repository root,
# and the sha256 is that of the file this script must produce.  Every file is checked against it
# after placing, so a moved upstream, a changed archive or a submodule at another commit is
# reported rather than silently measured.  Destinations are in .gitignore.
#
# A corpus whose files this repository patched, or whose file names state a verdict that is wrong
# for the program, has a note script/fetch/<name>.notes.md, which is copied to DEST/NOTES.md: the
# corpus is untracked, so the note has to arrive with it to survive a re-fetch.  It is this
# repository's own file, so it is also installed (or refreshed) in a corpus that is already
# present, and the manifest check does not count it as an extra file.
#
#   script/fetch_benchmarks.sh                    list what there is and whether it is present
#   script/fetch_benchmarks.sh QF_UF tacas2014    fetch those
#   script/fetch_benchmarks.sh smtlib             every SMT-LIB logic listed below
#   script/fetch_benchmarks.sh materialised       every corpus that has a manifest
#   script/fetch_benchmarks.sh --verify NAME ...  check a present corpus against its manifest
#
# Run it from the repository root.  Nothing is ever overwritten: a target that already has
# files is left alone and reported, so re-running the script is safe.  A corpus built from a
# submodule checks the submodule out first (git submodule update --init, which needs the network
# unless the submodule's store is already in .git/modules).
#
# WHY THE SMT-LIB LOGICS ARE HERE.  They were nine git submodules of
# clc-gitlab.cs.uiowa.edu:2443 from 2020 until 2026-09-14.  None was ever checked out, the port
# stopped answering, and SMT-LIB itself moved: smt-lib.org now names Zenodo (releases from 2023
# on) and StarExec (2013-2023) as the distribution channels and does not mention that GitLab.
# The Zenodo releases are published per logic, as <LOGIC>.tar.zst inside one record.  A record id
# pins better than the submodules did: a Zenodo record is immutable, where those repositories
# were force-pushed on each release.
#
# NOT HERE, ON PURPOSE: benchmarks/SMT/QF_CDT.  That logic no longer exists in SMT-LIB -- it is
# absent from the 2023, 2024 and 2025 releases, and its file names have no overlap with QF_DT,
# so it was not folded into that either.  The copy in this tree is tracked and stays tracked;
# there is nothing left to fetch it from.

set -u

# SMT-LIB release 2025 (non-incremental).  Its files are <LOGIC>.tar.zst, unpacking as
# non-incremental/<LOGIC>/<family>/..., which is why the untar strips two components: the
# convention in this tree is that benchmarks/SMT/<LOGIC>/ holds the families directly.
# Overridable for the QF_* logics, because a record is a *release*: SMTLIB_RECORD=11061097 fetches
# the 2024 one.  The two quantified logics below are pinned to 15493090 instead, since their
# manifests record that release's files.
# Zenodo answers 504 on a record whose files are momentarily unavailable, and it does so for
# minutes at a time -- the retries below are for that, and a persistent 504 means try later or
# pin an earlier release, not that the name or the URL is wrong.
SMTLIB_RECORD=${SMTLIB_RECORD:-15493090}
SMTLIB_LOGICS="QF_ALIA QF_DT QF_LIA QF_LIRA QF_LRA QF_NIA QF_NIRA QF_NRA QF_UF"
MATERIALISED="qsmt-lra qsmt-lia qsmt-cav24 pcsat-rl sygus-compare tacas2014 cav2018term fse2022 adtrem-ijcar20 cav2015ltl rethfl-ack ltlverp recheck-tacas26 popl2024 rethfl-inputs hflmc2-inputs muhfl-inputs"
MANIFESTS=script/fetch

# Sets DEST, URL (or SUB), KIND, NOTE and, where it is pinned, SHA256 (of the downloaded archive),
# RANGE (the byte range of URL that is the archive, when it is one member of a larger one), COMMIT and SPARSE (of a git source read without a submodule), MANIFEST and PATCH, and for a generated corpus
# GEN, the script that writes DEST.
entry() {
  DEST=""; URL=""; SUB=""; KIND=""; NOTE=""; SHA256=""; RANGE=""; COMMIT=""; SPARSE=""; MANIFEST=""; PATCH=""; MD5=""; SIZE=""; GEN=""
  DSPREFIX=""; DSTAKE=""; DSGZIP=""
  case $1 in
  QF_*)
    DEST="benchmarks/SMT/$1"
    URL="https://zenodo.org/api/records/$SMTLIB_RECORD/files/$1.tar.zst/content"
    KIND=tar_zst_strip2
    NOTE="SMT-LIB release 2025 (non-incremental), Zenodo record $SMTLIB_RECORD"
    ;;
  qsmt-lra | qsmt-lia)
    # The quantified linear real and integer arithmetic logics LRA and LIA, all of each.
    local L; L=$(echo "${1#qsmt-}" | tr a-z A-Z)
    DEST="benchmarks/QSMT/$L"
    URL="https://zenodo.org/api/records/15493090/files/$L.tar.zst/content"
    KIND=tar_zst_strip2
    case $L in
    LRA) SHA256=89f73c32150ccc1fdbda3dcb459e4c687a75bea2a96cb53a6d5f7f9c55c67bae ;;
    LIA) SHA256=4b402d114016530fce7677b7c3f4066b567f3aa0dda4d5bd23e7c7b92545adcb ;;
    esac
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="SMT-LIB release 2025 (non-incremental) $L, Zenodo record 15493090"
    ;;
  qsmt-cav24)
    # The quantified linear integer arithmetic benchmarks of Murphy and Kincaid, Quantified Linear Arithmetic
    # Satisfiability via Fine-Grained Strategy Improvement, CAV 2024, that SMT-LIB 2025 does not carry: Simulation
    # (2,060 formulas, weak simulation of two message-passing programs for n steps), Termination (170 sufficient
    # conditions for termination; the paper's 30 polybench ones are not in the artifact) and 191 files of SMT-LIB's
    # LIA family 20190429-UltimateAutomizerSvcomp2019 that later releases dropped.  The artifact is the branch
    # cav2024-artifact of the authors' srk fork, which states no licence, so it is fetched and never shipped.  The
    # expected verdicts, read from the artifact's own result files, are script/fetch/qsmt-cav24.expected.
    DEST="benchmarks/QSMT/cav2024"
    URL="https://github.com/tm507211/srk.git"
    COMMIT=521160295f94b366206325ab36a442ad3ccdb0cc
    SPARSE="/benchmarks/simulation/ /benchmarks/termination/ /benchmarks/smt-comp/LIA/20190429-UltimateAutomizerSvcomp2019/"
    KIND=git_sparse_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="Murphy-Kincaid CAV 2024 artifact (tm507211/srk cav2024-artifact): Simulation, Termination, old SMT-LIB LIA"
    ;;
  pcsat-rl)
    # PCSat's reinforcement-learning inputs: the 858 invariant-synthesis problems of SyGuS-Comp
    # 2019, each named <family>-<file>, split twice -- learn/test (687/171) and sp0..sp4 for
    # cross-validation.  The learner's configurations glob these directories.
    DEST="benchmarks/SyGuS/pcsat_rl"
    SUB="benchmarks/sygus-comp"
    KIND=links
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="SyGuS-Comp 2019 Inv_Track from the sygus-comp submodule, as symbolic links"
    ;;
  sygus-compare)
    DEST="benchmarks/sygus-comp19-inv/compare"
    SUB="benchmarks/sygus-comp"
    KIND=links
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="81 SyGuS-Comp 2019 Inv_Track problems from the sygus-comp submodule, as symbolic links"
    ;;
  tacas2014)
    # Chen, Cook, Fuhs, Nimkar and O'Hearn, Proving Nontermination via Safety, TACAS 2014: the
    # authors' benchmark archive.  This tree sorts the 492 programs by the paper's status into
    # terminating/, nonterminating/ and unknown/ -- the directory is the expected verdict -- so
    # the manifest maps each archive path to its verdict directory.  The page answers on http only,
    # which is why the archive's checksum is pinned.
    DEST="benchmarks/LTS/tacas2014"
    URL="http://www0.cs.ucl.ac.uk/staff/C.Fuhs/safety-nontermination/test_suite.zip"
    SHA256=496f510db0992707bc4dad8e455b20fbbef45e4630b54cbcb3873a46298dcc23
    KIND=zip_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="TACAS 2014 nontermination benchmarks (Chen et al.), the authors' test_suite.zip"
    ;;
  recheck-tacas26)
    # Hamana and Emoto, ReCheck (TACAS 2026): the artifact's 16 OCaml programs, each asserting an
    # equation between two pure functional expressions (map-map fusion, append associativity,
    # take of an infinite list, ...), which its authors ran through MoCHi and through RCaml with
    # PCSat and with Spacer.  Only those inputs are placed; the archive also holds ReCheck's own
    # sources, the Timbuk encodings and the other tools' logs.  Zenodo record 17493184, BSD-3-Clause.
    DEST="benchmarks/OCaml/recheck"
    URL="https://zenodo.org/api/records/17493184/files/reck.zip/content"
    SHA256=58fe8570f4e9f370596fa9bec5da679eebdac9183bf91fa2dc7e51ef24e8eccd
    KIND=zip_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="ReCheck TACAS 2026 artifact's OCaml programs (16), Zenodo record 17493184"
    ;;
  popl2024)
    # Heim and Dimitrova, Solving Infinite-State Games via Acceleration (POPL 2024): the artifact's 47 muCLP
    # inputs, benchmarks/hes/ of artifact-content.zip.  Zenodo record 8424953 holds one 3.8 GB zip (md5
    # 2b9ba986b1d85edfac6b7e724ccd4b1d) of a virtual machine image and that 68 MB zip, which it stores
    # uncompressed at bytes 78-70949203; only that range is downloaded, and SHA256 is the inner zip's.  The
    # same zip's benchmarks/ holds each input's game as a .rpg file (MIT licence, benchmarks/LICENSE), and
    # rpgencode (rpglib at 2ddb0a8) writes all 47 inputs from those games byte for byte (`rpgencode muclp <
    # NAME.rpg`).
    DEST="benchmarks/muCLP/popl2024"
    URL="https://zenodo.org/api/records/8424953/files/artifact-popl2024-60.zip/content"
    RANGE=78-70949203
    SHA256=c299966828fb525b73c46cf45b560108ecca1f3297beb0620f5b0eaf920bf6fb
    KIND=zip_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="POPL 2024 (Heim, Dimitrova) artifact's muCLP inputs (47), Zenodo record 8424953, one byte range"
    ;;
  cav2018term)
    # The C termination benchmarks of the aeval repository, branch term, directory c_bench_term.
    # Upstream's term_02.c and term_03.c declare y twice and never declare z, so they do not
    # compile; the patch renames the second declaration.
    DEST="benchmarks/C/cav2018term"
    SUB="benchmarks/aeval"
    KIND=copy_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    PATCH="$MANIFESTS/$1.patch"
    NOTE="aeval (branch term) c_bench_term from the aeval submodule, copied and patched"
    ;;
  fse2022)
    # The FSE 2022 termination-bug benchmarks (programs extracted from real termination bugs, each
    # with a terminating _T and a non-terminating _NT version), directory benchmark/ of the
    # submodule.  The .c files are upstream's bytes.  Upstream calls __VERIFIER_nondet_* functions
    # without declaring them; C accepts that as an implicit declaration, C++ does not, so the patch
    # declares the one nondet function each of the two .cpp files that call one uses.
    DEST="benchmarks/C/fse2022"
    SUB="benchmarks/fse2022-termination"
    KIND=copy_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    PATCH="$MANIFESTS/$1.patch"
    NOTE="FSE 2022 termination benchmarks from the fse2022-termination submodule, copied and patched"
    ;;
  adtrem-ijcar20)
    # De Angelis, Fioravanti, Pettorossi and Proietti, Removing Algebraic Data Types from
    # Constrained Horn Clauses Using Difference Predicates (IJCAR 2020): the authors' archive of 169 problems, each in four
    # forms -- CHC-source (the clauses, SMT-LIB), CHC-source-prolog, CHC-transformed (after ADT
    # removal, for the problems it succeeded on) and DTT-nolemmas (Reynolds and Kuncak's original
    # first-order encoding).  The page still serves it beside the journal version below.  The
    # files are placed as upstream wrote them.  Two inputs of this repository's own are made beside
    # them, in length-lemma/: copies of CHC-source/clam/goal2 and goal4 to which the patch adds a
    # recursive length function and the lemma that it is positive on a non-empty list (a set-info
    # claim the reader must prove before using).  Upstream's own files are not patched.
    DEST="benchmarks/CHC/ADTs/ADTRem-benchmarks"
    URL="https://fmlab.unich.it/adtrem/adtrem-ijcar20/ADTRem-benchmarks.tgz"
    SHA256=6fb3630b6c980a90ec9f5c6d75fe65f368c81a35dfd212a2f39fce54f2ba676c
    KIND=tgz_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    PATCH="$MANIFESTS/$1.patch"
    NOTE="ADTRem IJCAR 2020 benchmarks (169 problems), the authors' archive, and two hinted copies"
    ;;
  cav2015ltl)
    # The LTL benchmarks of Dietsch, Heizmann, Langenfeld and Podelski, Fairness Modulo Theory, CAV
    # 2015: the coolant examples, Cook and Koskinen's decision-predicates programs and the RERS 2012
    # problems, from the Ultimate repository's examples.  That repository is about 1 GB, so it is
    # neither a submodule nor cloned: a blob-less, depth-1 clone of the pinned commit checks out only
    # the three directories.  Upstream's 13-windows_os_frag1.c initialises A and R, which it never
    # declares, where it means its globals a and r; the patch writes a and r.
    DEST="benchmarks/C/cav2015ltl"
    URL="https://github.com/ultimate-pa/ultimate.git"
    COMMIT=4636c3456d240cfb917098e460415d4effcbe3ae
    SPARSE="/trunk/examples/LTL/coolant/ /trunk/examples/LTL/koskinen/ltlcmodelchecker-benchmarks/ /trunk/examples/LTL/rers2012/"
    KIND=git_sparse_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    PATCH="$MANIFESTS/$1.patch"
    NOTE="CAV 2015 LTL benchmarks from ultimate-pa/ultimate trunk/examples/LTL, sparse checkout, patched"
    ;;
  ltlverp)
    # The LTL benchmarks of Chatterjee, Goharshady, Goharshady, Karrabi and Zikelic, Sound and Complete Witnesses
    # for Template-Based Verification of LTL Properties on Polynomial Programs, FM 2024: 318 integer programs (297
    # TermComp'22 C-Integer, 21 SV-COMP'22 nla-digbench), each the product with a Buechi automaton of four LTL
    # properties (RA, OV, RC, PR: the automaton of the property, read universally, -p ltsbuchi) and of their
    # negations (RA-not, ...: read existentially, -p ltsexbuchi), in T2's format extended by BUCHI and PRE lines.
    # The repository (GPL-3.0) is 136 MB with its artifact zip and solver binaries, so it is neither a submodule
    # nor cloned: a blob-less, depth-1 fetch of the pinned commit checks out benchmarks/ only.
    DEST="benchmarks/LTS/ltlverp"
    URL="https://github.com/ekgma/LTL-VerP.git"
    COMMIT=bb34e73f54662e29d430773510f12956a6930a12
    SPARSE="/benchmarks/"
    KIND=git_sparse_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="LTL-VerP (FM 2024) product transition systems, sparse checkout of the pinned commit"
    ;;
  rethfl-ack)
    # One extended CHC (disjunctive heads) that ReTHFL -- Katsura, Iwayama, Kobayashi and Tsukada, A New
    # Refinement Type System for Automated nu-HFL(Z) Validity Checking, APLAS 2020 -- generated for its PCSat
    # backend from an Ackermann program, committed upstream as scripts/ack/ack.in.  The repository carries no
    # licence, so the file is fetched rather than shipped.
    DEST="benchmarks/pCSP/rethfl"
    URL="https://github.com/hopv/rethfl.git"
    COMMIT=5ed9d34ebd7c493f4ceb0c56dbf3bd26624806e0
    SPARSE="/scripts/ack/"
    KIND=git_sparse_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="ReTHFL's scripts/ack/ack.in (APLAS 2020 tool), sparse checkout of the pinned commit"
    ;;
  rethfl-inputs|hflmc2-inputs|muhfl-inputs)
    # The HES inputs (.in, .hfl) of three HFL(Z) validity checkers, for -p hfl: ReTHFL (Katsura, Iwayama,
    # Kobayashi and Tsukada, APLAS 2020), hflmc2 = PaHFL (Iwayama, Kobayashi, Suzuki and Tsukada, SAS 2020)
    # and MuHFL (Kobayashi, Tanahashi, Sato and Tsukada, POPL 2023; the repository kamocyc/muapprox).  None of
    # the three repositories carries a licence, so the files are fetched, never shipped.  MuHFL's
    # benchmark/inputs reaches benchmark/prog and benchmark/prog2 through symbolic links, which a sparse
    # checkout would leave dangling, so those two are listed as directories of their own.
    case $1 in
    rethfl-inputs) URL="https://github.com/hopv/rethfl.git"; COMMIT=cca07d6cef8224f585157252f6b958f5ba3a8341
                   SPARSE="/input/"; NOTE="ReTHFL's input/ (HES), sparse checkout of the pinned commit" ;;
    hflmc2-inputs) URL="https://github.com/Hogeyama/hflmc2.git"; COMMIT=79e20958159ecb2cdd06188c2a4ae3c3694f9465
                   SPARSE="/input/"; NOTE="hflmc2's (PaHFL's) input/ (HES), sparse checkout of the pinned commit" ;;
    muhfl-inputs)  URL="https://github.com/kamocyc/muapprox.git"; COMMIT=5fd3a1b6d98e504c6be019e4061dce917610a975
                   SPARSE="/benchmark/inputs/ /benchmark/paper/ /benchmark/prog/ /benchmark/prog2/"
                   NOTE="MuHFL's benchmark inputs (HES), sparse checkout of the pinned commit" ;;
    esac
    DEST="benchmarks/HFL/fetched/${1%-inputs}"
    KIND=git_sparse_patch
    MANIFEST="$MANIFESTS/$1.manifest"
    ;;
  rethfl-aplas2020)
    # The extended CHC systems ReTHFL (the same tool) writes for PCSat on the ten nu-HFL(Z) non-termination
    # benchmarks of its repository (benchmark/inputs/higher_nonterminating/, the inputs of its APLAS 2020
    # experiments), with its default options and with --no-inlining, and for nine of their OCaml versions
    # (ml/*.ml) after ml2hfl -non-termination: 38 systems, generated rather than fetched, by
    # script/gen_rethfl_pcsp.sh with a ReTHFL and an ml2hfl that script must build first (--build DIR, then
    # RETHFL=... ML2HFL=...).  Not in `materialised` because it needs that build.  The systems are deterministic for the
    # pinned ReTHFL commit, so the manifest pins each one; they are not the files ReTHFL wrote in 2020, whose names
    # were random and whose numbering of unknowns and variables came from an older commit.
    DEST="benchmarks/pCSP/rethfl-aplas2020"
    KIND=generate
    GEN=script/gen_rethfl_pcsp.sh
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="ReTHFL's extended CHC for its higher_nonterminating inputs, generated by script/gen_rethfl_pcsp.sh"
    ;;
  linarb-regen)
    # SeaHorn's small-step CHC encoding of the C programs of the LinearArbitrary-SeaHorn submodule, regenerated
    # beside the 2021 set of benchmarks/CHC/LinearArbitrary (generator unrecorded; since 2026-11-03 cut down to the
    # cited files in benchmarks/CHC/LinearArbitrary_kept, the full set read from the history by the generator).
    # script/gen_linear_arbitrary_chc.sh runs SeaHorn's published Docker image, pinned by digest, on every upstream
    # path that script/fetch/linarb-regen.mapping gives for a tracked name, patches the uninitialised-local
    # nondeterminism idiom into an external declaration first, and places only the outputs that pass its checks (SeaHorn found the assertion; z3 does not decide them
    # against the name's verdict or the tracked file's); DEST/MANIFEST.tsv records the image, the command, the
    # submodule commit and every file's hashes and outcome, and every SeaHorn output is compared with the sha256
    # pinned in script/fetch/linarb-regen.pinned (a difference fails the fetch and is listed).  Not a .manifest:
    # which outputs are placed depends on z3's budget, so --verify has nothing fixed to check.  Needs Docker and z3,
    # so it is not in `materialised`.
    DEST="benchmarks/CHC/LinearArbitrary_regen2026"
    SUB="benchmarks/LinearArbitrary-SeaHorn"
    KIND=generate
    GEN=script/gen_linear_arbitrary_chc.sh
    NOTE="LinearArbitrary C programs as SeaHorn small-step CHC, generated in SeaHorn's Docker image"
    ;;
  termcomp-t2)
    # termCOMP's C category (the C/ programs of the TPDB submodule benchmarks/term-comp) as T2 transition systems,
    # translated by CoAR's own Athena route (Ptr2ArrFC on Frama-C, clang 19, llvm2lts) under termCOMP's C reading
    # (integers without a range, unbounded regions, hoisting), in a Docker image script/gen_termcomp_t2.sh builds from
    # this checkout.  It replaces the T2 files the repository tracked under benchmarks/LTS/term-comp, written by an
    # earlier version of the same pipeline; the files whose programs the route refuses are tracked as
    # benchmarks/LTS/term-comp_kept.  DEST/MANIFEST.tsv records the CoAR commit, the image and every tool's version,
    # the configuration and every program's outcome and hashes, and every output is compared with the sha256 pinned
    # in script/fetch/termcomp-t2.pinned (a difference fails the fetch and is listed).  Not a .manifest: the outputs
    # are a function of the image, which is built, not pinned.  Needs Docker and an 8 GB image, so it is not in
    # `materialised`.
    DEST="benchmarks/LTS/term-comp_llvm2lts"
    SUB="benchmarks/term-comp"
    KIND=generate
    GEN=script/gen_termcomp_t2.sh
    NOTE="termCOMP's C programs as T2, generated by CoAR's Athena route in a Docker image built from this checkout"
    ;;
  adtrem)
    # The journal version of the same suite (J. Log. Comput. 32(2), 2022): 251 problems, 168 valid
    # properties and 83 invalid ones (the file names starting unsat- or dunsat-), in the same four
    # forms.  It revises 36 of the 169 earlier CHC-source problems and drops one (leon/heap-goal11),
    # so it is a different corpus rather than an update, and it is fetched beside the old one.
    # Its CHC-source half is also the CHC-COMP benchmark set github.com/chc-comp/ADTRem, which is
    # the submodule benchmarks/CHC/ADTRem: the same 251 files with every '-' removed from the
    # identifiers (an injective renaming in each file), which is what the sweeps read.  The archive
    # carries macOS AppleDouble files (._*) and .DS_Store beside the problems.
    DEST="benchmarks/CHC/ADTs/ADTRem-JLC-benchmarks"
    URL="https://fmlab.unich.it/adtrem/ADTRem-JLC-benchmarks.tgz"
    SHA256=15483fc9d4bc8c46b06e858bd995f0210a500a7a30734c08a38df1a631ab1e9d
    KIND=tgz
    NOTE="ADTRem supplementary material (journal version, 251 problems)"
    ;;
  sprouta)
    # Sprout(A) (PLDI 2026 artifact): the protocols and the evaluation scripts, which exist only inside
    # the artifact's Docker image, a 2.7 GB tar in the record.  The image is read as a stream and never
    # stored: script/fetch/docker_stream_extract.py keeps the image's /home/opam/sprout/examples/ and the
    # top-level files of /home/opam/sprout/query-generator/ (the scripts and table templates), applying
    # the layers in the image's order, and checks the md5 Zenodo publishes for the tar.  The generator's
    # sources are the record's source.zip (script/gen_sprouta_hes.sh --build).  Not in `materialised`
    # because of the download's size.  Set SPROUTA_LISTING=FILE to also write the image's file list.
    DEST="benchmarks/sprouta"
    URL="https://zenodo.org/api/records/19600644/files/sprout-a.tar/content"
    MD5=ee1cae85c16b587d05556dd6267cfa85
    SIZE=2721127936
    DSPREFIX=home/opam/sprout/
    DSTAKE="examples/ query-generator/[^/]+\$"
    KIND=docker_stream
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="Sprout(A) protocols from the PLDI'26 artifact's Docker image, Zenodo record 19600644, streamed"
    ;;
  hyhorn)
    # HyHorn (Itzhaky, Shoham, Vizel, ESOP 2024) and its benchmark suite, which exist only inside the artifact's
    # Docker image, a gzip-compressed `docker save` of 251 MB in Zenodo record 10449234 (CC-BY-4.0).  Streamed like
    # sprouta: the image's /hyhorn/ is kept without lib/pdsc/ (the bundled Pdsc checkout with its .git and a
    # thesis PDF), i.e. the specifications (benchmarks/*.py and the Pdsc comparator CHC files benchmarks/pdsc/),
    # HyHorn's own sources and its library.  Nothing is run: script/hyhorn_to_pcsp.py reads the specifications
    # as Python syntax trees and writes CoAR pCSP files (default benchmarks/hyhorn-pcsp/).
    DEST="benchmarks/hyhorn"
    URL="https://zenodo.org/api/records/10449234/files/hyhorn-docker-x64.tgz/content"
    MD5=c6b87b7c9bd77f7816be640b4d9eefbe
    SIZE=251131358
    DSPREFIX=hyhorn/
    DSTAKE="benchmarks/ hyhorn/ lib/[^/]+\$ [^/]+\$"
    DSGZIP=1
    KIND=docker_stream
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="HyHorn's sources and suite from the ESOP'24 artifact's Docker image, Zenodo record 10449234, streamed"
    ;;
  sc2016-gbd)
    # 180 CNF instances of SAT Competition 2016 (crafted track: Heule's Schur colourings, Elffers's
    # relativized pigeonhole rphp4/rphp5, fixedbandwidth; random track: fla- planted 3-SAT and unif-k5),
    # the copy of benchmarks/SAT/small that the Global Benchmark Database (benchmark-database.de) holds.
    # The competition's own archives (crafted16.zip, RandomSat.zip) are no longer served, so each file is
    # fetched by its GBD instance hash -- the md5 of its clause tokens, comments and the p line left out --
    # which names the content, not a download.  GBD serves the clauses without the comment lines;
    # the patch puts back the generators' comment headers and a trailing blank line, so every file is
    # byte-identical to the copy this repository tracked (the manifest's sha256).
    DEST="benchmarks/SAT/sc2016"
    URL="https://benchmark-database.de/file/%s?context=cnf"
    KIND=gbd_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    PATCH="$MANIFESTS/$1.patch"
    NOTE="SAT Competition 2016 crafted/random CNFs, from the Global Benchmark Database by hash, patched"
    ;;
  horsat-exp)
    # The benchmark suite of Broadbent and Kobayashi, Saturation-Based Model Checking of Higher-Order
    # Recursion Schemes, CSL 2013 (TRecS/HorSat format; from TRecS's and TravMC's examples), as the
    # HorSat page serves it.  The archive's selected/ is placed at the destination.
    DEST="benchmarks/HORS/koba"
    URL="https://www-kb.is.s.u-tokyo.ac.jp/~koba/horsat/exp.zip"
    SHA256=cf2476765a9e5c8bc0a5b41f88d0e3631135070eb6f102f4bb1a79a6336fee61
    KIND=zip_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="HorSat (CSL 2013) benchmark suite, exp.zip of Kobayashi's HorSat page"
    ;;
  horsat2-benchmark)
    # The second HorSat2 example archive (from-aplas2014/ and new/), as the HorSat2 page serves it.
    DEST="benchmarks/HORS/koba2"
    URL="https://www-kb.is.s.u-tokyo.ac.jp/~koba/horsat2/benchmark.zip"
    SHA256=b0f8772b1bf272d89596c152e1083623ce2ea0acc293db066fea5880fca0e277
    KIND=zip_manifest
    MANIFEST="$MANIFESTS/$1.manifest"
    NOTE="HorSat2 examples, benchmark.zip of Kobayashi's HorSat2 page"
    ;;
  dqbf-sic)
    # The DQBF benchmarks collected for Sic's DQBDD (jurajsic/DQBFbenchmarks): benchmarks/ holds the
    # original DQDIMACS instances, their HQSpre-preprocessed versions and a test set.  The repository states
    # no licence, so it is fetched and never shipped.  A git source is pinned by its commit, which also
    # pins the content; the clone is kept, so --verify checks the commit and a clean tree.
    DEST="benchmarks/QSAT/DQBFbenchmarks"
    URL="https://github.com/jurajsic/DQBFbenchmarks.git"
    COMMIT=67df966f0da4d53753a54c57de58087afb781631
    SPARSE="/benchmarks/ /README.md"
    KIND=git_pinned
    NOTE="DQBF benchmarks (DQDIMACS) of jurajsic/DQBFbenchmarks, benchmarks/ only, pinned commit"
    ;;
  synthetic-qbf)
    # Rabe's generated QBF families (MarkusRabe/synthetic_qbf_formulas: QDIMACS, QAIGER and DIMACS),
    # the whole repository at a pinned commit.
    DEST="benchmarks/QSAT/synthetic_qbf_formulas"
    URL="https://github.com/MarkusRabe/synthetic_qbf_formulas.git"
    COMMIT=1aa5df37ffa58b1bb89b1760ee105ee2142d96d8
    KIND=git_pinned
    NOTE="synthetic QBF formulas of MarkusRabe/synthetic_qbf_formulas, pinned commit"
    ;;
  *) return 1 ;;
  esac
  return 0
}

ALL="$SMTLIB_LOGICS adtrem sprouta hyhorn rethfl-aplas2020 linarb-regen termcomp-t2 sc2016-gbd horsat-exp horsat2-benchmark dqbf-sic synthetic-qbf $MATERIALISED"

usage() {
  echo "usage: $0 [--verify] [name ...]"
  echo "  names: $ALL"
  echo "  smtlib       = $SMTLIB_LOGICS"
  echo "  materialised = $MATERIALISED"
  echo
  printf "  %-16s %-42s %s\n" NAME DESTINATION STATE
  for n in $ALL; do
    entry "$n"
    if [ -d "$DEST" ] && [ -n "$(ls -A "$DEST" 2>/dev/null)" ]; then
      st="present ($(find "$DEST" -type f -o -type l | wc -l) files)"
    else st="absent"; fi
    printf "  %-16s %-42s %s\n" "$n" "$DEST" "$st"
  done
}

need() {
  command -v "$1" >/dev/null 2>&1 && return 0
  echo "  MISSING TOOL: $1 is needed for this corpus" >&2
  return 1
}

# Copies script/fetch/<name>.notes.md, when there is one, to DEST/NOTES.md, unless it is already there
# with the same content.  Assumes entry has been called and DEST exists.
install_notes() {
  local src="$MANIFESTS/$1.notes.md"
  [ -f "$src" ] || return 0
  cmp -s "$src" "$DEST/NOTES.md" && return 0
  cp "$src" "$DEST/NOTES.md" || { echo "   FAILED to install $src" >&2; return 1; }
  echo "   installed $src as $DEST/NOTES.md"
}

# The manifest's lines without comments or blank lines.
manifest_lines() { grep -vE '^\s*(#|$)' "$MANIFEST"; }

# Every destination of the manifest exists and has the recorded sha256 (a link is followed), and
# DEST holds nothing else.
verify_manifest() {
  [ -n "$MANIFEST" ] || { echo "   no manifest for this corpus; nothing to verify"; return 0; }
  need sha256sum || return 1
  local n bad extra
  n=$(manifest_lines | wc -l)
  bad=$(manifest_lines | awk -F'\t' '{print $3 "  " $2}' | sha256sum --quiet -c - 2>&1 | grep -c 'FAILED')
  extra=$(comm -13 <(manifest_lines | cut -f2 | LC_ALL=C sort) \
                   <(find "$DEST" \( -type f -o -type l \) ! -path "$DEST/NOTES.md" | LC_ALL=C sort) | wc -l)
  echo "   verified $((n - bad)) of $n files against $MANIFEST; $extra files not in it"
  [ "$bad" -eq 0 ] && [ "$extra" -eq 0 ]
}

# A git_pinned corpus is a clone: it is at the pinned commit and its checkout is unmodified.
verify_git() {
  local have
  have=$(git -C "$DEST" rev-parse HEAD 2>/dev/null)
  if [ "$have" != "$COMMIT" ]; then
    echo "   $DEST is at ${have:-no commit}, expected $COMMIT"; return 1
  fi
  if [ -n "$(git -C "$DEST" status --porcelain 2>/dev/null)" ]; then
    echo "   $DEST is at $COMMIT but its checkout is modified"; return 1
  fi
  echo "   $DEST is a clean checkout of $COMMIT"
}

# Checks the submodule out when it is not, and refuses one at another commit than the gitlink.
ensure_submodule() {
  if [ ! -e "$SUB/.git" ]; then
    echo "   checking out the submodule $SUB"
    git submodule update --init "$SUB" || { echo "   FAILED to check out $SUB" >&2; return 1; }
  fi
  local want have
  want=$(git ls-files -s -- "$SUB" | awk '{print $2}')
  have=$(git -C "$SUB" rev-parse HEAD 2>/dev/null)
  if [ "$want" != "$have" ]; then
    echo "   $SUB is at $have, the tree pins $want: run git submodule update $SUB" >&2
    return 1
  fi
}

download() {  # $1 = output file; checks SHA256 when the entry pins one; reads only RANGE when it is set
  local ranged=()
  if [ -n "$RANGE" ]; then
    # --max-filesize refuses a server that ignores the range and answers with the whole file.
    tot=$(( ${RANGE#*-} - ${RANGE%-*} + 1 ))
    ranged=(-r "$RANGE" --max-filesize "$tot")
    echo "   downloading $((tot / 1048576)) MB (bytes $RANGE) from $URL"
  else
    tot=$(curl -sSLI "$URL" 2>/dev/null | awk 'tolower($1)=="content-length:"{print $2}' | tr -d '\r' | tail -1)
    [ -n "${tot:-}" ] && echo "   downloading $((tot / 1048576)) MB from $URL" \
                      || echo "   downloading from $URL"
  fi
  if ! curl -sSL --fail --retry 3 --retry-delay 5 --retry-all-errors "${ranged[@]}" -o "$1" "$URL"; then
    echo "   FAILED to download $URL" >&2; return 1
  fi
  if [ -n "$SHA256" ]; then
    got=$(sha256sum "$1" | cut -d' ' -f1)
    if [ "$got" != "$SHA256" ]; then
      echo "   CHECKSUM MISMATCH: $URL has sha256 $got, expected $SHA256" >&2; return 1
    fi
  fi
}

fetch_one() {
  n="$1"
  if ! entry "$n"; then echo "unknown name: $n" >&2; return 1; fi
  echo "== $n  ($NOTE)"
  if [ -d "$DEST" ] && [ -n "$(ls -A "$DEST" 2>/dev/null)" ]; then
    echo "   already present at $DEST -- left alone.  Delete it first to refetch."
    install_notes "$n"
    return
  fi
  case $KIND in
  tar_zst_strip2) need zstd || return 1; need tar || return 1; need curl || return 1 ;;
  tgz) need tar || return 1; need curl || return 1 ;;
  zip_manifest) need unzip || return 1; need curl || return 1 ;;
  tgz_manifest) need tar || return 1; need curl || return 1; need patch || return 1 ;;
  copy_patch) need patch || return 1 ;;
  git_sparse_patch) need git || return 1; [ -z "$PATCH" ] || need patch || return 1 ;;
  docker_stream) need curl || return 1; need python3 || return 1 ;;
  generate) need git || return 1 ;;
  gbd_manifest) need curl || return 1; need xz || return 1; [ -z "$PATCH" ] || need patch || return 1 ;;
  git_pinned) need git || return 1 ;;
  esac
  tmp=$(mktemp -d) || return 1
  trap 'rm -rf "$tmp"' RETURN
  case $KIND in
  tar_zst_strip2)
    download "$tmp/archive" || return 1
    mkdir -p "$DEST" || return 1
    if ! zstd -dc "$tmp/archive" | tar -x -C "$DEST" --strip-components=2; then
      echo "   FAILED to unpack" >&2; return 1
    fi ;;
  tgz)
    download "$tmp/archive" || return 1
    mkdir -p "$DEST" || return 1
    if ! tar -xzf "$tmp/archive" -C "$DEST" --strip-components=1; then
      echo "   FAILED to unpack" >&2; rmdir "$DEST" 2>/dev/null; return 1
    fi ;;
  zip_manifest)
    download "$tmp/archive" || return 1
    mkdir -p "$tmp/x" && unzip -q "$tmp/archive" -d "$tmp/x" || { echo "   FAILED to unpack" >&2; return 1; }
    manifest_lines | while IFS=$'\t' read -r src dst _; do
      mkdir -p "$(dirname "$dst")" && cp "$tmp/x/$src" "$dst" || exit 1
    done || { echo "   FAILED to place the files" >&2; return 1; } ;;
  tgz_manifest)
    download "$tmp/archive" || return 1
    mkdir -p "$tmp/x" && tar -xzf "$tmp/archive" -C "$tmp/x" || { echo "   FAILED to unpack" >&2; return 1; }
    manifest_lines | while IFS=$'\t' read -r src dst _; do
      mkdir -p "$(dirname "$dst")" && cp "$tmp/x/$src" "$dst" || exit 1
    done || { echo "   FAILED to place the files" >&2; return 1; }
    if [ -n "$PATCH" ]; then
      patch -s -d "$DEST" -p1 <"$PATCH" || { echo "   FAILED to apply $PATCH" >&2; return 1; }
    fi ;;
  links)
    ensure_submodule || return 1
    # A relative link, so the checkout can be moved and a worktree reads its own submodule.
    manifest_lines | while IFS=$'\t' read -r src dst _; do
      d=$(dirname "$dst")
      mkdir -p "$d" && ln -s "$(realpath -m --relative-to="$d" "$src")" "$dst" || exit 1
    done || { echo "   FAILED to make the links" >&2; return 1; } ;;
  copy_patch)
    ensure_submodule || return 1
    manifest_lines | while IFS=$'\t' read -r src dst _; do
      mkdir -p "$(dirname "$dst")" && cp "$SUB/$src" "$dst" || exit 1
    done || { echo "   FAILED to copy the files" >&2; return 1; }
    patch -s -d "$DEST" -p1 <"$PATCH" || { echo "   FAILED to apply $PATCH" >&2; return 1; } ;;
  git_sparse_patch)
    # Only the pinned commit and only the listed directories' blobs are transferred.
    echo "   fetching $COMMIT of $URL (the listed directories only)"
    if ! { git init -q "$tmp/r" && git -C "$tmp/r" remote add origin "$URL" &&
           git -C "$tmp/r" -c gc.auto=0 fetch -q --filter=blob:none --depth 1 origin "$COMMIT" &&
           git -C "$tmp/r" sparse-checkout set --no-cone $SPARSE &&
           git -C "$tmp/r" -c gc.auto=0 checkout -q FETCH_HEAD; }; then
      echo "   FAILED to fetch $COMMIT of $URL" >&2; return 1
    fi
    manifest_lines | while IFS=$'\t' read -r src dst _; do
      mkdir -p "$(dirname "$dst")" && cp "$tmp/r/$src" "$dst" || exit 1
    done || { echo "   FAILED to copy the files" >&2; return 1; }
    if [ -n "$PATCH" ]; then
      patch -s -d "$DEST" -p1 <"$PATCH" || { echo "   FAILED to apply $PATCH" >&2; return 1; }
    fi ;;
  docker_stream)
    # pipefail: a failed download must fail the step even though the extractor read what came.
    echo "   streaming $((SIZE / 1048576)) MB from $URL (nothing of it is stored)"
    # The --take patterns are regular expressions: split DSTAKE on blanks without expanding them as globs.
    set -f; takes=(); for t in $DSTAKE; do takes+=(--take "$t"); done; set +f
    if ! ( set -o pipefail
           curl -sSL --fail --retry 3 --retry-delay 5 --retry-all-errors "$URL" |
           python3 -I script/fetch/docker_stream_extract.py --prefix "$DSPREFIX" "${takes[@]}" --out "$DEST" \
             ${DSGZIP:+--gunzip} --md5 "$MD5" --size "$SIZE" ${SPROUTA_LISTING:+--listing "$SPROUTA_LISTING"} ); then
      echo "   FAILED to stream or extract $URL" >&2; rm -rf "$DEST.partial"; return 1
    fi ;;
  generate)
    if [ -n "$SUB" ]; then ensure_submodule || return 1; fi
    "$GEN" "$DEST" || { echo "   FAILED to generate $DEST" >&2; return 1; } ;;
  gbd_manifest)
    # One download per file; URL is a printf pattern taking the GBD hash.  The sha256 check after the
    # patch is what decides; the hash in the URL only selects the file.
    echo "   downloading $(manifest_lines | wc -l) files from $(printf "$URL" '<hash>')"
    manifest_lines | while IFS=$'\t' read -r h dst _; do
      mkdir -p "$(dirname "$dst")" &&
        curl -sSL --fail --retry 3 --retry-delay 5 --retry-all-errors "$(printf "$URL" "$h")" | xz -dc >"$dst" ||
        { echo "   FAILED to fetch $h for $dst" >&2; exit 1; }
    done || return 1
    if [ -n "$PATCH" ]; then
      patch -s -d "$DEST" -p1 <"$PATCH" || { echo "   FAILED to apply $PATCH" >&2; return 1; }
    fi ;;
  git_pinned)
    # The clone stays at DEST (with its .git), so that --verify can compare the commit; SPARSE, when set,
    # limits the checkout to those paths.
    echo "   fetching $COMMIT of $URL${SPARSE:+ (only $SPARSE)}"
    if ! { git init -q "$DEST" && git -C "$DEST" remote add origin "$URL" &&
           git -C "$DEST" -c gc.auto=0 fetch -q --filter=blob:none --depth 1 origin "$COMMIT" &&
           { [ -z "$SPARSE" ] || git -C "$DEST" sparse-checkout set --no-cone $SPARSE; } &&
           git -C "$DEST" -c gc.auto=0 checkout -q FETCH_HEAD; }; then
      echo "   FAILED to fetch $COMMIT of $URL" >&2; return 1
    fi
    echo "   $DEST: $(git -C "$DEST" ls-files | wc -l) files"
    verify_git
    return ;;
  esac
  install_notes "$n" || return 1
  echo "   $DEST: $(find "$DEST" \( -type f -o -type l \) ! -path "$DEST/NOTES.md" | wc -l) files"
  verify_manifest
}

if [ $# -eq 0 ]; then usage; exit 0; fi

mode=fetch
names=""
for a in "$@"; do
  case $a in
  smtlib) names="$names $SMTLIB_LOGICS" ;;
  materialised) names="$names $MATERIALISED" ;;
  all) names="$names $ALL" ;;
  --verify) mode=verify ;;
  -h | --help) usage; exit 0 ;;
  *) names="$names $a" ;;
  esac
done

fail=0
for n in $names; do
  if [ $mode = verify ]; then
    entry "$n" || { echo "unknown name: $n" >&2; fail=1; continue; }
    echo "== $n"
    [ -d "$DEST" ] || { echo "   absent: $DEST"; fail=1; continue; }
    if [ "$KIND" = git_pinned ]; then verify_git || fail=1; else verify_manifest || fail=1; fi
  else
    fetch_one "$n" || fail=1
  fi
done
exit $fail
