# Reproduction directory: the four-speed spectrum theorem in Lean 4

All paths below are relative to this directory (`repro/`); the Lean project is `../lean`.
"Observed" means: run on the author's machine (macOS, 24 GB, 10 cores) on 17 November 2026 and the output read.

## 1. What is claimed

`LRSpectrumFull.L4S5.four_speed_spectrum` (module `LRSpectrumFull/L4S5/FourSpeed.lean`): for `v : Fin 4 -> Int` with all entries positive, `v` injective and `ML v < 1/4`,
there is an integer `j >= 2`, `j != 3`, with `ML v = j/(4j+2)`. Also `four_speed_attained` (every such `j` occurs on four distinct positive speeds) and `four_speed_spectrum_iff`.
`ML v = sSup_t min_i dist(v_i t, Z)` (`MaxLoneliness.lean`, `NearestInteger.lean`; read these two files, 218 lines, before trusting the English).
Not claimed: repeated, zero, negative or non-integer speeds, other numbers of speeds, shifted versions, values `>= 1/4`, any first proof (the theorem is due to Yi, Gill and Bu, arXiv:2610.40694; this is a formalization).

## 2. Trust base

* Lean kernel 4.30.0 (`leanprover/lean4:v4.30.0`) and Mathlib at revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` (`../lean/lakefile.toml`: `rev = "v4.30.0"`); the other pins (Batteries, Aesop, Qq, plausible, importGraph, LeanSearchClient, ProofWidgets, Cli) are in `../lean/lake-manifest.json`. Mathlib is not rebuilt by this recipe; its oleans come from the Mathlib cache.
* Axioms (observed, output in `expected_output/`): `check_axioms.sh` prints `#print axioms` for 24 theorems, all exactly `propext, Classical.choice, Quot.sound`, and two planted-`sorry` controls that print `sorryAx` (direct and transitive).
  A scan of the code of the 103 sources (comments stripped; `tools/source_scan.sh`) finds no `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque`, `Classical.choose`, `ofReduceBool`, `skipKernelTC`, `autoImplicit`;
  `set_option` is used for three linter switches and one `maxHeartbeats 1600000`; `decide +kernel` is used 867 times (kernel evaluation, no `ofReduceBool`).
* The Rust generators are an untrusted oracle: the kernel re-checks every generated data blob against Lean definitions whose soundness is proved in Lean (`node_sound`, `linesChunk_sound`, `leafLinesB_sound`). A wrong generator can only make the build fail.
* Statements to read: the three headline theorems, plus `ML`, `gap`, `nearestIntDist`. `check_axioms.lean` prints them with `#check` and `#print`.

## 3. Dependency closure beyond Mathlib (`deps_report.sh`, output in `expected_output/deps_report.txt`)

40,242 constants are reachable from the headline proofs: Mathlib 30,418, Lean core `Init` 6,725, Batteries 177, Aesop 1, Std 1, project 2,920.
The import closure of `LRSpectrumFull.L4S5.FourSpeed` has 103 project modules (`MANIFEST.tsv`): 93 written for the four-speed line (kinds `hand` 50, `generated` 43) and 10 older modules (kind `base`).
The declarations actually reached in the ten base modules: `NearestInteger` (`nearestIntDist` and 7 lemmas), `MaxLoneliness` (`ML`, `gap` and 7 lemmas; the definition of the quantity), `DValue` (`gap_le_ML`),
`ObsCrystallographic` (`nd_exists_nearest`, `nd_le_add`), `ObsRootTorus` (imported; no declaration reached), `L5S3/Babai` (nearest-plane rounding), `L5S3/LayerStep` (the geometric-sum constants),
`L5S4/Compl`, `L5S4/Bordered`, `L5S4/IntForm` (Gram-matrix and bordered-determinant lemmas). Modules `L5S3`, `L5S4`, `ObsRootTorus` and `ObsCrystallographic` belong to other lines of the same author (five-speed and root-torus work) and are included only because the closure needs them.

## 4. Requirements

* `elan` with `leanprover/lean4:v4.30.0` (file `../lean/lean-toolchain`); Lake 5.0.0. The Mathlib cache for the pinned revision (`lake exe cache get` in `../lean`; needs network; not done by these scripts).
* Rust (cargo 1.96.0 used; std only, no crates) for `regen_data.sh` only.
* Machine: observed peak of one `lean` process on the heavy line modules 8.9 GB (max sample 8,901 MB). Build time about 2.4 hours (sum of module times 8,598 s). One `lean` process at a time. Disk: tens of MB for the 103 modules' build products, keep 3 GB free.
* 16 GB machines: the line modules `L4S5.LinesN1C0`, `LinesN1C1p*`, `LinesN4C*` (and `NodeS1`, `NodeS4`) peak at 6 to 9 GB each. They fit only if that `lean` process is the only large process: set `GATE_LIMIT_MB=16000 GATE_RESERVE_MB=9500`, close other applications, and expect a possible out-of-memory kill; the modules are split into parts of at most about 55 range theorems so that one kill costs at most about 12 minutes, and `build.sh` retries. Below 12 GB do not try.

## 5. Contents

| file | purpose |
|---|---|
| `MANIFEST.tsv` | 103 modules, topological build order, path, sha256, bytes, lines, kind, project imports. Regenerate with `tools/make_manifest.sh` (reads sources only) |
| `EXPECTED.tsv` | observed wall time and peak memory per module from clean rebuilds (NA where no observation) |
| `build.sh` | build one module at a time; modes `--plan`, `--status`, `--run` (section 6) |
| `check_axioms.lean`, `check_axioms.sh` | print the axioms and judge the printout; builds nothing (section 7) |
| `deps_report.lean`, `deps_report.sh` | the dependency listing of section 3; builds nothing |
| `regen_data.sh`, `generators/`, `reference/`, `tools/split_lines.sh` | regenerate the Rust-generated Lean data and compare bytes (section 8) |
| `tools/` | `make_manifest.sh`, `source_scan.sh` (+ `strip.awk`), `selftest.sh` and `fake_wrapper.sh` (negative controls for `build.sh`), `dryrun.sh`, `wait_file.sh` |
| `expected_output/` | recorded output of `check_axioms.sh` and `deps_report.sh` on the author's machine |

## 6. Building

```
bash build.sh --plan                 # validate: sources present, sha256 = MANIFEST, order topological, toolchain/Mathlib pins, disk; no lake
bash build.sh --status               # plan, then `lake build --no-build` per module: UP-TO-DATE / NEEDS-BUILD
bash build.sh --run                  # build all 103, one module per `lake build LRSpectrumFull.<M>`, resumable
bash build.sh --run --from 7 --to 25 # a range;  --only L4S5.LinesN2C0,L4S5.LinesN0C0  selected modules;  --force  rebuild even if results say OK
```

Never run a bare `lake build` for this project (one `lean` worker per core, each up to 9 GB). `build.sh` waits for a memory gate (RSS of all `lean` processes + `GATE_RESERVE_MB` <= `GATE_LIMIT_MB`, defaults 6500/14500),
takes an atomic lock directory, refuses to build a module whose project imports are not built, writes one row per module to `logs/build_results.tsv` (so a second `--run` resumes),
retries a guard kill (exit 137 with no other `error:` line) after 600 s up to 6 times, and aborts on a real error. Exit codes: 0 done, 1 error, 2 plan invalid, 3 disk or lock problem.
Optionally set `WRAPPER` to a launcher that is called as `WRAPPER CEILING_MB LOGDIR NAME cmd...`, enforces a memory ceiling, and appends `rss=NNNMB` lines to `LOGDIR/NAME.watch`; with none, the build runs plainly.
Observed on 17 November 2026 on the author's machine: `--plan` valid for all 103 modules (0 missing, 0 hash mismatch, 0 order violations); `tools/selftest.sh` 11 of 11 negative controls pass (corrupted hash, order violation, unknown module, resume, real error aborts, exit-137 retried then gives up, watchdog kill aborts, held lock waits).
The complete 103-module build was done by the author in several clean rebuilds from source (the final layer in one run, the base layers in another, byte-identical build products); `build.sh --run` itself was exercised end to end on a subset only.

## 7. Axioms

`bash check_axioms.sh` (one `lean` process, no build; about 10 s, peak 2.8 GB) prints the statements and the axioms of 24 theorems and 2 controls and judges the printout: the number of printed axiom lines must equal the number of `#print axioms` commands (26),
24 must be exactly the three standard axioms, the two controls must print `sorryAx`, no `error`. Expected last line: `VERDICT: PASS`. The modules must have been built first (section 6).

## 8. Regenerating the certificate data

Chain: `four_wp0 gen cert --var=mid --qmax=50` (15 depth-1 nodes, 5,010 leaf records) -> `four_wp5 cert Data.lean 800` (`L4S5/Data.lean`) -> `emitn Data.lean dir 100` (`NodeS0..14`) and `prof cert profile.tsv` ->
`emit Data.lean profile.tsv dir manifest 8000 30` (17 chunk modules) -> `tools/split_lines.sh` (part sizes N1C1 54, N4C0 55, N4C1 55, N4C2 56).
`bash regen_data.sh` builds the five Rust crates (std only, `--offline`), runs the chain into `work/` and compares with the committed Lean sources and with `reference/` (the stored certificate `cert_final`, the profile, and the unsplit chunk modules),
then deletes `work/`. Observed: 66 of 66 files byte-identical, about 10 s. Not run for the recorded output: `four_wp0 check` (re-derivation of the certificate), the independent `recount` crate (`generators/four_wp0/recount`), `generators/four_wp0/run_plants.sh` (planted-failure controls), `ctlbox` (run it from this directory).
The generators are an untrusted oracle (section 2): this script is for reproducibility, not for trust.

## 9. Known limits

Proof bodies of some modules (`LinesSound`, `L4S3`, `L4S4`, the tail files) were not re-read line by line by a human; the kernel is the arbiter. There is no loop control that corrupts the geometry of the line enumeration (only a control of the time list).
No aggregator module imports the 103 modules (a single module importing all of them is not expected to be buildable on a 24 GB machine); the manifest and `build.sh` are the artefact.
Docstrings and comments of 35 modules were rewritten for publication after the archived build (internal references removed; code unchanged, see the main README); `MANIFEST.tsv` records the hashes of the files in this archive. A few doc comments in `L4S3`, `L4S4` and `L4S5` may still describe hypotheses that were later proved; they do not affect any statement.
