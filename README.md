# The four-speed lonely runner spectrum below 1/4: a kernel-checked formalization

Repository: https://github.com/ElVec1o/lonely-runner-four-speed
Version 1.0.0 (November 2026). Author: Vico Bonfioli. License: CC-BY-4.0 (`LICENSE.md`).
Paper: `paper/main.pdf` (28 pages; source `paper/main.tex`). Not peer reviewed.

## Abstract

For positive integer speeds `v_1,...,v_n` let `ML(v) = sup_t min_i dist(t v_i, Z)`, where `dist` is the distance to the nearest integer.
Yi, Gill and Bu (arXiv:2610.40694, Theorem 1.2) state that for four distinct positive integer speeds the values of `ML` below `1/4` are exactly
`j/(4j+2)` with `j >= 2`, `j != 3`; Jain and Kravitz (Theorem 1.3) had shown this up to an ineffective finite set, and Fan and Sun (Conjecture 4.1) had conjectured it.
This repository contains a complete formalization of that statement in Lean 4 with Mathlib: the inclusion, the attainment of every value, and the equivalence,
with no `sorry`, no `native_decide`, and no axiom beyond `propext`, `Classical.choice`, `Quot.sound`. The proof uses a computer-generated certificate
(15 depth-one nodes, 5,010 child points, 408,232 line checks, 765 kernel-evaluated theorems) that the Lean kernel checks, an exact analysis of two infinite families
on the critical tori, and one sporadic tuple. **The theorem is not new and no first proof is claimed**; the contribution is the kernel check and the exact tail analysis.
To our knowledge, as of searches made on 17 November 2026, no other formal proof of the statement is known (see the section "Prior art" of the paper for the searches and their limits).

## Idea in words

A primitive vector `v` of four speeds with `ML(v) < 1/4` is encoded by its lattice of integer relations `{x : <x,v> = 0}`, of rank three. A greedily reduced basis of that
lattice (a flag) and covering-radius bounds on each stage turn "infinitely many candidate `v`" into a finite tree of choices for the first two basis vectors. Each leaf is
either a critical torus (a two-dimensional subtorus of `(R/Z)^4` on which the maximum is exactly `1/4`; there are two, classified by Jain and Kravitz), where `ML` is an explicit
function of residues modulo 4, or a finite list of vectors each shown to have `ML >= 1/4` by an explicit rational time, except for one sporadic tuple, `(1,3,4,14)`, whose `ML` is computed exactly (`4/17`).
The tree is finite but too large to check by hand, so the Lean kernel checks it.

## Main results (all in Lean, module `LRSpectrumFull/L4S5/FourSpeed.lean`; label VERIFIED, see "Trust" below)

| paper | Lean declaration (namespace `LRSpectrumFull.L4S5`) | statement |
|---|---|---|
| Theorem 1 | `four_speed_spectrum` | `v : Fin 4 -> Int`, all `v i > 0`, `v` injective, `ML v < 1/4` implies there is an integer `j >= 2`, `j != 3`, with `ML v = j/(4j+2)` |
| Theorem 2 | `four_speed_attained` | for every integer `j >= 2`, `j != 3`, there are four distinct positive integers `v` with `ML v = j/(4j+2)` |
| Corollary 3 | `four_speed_spectrum_iff` | the set of values `< 1/4` of `ML` on four distinct positive integer speeds is `{j/(4j+2) : j >= 2, j != 3}` |
| Proposition 9 | `LRSpectrumFull.L4Tail.ML_1_3_4_14` | `ML(1,3,4,14) = 4/17` |

`ML v := sSup (Set.range (gap v))` with `gap v t := inf'_i nearestIntDist (v i * t)` and `nearestIntDist x := min (Int.fract x) (1 - Int.fract x)`
(`LRSpectrumFull/MaxLoneliness.lean`, `NearestInteger.lean`; 218 lines in all: read these before trusting the English above).
The Lean name of each lemma is given with its statement in the paper (Sections 3 to 5); Appendix A lists the modules.

## What is not claimed

No first proof of the theorem (it is due to Yi, Gill and Bu, arXiv:2610.40694, with a computer-assisted effective proof; this work is a formalization). No statement about repeated, zero, negative or non-integer
speeds, other numbers of speeds, shifted versions, or values `>= 1/4`. No proof of the lonely runner conjecture. The paper has not been peer reviewed, and no human referee has checked the Lean proofs.
No withdrawal or retraction notice applies to this release.

## Trust

* Lean 4.30.0 (`leanprover/lean4:v4.30.0`) and Mathlib at revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` (pinned in `lean/lake-manifest.json`).
* Axioms: `repro/check_axioms.sh` prints `#print axioms` for 24 theorems (the headline ones included) and two planted-`sorry` controls and judges the printout; the expected result is exactly
  `[propext, Classical.choice, Quot.sound]` for the 24 theorems and `sorryAx` for the two controls. The recorded output is in `repro/expected_output/`. A source scan of the 103 modules finds no `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque`, `Classical.choose` or `ofReduceBool` in code (comments stripped); `decide +kernel` is used 867 times.
* The Rust generators are an untrusted oracle: the kernel re-checks every generated data blob against Lean definitions whose soundness is proved in Lean.
* Not guaranteed: that the Lean statement is the mathematical statement the reader has in mind (read the definitions above), and the numbers quoted in the paper about the certificate (they describe the generated data; no theorem depends on them being as printed).

## Reproduction (verify in three commands)

Requirements: `elan` with the toolchain above, the Mathlib cache for the pinned revision (`lake exe cache get`, needs network; not done by the scripts), Rust (std only, no crates) for `regen_data.sh`, 24 GB RAM recommended (one `lean` process peaks at 8.9 GB on the heaviest modules; see `repro/README.md` for 16 GB machines), about 3 GB free disk.
Expected build time about 2.4 hours (sum of module times 8,598 s, observed on the author's machine).

```
cd repro
bash build.sh --plan        # validate sources, hashes, build order, pins; builds nothing
bash build.sh --run         # build the 103 modules one at a time, resumable (about 2.4 h)
bash check_axioms.sh        # after the build: print and judge the axioms; expect VERDICT: PASS
bash regen_data.sh          # optional: regenerate the Rust-generated Lean data and compare byte for byte (about 10 s)
```

Never run a bare `lake build` in `lean/`: it would start one `lean` worker per core, each of which can reach 9 GB (the lakefile has no default target for this reason).
Details, 16 GB settings and the dependency list are in `repro/README.md`.

## File map

| path | content |
|---|---|
| `paper/main.tex`, `paper/main.pdf` | the paper |
| `lean/` | Lake project: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and `LRSpectrumFull/` with the 103 modules of the closure of `L4S5/FourSpeed.lean` (10 older base modules, 50 hand-written, 43 generated). No aggregator module exists; build by module name as `repro/build.sh` does |
| `repro/` | reproduction entry point: `build.sh`, `check_axioms.sh/.lean`, `deps_report.sh/.lean`, `regen_data.sh`, `MANIFEST.tsv` (module order and sha256), `EXPECTED.tsv` (observed time and memory), `generators/` (Rust sources), `reference/` (certificate and profile used by `regen_data.sh`), `tools/`, `expected_output/`, `README.md` |
| `CHECKSUMS.sha256` | sha256 of every file of this repository (except itself) |
| `CITATION.cff`, `.zenodo.json`, `LICENSE.md` | citation and archive metadata, license |

Ten of the 103 modules belong to the author's earlier work and are shared with other lines (nearest-plane rounding, Gram-matrix lemmas, the definition of `ML`); they are included because the closure needs them.
**Docstrings and comments.** In 35 of the 103 Lean modules, docstrings and comments were rewritten for publication (references to internal working notes were removed) after the archived build was made. The code, declarations and proofs are identical to the tree that was built (checked by comparing the sources with comments stripped), so the kernel content is the same; but the sha256 of those 35 files differ from the files that were built, and the doc comments recorded in a build from this archive are the new ones.

## Provenance

The Lean modules, the Rust certificate generators and checkers, and the first draft of the paper were produced by an AI system (Claude, Anthropic); further instances of the same system reviewed them; the questions, the research directions and the decision to formalize this statement came from Vico Bonfioli. The Lean kernel, not a human reader, checks the proofs.

## Prior art and credit

* Yi, Gill and Bu, *Four runners that are barely lonely*, arXiv:2610.40694 (v1, 28 October 2026): the theorem, with an effective computer-assisted proof (C and Python, no proof assistant).
* Jain and Kravitz, *Relative Lonely Runner spectra*, Combinatorial Theory 6 (2026), Paper 1; arXiv:2411.12684, Theorem 1.3 and the classification of the critical tori (Section 3.3).
* Fan and Sun, *Amending the lonely runner spectrum conjecture*, Electron. J. Combin. 33 (2026), P1.38; arXiv:2306.10417, Conjecture 4.1.
* Kravitz, *Barely lonely runners and very lonely runners*, Combinatorial Theory 1 (2021), #P17; arXiv:1912.06034.
* Related Lean work: Chen, `chlciallo/lean4-lonely-runner` (lonely runner conjecture for three to seven runners), doi:10.5281/zenodo.22851977; Oliner, Zenodo record doi:10.5281/zenodo.24232945 (partial Lean results on families `{1,2,3,b}` and `{1,2,3,4s}`; stated in the record to be produced by an AI system, not refereed); Google DeepMind `formal-conjectures` (statement only).
