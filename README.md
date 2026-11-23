# Riemann Hypothesis · Lean 4 Community Collaboration Hub

> **Live Progress & Proof Techniques Board:** <https://riemann.verifytask.cn/>  
> **Discord Community:** <https://discord.gg/dUeUNEY5pc> · **Updates on X:** <https://x.com/osgood001> · **Upstream:** [`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis) · **How to Contribute:** [`CONTRIBUTING.md`](CONTRIBUTING.md)

This repository is the active community collaboration hub and fork of [`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis) hosting the full Lean 4 Riemann Hypothesis formalization (`149,097` active `v4.36.0` `.lean` files under `src/`), lightweight static PR checks, maintainer-gated Bohrium Sandbox verification, and attributed frontier proof simplifications mirrored from **Agentic Science Playground**.

## Modular Core Pillars (`Core 1–13`) & Grand Challenge (`Main RH`)

> **Coverage Accounting:** Core Pillars `1–13` cover **`1,938` deduplicated `.lean` files (`1.11%` of Alpöge's `175,187`-file archive) / `16,603,617` characters (`1.69%` of `980.4M` chars)** — combining Phase 1 (`Core 1–5`: `712` files / `0.94%`) and Phase 2 (`Core 6–13`: `+1,226` files / `+0.76%`, `0` file overlap). **Phase 3 expansion** targeting the remaining **~98.3%** core engine (`AbelianVarietyTheory`, `AutomorphicArithmetic`, `AutomorphicSpectrum`, `WeilBound`, `LocalToGlobal`, etc.) is actively underway — see [`CONTRIBUTING.md`](CONTRIBUTING.md) to jump straight into uncovered `src/` modules!

| Pillar | Playground Challenge | Target Module Family (`src/`) | GitHub Draft PR | Frontier Snapshot (`0 sorry`, Standard Axioms) |
|---|---|---|---|---|
| **Core 1** | [ζ(s) Zero-Free Region](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) | `Formalism/ZetaNonvanishing` + `LandauZeroFreeBounds` | [PR #2](https://github.com/Osgood001/riemann-hypothesis/pull/2) | `#99218` · `Mikko Nyman` · `68.74` · **-93.7%** tokens (`21→1` files) |
| **Core 2** | [Chebotarev Density (ℚ)](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-2-5-chebotarev-3c22e466) | `ReciprocityTheory/Chebotarev` + `GlobalFields` | [PR #3](https://github.com/Osgood001/riemann-hypothesis/pull/3) | `#99123` · `Pi` · `62.10` · **-77.0%** tokens (`47→1` files) |
| **Core 3** | [Truncated Explicit Formula](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-3-5-truncated-e-9cef4156) | `Formalism/PeriodIntegrals` | [PR #4](https://github.com/Osgood001/riemann-hypothesis/pull/4) | `#99125` · `Pi` · `65.05` · **-86.2%** tokens (`89→1` files) |
| **Core 4** | [Siegel–Walfisz Bound](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-4-5-siegel-walf-dbc36883) | `Formalism/LandauZeroFreeBounds` | [PR #5](https://github.com/Osgood001/riemann-hypothesis/pull/5) | `#99192` · `Pi` · `64.92` · **-85.9%** tokens (`114→1` files) |
| **Core 5** | [Hironaka Resolution (Char 0)](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-5-5-functorial-d282e185) | `Development/ResolutionOfSingularities` | [PR #6](https://github.com/Osgood001/riemann-hypothesis/pull/6) | `#98238` · `Pi` · `54.37` · **-35.6%** tokens (`500→15` files) |
| **Core 6** | [CM j-Invariant Integrality](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-6-cm-j-invarian-70b3d4ba) | `Formalism/LocalToGlobal` + `ReciprocityTheory/ReductiveGroups` | [PR #7](https://github.com/Osgood001/riemann-hypothesis/pull/7) | `#99242` · `Pi` · `59.14` · **-64.3%** tokens (`452→6` files) |
| **Core 7** | [Irreducible Complex Open Connected](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-7-connectedness-ec7f9c89) | `GroundTheory/HeightsAndTheta` + `ReciprocityTheory/ReductiveGroups` | [PR #8](https://github.com/Osgood001/riemann-hypothesis/pull/8) | `#99236` · `Andrew Pullin` · `73.68` · **-98.4%** tokens (`584→1` files) |
| **Core 8** | [Siegel–Weil Local Density](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-8-siegel-weil-u-4d13d2e3) | `Development/AutomorphicSpectrum` + `Development/WeilBound` | [PR #9](https://github.com/Osgood001/riemann-hypothesis/pull/9) | `#99219` · `Pi` · `55.51` · **-43.5%** tokens (`53→1` files) |
| **Core 9** | [Gelfand–Graev Mult. One](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-9-gelfand-graev-509f3aa4) | `Formalism/LocalToGlobal` + `Formalism/PeriodIntegrals` | [PR #10](https://github.com/Osgood001/riemann-hypothesis/pull/10) | `#99253` · `Pi` · `69.36` · **-94.6%** tokens (`45→1` files) |
| **Core 10** | [Jacquet–Langlands Trace Formula](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-10-jacquet-lang-8fa3c55d) | `PositivityTheory/AutomorphicForms` + `GroundTheory/AutomorphicForms` | [PR #11](https://github.com/Osgood001/riemann-hypothesis/pull/11) | `#99249` · `Pi` · `55.13` · **-40.9%** tokens (`60→7` files) |
| **Core 11** | [Bochner–Martin Jacobian ≠ 0](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-11-bochner-mart-0121963b) | `GroundTheory/HeightsAndTheta` | [PR #12](https://github.com/Osgood001/riemann-hypothesis/pull/12) | `#99154` · `Pi` · `60.92` · **-72.4%** tokens (`26→1` files) |
| **Core 12** | [Cyclotomic Power Series Rigidity](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-12-cyclotomic-p-3bfcc9a1) | `Formalism/SharpRestriction` | [PR #13](https://github.com/Osgood001/riemann-hypothesis/pull/13) | `#99275` · `LewyM` · `60.12` · **-68.9%** tokens (`10→1` files) |
| **Core 13** | [Hermitian Curvature Box Bounds](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-13-hermitian-cu-6e1ac05a) | `Formalism/HermitianCurvature` | [PR #14](https://github.com/Osgood001/riemann-hypothesis/pull/14) | `#99274` · `Pi` · `60.55` · **-70.8%** tokens (`6→1` files) |
| **Main RH** | [Full Riemann Hypothesis (Grand Challenge)](https://play.bohrium.com/challenges/lean-4-verification-riemann-hypothesis-levent-alpo-78ee076d) | `src/Main.lean` (Full 175,187-file / 980.4M-char archive) | `main` (`src/`) | `#93193` · `osgood` · `50.00` · Offline Lean `v4.33.1` full build + `#print axioms` clean |

## Two Ways to Contribute

1. **Direct GitHub Pull Requests (`Osgood001/riemann-hypothesis`)** — See [`CONTRIBUTING.md`](CONTRIBUTING.md)
   - Fork this repository, pick any uncovered module in `src/` (including the 98.3%+ remaining core engine) or port a staged `community/core<N>-attempt-<id>/` proof to Lean `v4.36.0`, run `scripts/pr_lightweight_checks.py`, and open a PR against `main`.
   - **Automatic Lightweight CI** (`.github/workflows/pr-lightweight-checks.yml`, ~12s): zero-compilation `0 sorry` / `0 admit` / `0 custom axiom` scan + exact `TOKEN_RE` normalized token delta + toolchain guard.
   - **Maintainer-Gated Bohrium Sandbox CI** (`.github/workflows/bohrium-verify.yml`): after code review, maintainers comment `/verify <head_sha>` (or run `workflow_dispatch`) to launch an air-gapped, zero-token Bohrium Sandbox via `bohr` CLI (`lake build` + `-DwarningAsError=true` + `#print axioms` + Comparator).
2. **Bohrium Playground CLI (Automated Lean 4 + Comparator Scoring)**
   - Install the CLI (`curl -fsSL https://play.bohrium.com/install.sh | bash`) and submit against any pillar in the table above.
   - Frontier breakthroughs are automatically staged here as attributed Draft PRs (`#2–#14` and future Phase 3 pillars) awaiting explicit author confirmation, licensing clearance, and `v4.36.0` `src/` integration.

---

# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A [Comparator](https://github.com/leanprover/comparator) setup and community build cache for the Lean formalization that
claims a proof of the Riemann Hypothesis, and of GRH for Dirichlet L-functions, announced on
2026-11-20 at <https://alpo.ge/remark.pdf>.

The first commit, `40e56bab`, is the submitted Lean source exactly as published. Merged pull
requests have since made the source smaller, mainly by deleting files the proof does not use and
by shortening proofs. `git diff --stat 40e56bab HEAD -- src` shows every change so far, and the
[notes](verification/NOTES.md#source) have more detail. For the original, check out `40e56bab` or
use [riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original),
which keeps the published source frozen.

This repository also adds Comparator files and cache infrastructure:

| File | What it is |
|---|---|
| [`src/Challenge.lean`](src/Challenge.lean) | the five theorems, stated in a file that imports only Mathlib |
| [`comparator.json`](comparator.json) | the Comparator config |
| [`export-targets.txt`](export-targets.txt) | the declarations to export |
| [`verification/`](verification/NOTES.md) | our notes, and the results once there are some |
| [`scripts/`](scripts/) | public Lake cache configuration and reproducible bootstrap/publishing tools |

## Using the build cache

Fetch and restore Mathlib and this project's compiled modules:

```bash
lake exe cache get
lake build --no-build
```

The cache settings are in `lakefile.toml`; no user configuration is needed. The first command
fetches both caches anonymously and extracts the oleans to `.lake/build`. It prefers a successful
CI build matching the current clean source, configuration, dependency manifest and toolchain;
documentation-only commits can reuse the same cache. Otherwise it tries the original published
cache. The second command checks the default build targets without compiling them. The original
project cache is 4.94 GB and contains portable Lean outputs and generated C. Subsequent ordinary
builds compile changed modules and their dependents.

The community cache includes outputs from **untrusted pull requests and volunteer machines**.
Download integrity checks do not verify proofs. Use an independent fresh build when you need
to trust the result.

The [cache notes](verification/CACHE.md) describe the pinned published archive, the cheaper
bootstrap that reuses its proofs, and how to produce and publish future caches. For independent
verification, follow the clean-build instructions below.

## What is claimed

| Theorem in `Main.lean` | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same, written out |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the same, for primitive characters |

## Checking it

The [Lean and Mathlib verification statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
certifies the Riemann Hypothesis proof from Alpöge's November 20 release. The
[independent verification logs](https://math.mit.edu/~drew/grh/) cover all five theorem statements.

The commands below reproduce the check of that release. For checks on changes to this fork's
Lean `v4.36.0` `main` branch, follow [the contributor workflow](CONTRIBUTING.md#local-setup--workflow).

Set `$CLEAN` to a clean checkout of the [original-release verification setup](https://github.com/leanprover-community/riemann-hypothesis/tree/7cce738ba719a32964ca3822d0994f4c6952c7ae).
Use a separate checkout at `40e56bab026552e089d7afcfeff08d2defb9c005` for the solution, and set
`$SOLUTION` to that checkout. Both checkouts use Lean `v4.33.1`.

```bash
export LEAN_ABORT_ON_PANIC=1   # as Comparator sets it: stop on an internal error, don't continue
export LAKE_ARTIFACT_CACHE=false   # rebuild the submission even if cache-env.sh was sourced earlier
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4   # Mathlib's current cache server

# 1. Export the challenge. Clean clone at $CLEAN, Lean v4.33.1.
cd "$CLEAN"
lake exe mathlib/cache get
lake build Challenge
lake env lean4export Challenge -- $(cat export-targets.txt) > challenge.export

# 2. Build the original solution in a sandbox with no network. Takes hours.
cd "$SOLUTION"
lake exe mathlib/cache get      # before entering the sandbox
lake build Main         # inside the sandbox

# 3. Export the solution. Still inside the sandbox; only solution.export comes out.
lake env lean4export Main -- $(cat "$CLEAN/export-targets.txt") > solution.export

# 4. Copy solution.export out of the sandbox and set SOLUTION_EXPORT to its absolute path.
# Run from an empty directory using Lean v4.36.0.
lake comparator --config "$CLEAN/comparator.json" \
  --challenge-from-export "$CLEAN/challenge.export" --solution-from-export "$SOLUTION_EXPORT"
```

What to know before running it:

- **Exporter.** For both exports, build [lean4export](https://github.com/leanprover/lean4export)
  at tag `v4.33.0` with Lean `v4.33.1` and make the executable available on `PATH`.
- **Challenge first.** Compiling the submission runs its code, so the challenge is exported
  where none of that code has been compiled. The original challenge export's sha256 is
  `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9`.
- **Mathlib cache.** Use `lake exe mathlib/cache get` for steps 1 and 2. The fork's
  `lake exe cache get` can also fetch prebuilt submission modules, bypassing a fresh build.
- **Cost.** Hours on a large machine, about 100 GB of disk, and a lot of memory for step 4.

The [notes](verification/NOTES.md) have the details: where the source came from, the Lean
version and its known kernel fixes, the tools, the sandboxes, the test of these steps, and the
limits of what a passing run shows.

## License

The submission belongs to its author and was published without a license. It is mirrored here
for verification only: unmodified at commit `40e56bab`, and changed since then as the
[notes](verification/NOTES.md#source) describe.
