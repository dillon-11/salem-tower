# The Salem tower: a prime-generating sequence attached to each Salem number

To a monic reciprocal integer polynomial `P` (e.g. a Salem polynomial) attach the
**tower**

```
L_k = |Res(P, x^(2^k) + 1)| = |Norm Φ_{2^(k+1)}(α)|,   k = 1, 2, 3, …
```

Every `L_k` is a **perfect square**, and `√L_k` generates a graded sequence of
primes: a prime `q` enters at rung `k` exactly when `P` has a root of
multiplicative order `2^(k+1)` over `F̄_q`. For Lehmer's polynomial
`x¹⁰ + x⁹ − x⁷ − x⁶ − x⁵ − x⁴ − x³ + x + 1` (the smallest known Salem number) the
tower generates the Mersenne primes 3, 31, 127 (through field extensions), the
Fermat primes 257 and 65537 (through splitting), and new large primes —
`√L_9 = 1302851980779781121` is a 19-digit prime.

## What is proven (Lean 4, sorry-free; axiom footprint `propext, Quot.sound, Classical.choice`)

| module | headline |
|---|---|
| `DicksonTower` | the perfect-square law: `√L_k = \|Res(P_tr, D_{2^(k−1)})\|` via Dickson polynomials; the doubling generator `D_{2n} = D_n² − 2` |
| `LucasLehmerTower` | the tower recurrence at atom 4 is the Lucas–Lehmer step |
| `MersenneBridge` | `D_{2^k}(4) = LucasLehmer.s k` — the tower coincides term-by-term with Mathlib's certified Lucas–Lehmer sequence |
| `MersenneCapstone` | `2^p − 1` is prime iff the tower vanishes mod `2^p − 1` (both directions, via Mathlib's Lucas–Lehmer test) |
| `CyclotomicOrder` | the master order theorem: `q ∣ Φ_n(a)`, `q ∤ n` ⟹ `ord_q(a) = n` ⟹ `n ∣ q − 1` |
| `FermatSplitting` | `(ℤ/p)ˣ` is a pure 2-group for a Fermat prime `p = 2^n + 1`: any splitting unit lands in the tower |
| `SplitCriterion` | the split (r = 1) Dedekind grade: a shared root of `P` and `Φ_{2^(k+1)}` mod `q` has order exactly `2^(k+1)`, so `q ≡ 1 (mod 2^(k+1))` |
| `ExtensionGrade` | the extension (r > 1) grade: a root of order `n` in `F_{q^m}` forces `n ∣ q^m − 1`, hence `ord_n(q) ∣ m` |
| `OrderLift` | the order-lift dichotomy `ord_{q²}(a) ∈ {ord_q(a), q·ord_q(a)}` |
| `RungWieferich` | the localized Wieferich theorem: `q² ∣ Φ_n(a) ⟺ ord_{q²}(a) = n` — squared primes in tower values are order-lift failures |
| `DicksonTraceTest` | the Wieferich trace test is a Dickson evaluation on trace atoms (`D_n(u+u⁻¹) = uⁿ + u⁻ⁿ`); the mod-p guard is Frobenius |
| `TernaryTower` | the 3-power tower: rung square law `(v²+v+1)(v⁻²+v⁻¹+1) = (D_s(y)+1)²` and the tripling ascent `D₃(t) = t³ − 3t` |
| `ZsygmondyScaffold` | the primitive/intrinsic dichotomy: every prime factor of `Φ_n(a)` has order exactly `n` or divides `n`; existence reduces to a size bound |
| `UnitAntiperiod` | the antiperiod calculus: the trace–antiperiod dictionary `D_n(u+u⁻¹) = 0 ⟺ u^(2n) = −1` (iff, any commutative ring), the 2-adic pin `v₂(ord u) = v₂(n) + 1`, and the converse (even order forces the antiperiod) |
| `MersenneSeedOrder` | **the seed-order theorem** (v0.1.1): a Mersenne prime `2^p − 1` forces a unit of order exactly `2^p` in `AdjoinRoot(x² − 4x + 1)` — the Lucas–Lehmer test is a tower-membership certificate |
| `ZsygmondyReduction` | **the Zsygmondy reduction** (v0.1.1): intrinsic primes divide `Φ_d(2)` exactly once (elementary LTE), so no primitive divisor ⟹ `\|Φ_d(2)\| ∣ rad(d)`; existence follows from the single inequality `rad(d) < \|Φ_d(2)\|` |

Headline statements, Mathlib-only, in [`Challenge.lean`](Challenge.lean).

## Census facts (exact integer arithmetic; scripts included)

- Lehmer's tower is squarefree through rung 10; 65537 appears at rungs 10, 14
  and 15 (different roots, different 2-power orders).
- Across a 367-polynomial Salem census (degrees 6–10, rungs ≤ 8), every squared
  prime classifies under the rung-local Wieferich theorem: most are horizontal
  (several root pairs at one rung, e.g. 8191², 257²); two are genuine
  **order-lift failures** at q = 7 (the vertical / Wieferich channel).
- The ternary tower of Lehmer's polynomial generates 163 (rung 3) and 19100773
  (rung 4), both ≡ 1 mod 3^(k+1), with the cyclotomic (degenerate-seed)
  control collapsing to 1.

**Not claimed:** no completeness statement about squared primes or
Wieferich-type members beyond the stated censuses is made here; the census
facts above are exact integer computations over the stated ranges (scripts
included), not asymptotic or exhaustive claims. Lehmer's conjecture is
neither claimed nor assumed anywhere.

## Why these constructions are worth extracting

- **The Mersenne capstone** closes a loop: the tower attached to *any* monic
  reciprocal polynomial specializes, at trace atom 4, to Mathlib's certified
  Lucas–Lehmer sequence — so "`2^p − 1` is prime ⟺ the tower vanishes
  mod `2^p − 1`" is proved by identifying the construction with Mathlib's existing
  `LucasLehmer` machinery rather than re-proving the test.
- **The rung-local Wieferich theorem** localizes the Wieferich condition to a
  single cyclotomic value: `q² ∣ Φ_n(a) ⟺ ord_{q²}(a) = n` (for `q ∤ n`).
  Squared primes in tower values stop being anomalies and become order-lift
  failures with an exact criterion, one rung at a time.
- **The Dickson trace descent** halves every computation: the tower lives on
  trace atoms via `√L_k = |Res(P_tr, D_{2^(k−1)})|`, with fast doubling
  `D_{2n} = D_n² − 2` — simultaneously the proof device and the census
  algorithm, and its mod-p correctness guard is literally Frobenius.
- **The split/extension dichotomy** (`SplitCriterion` / `ExtensionGrade`) is
  the Dedekind-grade reading of which primes enter which rung: split primes
  obey `q ≡ 1 (mod 2^(k+1))`, extension primes are graded by `ord_n(q)` —
  the tower acts as a factorization spectrometer for the Salem field.
- **The antiperiod calculus** (v0.1.1) types the mechanism under Lucas–Lehmer
  at full generality: over any commutative ring, the Dickson trace zero at
  rung `n` is *exactly* the antiperiod `u^(2n) = −1` (an iff — unit
  cancellation runs both directions, no domain hypothesis), and an antiperiod
  pins the 2-part of the order on the nose, `v₂(ord u) = v₂(n) + 1`.  The
  Lucas–Lehmer certificate is the rung-`2^k` instance.
- **The Zsygmondy reduction** (v0.1.1) upgrades the scaffold quantitatively:
  an intrinsic prime divides `Φ_d(2)` exactly once (by an elementary
  geometric-sum LTE step, `1 + x + … + x^(q−1) ≡ q (mod q²)`), so the absence
  of a primitive divisor forces `|Φ_d(2)|` to divide the radical of `d`.
  Unconditional Zsygmondy for `2^d − 1` reduces to the one size inequality
  `rad(d) < |Φ_d(2)|`.

## Companion repositories

The towers here instantiate the order-lift framework of
[`wieferich-families`](https://github.com/dillon-11/wieferich-families)
(the paper, its censuses, and its own Lean layer);
[`lehmer-e10`](https://github.com/dillon-11/lehmer-E10) proves the
irreducibility of Lehmer's polynomial and the E₁₀ Coxeter identity that
its Salem census relies on; [`cyclotomic-orders`](https://github.com/dillon-11/cyclotomic-orders)
carries the parity tower and Glaisher-band layer over the same
cyclotomic values. Every
repository builds against Mathlib only — no cross-repo dependencies,
by design: shared lemmas are duplicated or headed to Mathlib.

## Verifying the proofs with comparator

You do not need to read the proof library to check the claims. Inspect
[`Challenge.lean`](Challenge.lean) (the trust surface, Mathlib imports only),
then verify mechanically with
[comparator](https://github.com/leanprover/comparator), which checks that
each of the six theorems named in [`config.json`](config.json) — from
`mersenne_prime_iff_tower_vanishes` and `tower_eq_lucasLehmer` through
`no_primitive_cyclotomic_dvd_rad` — proves *exactly* the statement in
`Challenge.lean`,
uses only the permitted axioms, and is accepted by the Lean kernel:

```bash
# toolchain
elan toolchain install leanprover/lean4:v4.32.0-rc1

# tools (see https://github.com/leanprover/comparator for pinned setup)
git clone https://github.com/leanprover/comparator && (cd comparator && lake build comparator)
git clone https://github.com/leanprover/lean4export && (cd lean4export && lake build)
git clone https://github.com/Zouuup/landrun && (cd landrun && go build -o landrun cmd/landrun/main.go)   # Linux sandbox

# this repository
lake exe cache get   # fetch Mathlib build cache
lake build           # builds Challenge (sorry warnings, intentional) and SalemTower
lake env path/to/comparator/.lake/build/bin/comparator config.json
```

On systems without kernel-level sandbox support, use comparator's development
shim:

```bash
COMPARATOR_LANDRUN=path/to/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=path/to/lean4export/.lake/build/bin/lean4export \
lake env path/to/comparator/.lake/build/bin/comparator config.json
```

Expected output: `Your solution is okay!`

## Reproducing the census facts

`scripts/tower_census.py` recomputes the tower values, squared-prime
classification, and ternary tower in exact integer arithmetic (companion
matrix + Bareiss determinant, no floating point):

```bash
python3 scripts/tower_census.py
```

## Provenance

Three contributors: the human author (direction, judgment, review);
Claude (Anthropic) — reasoning, implementation, Lean formalization; and a
research harness enforcing preregistration, control-first experiments, and
independent re-computation. Trust none of them: every claim is
kernel-checked or re-computable in one command. Machine-readable
metadata: `formalization.yaml`.

## License

Apache-2.0.
