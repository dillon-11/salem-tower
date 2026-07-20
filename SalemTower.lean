/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.CyclotomicOrder
import SalemTower.OrderLift
import SalemTower.DicksonTower
import SalemTower.LucasLehmerTower
import SalemTower.MersenneBridge
import SalemTower.MersenneCapstone
import SalemTower.FermatSplitting
import SalemTower.RungWieferich
import SalemTower.SplitCriterion
import SalemTower.ExtensionGrade
import SalemTower.DicksonTraceTest
import SalemTower.TernaryTower
import SalemTower.ZsygmondyScaffold
import SalemTower.UnitAntiperiod
import SalemTower.MersenneSeedOrder
import SalemTower.ZsygmondyReduction

/-! Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only. -/

/-! The Challenge statements, re-declared at root level (comparator model). -/

open Polynomial in
/-- The Salem/Dickson tower at atom 4 is Mathlib's Lucas–Lehmer sequence. -/
theorem tower_eq_lucasLehmer :
    ∀ k : ℕ, (dickson 1 (1 : ℤ) (2 ^ k)).eval 4 = LucasLehmer.s k :=
  SalemTower.tower_eq_lucasLehmer

open Polynomial in
/-- Mersenne primality is decided by the tower: `2^(p'+3) − 1` is prime iff
    `D_{2^(p'+1)}(4)` vanishes mod it. -/
theorem mersenne_prime_iff_tower_vanishes (p' : ℕ) :
    (mersenne (p' + 3)).Prime ↔
      (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : ZMod (2 ^ (p' + 3) - 1)) = 0 :=
  SalemTower.mersenne_prime_iff_tower_vanishes p'

open Polynomial in
/-- The rung-local Wieferich theorem: `q² ∣ Φ_n(a)` iff the order of `a` fails
    to lift from `q` to `q²` (i.e. stays exactly `n`). -/
theorem cyclotomic_sq_dvd_iff_orderOf_eq {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hqa : ¬ q ∣ a)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval (a : ℤ) ↔
      orderOf ((a : ZMod (q ^ 2))) = n :=
  SalemTower.cyclotomic_sq_dvd_iff_orderOf_eq hn hq hqn hqa hdvd


open Polynomial in
/-- The trace–antiperiod dictionary: over any commutative ring, the Dickson
    trace zero at rung n is exactly the antiperiod, `D_n(u + u⁻¹) = 0 ↔ u^(2n) = −1`. -/
theorem dickson_zero_iff_pow_eq_neg_one {R : Type*} [CommRing R] (u : Rˣ) (n : ℕ) :
    (dickson 1 (1 : R) n).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) = 0 ↔
      ((u : R)) ^ (2 * n) = -1 :=
  SalemTower.dickson_zero_iff_pow_eq_neg_one u n

open Polynomial in
/-- A Mersenne prime is a rung split of the seed polynomial: `2^(p'+3) − 1` prime
    forces a unit of multiplicative order exactly `2^(p'+3)` in
    `AdjoinRoot (x² − 4x + 1)` over `ZMod (2^(p'+3) − 1)` — the Lucas–Lehmer seed. -/
theorem mersenne_prime_seed_order (p' : ℕ) (hp : (mersenne (p' + 3)).Prime) :
    ∃ u : (AdjoinRoot (C 1 * X ^ 2 + C (-4) * X + C 1 :
        Polynomial (ZMod (2 ^ (p' + 3) - 1))))ˣ,
      orderOf u = 2 ^ (p' + 3) :=
  SalemTower.mersenne_prime_seed_order p' hp

open Polynomial in
/-- The Zsygmondy reduction: if `2^d − 1` has no primitive prime divisor at
    index d, then `|Φ_d(2)|` divides the radical of d. -/
theorem no_primitive_cyclotomic_dvd_rad {d : ℕ} (hd : 1 < d)
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (cyclotomic d ℤ).eval 2 →
      orderOf ((2 : ℕ) : ZMod q) ≠ d) :
    ((cyclotomic d ℤ).eval 2).natAbs ∣ ∏ p ∈ d.primeFactors, p :=
  SalemTower.no_primitive_cyclotomic_dvd_rad hd h

