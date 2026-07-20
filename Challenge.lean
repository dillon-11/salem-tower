/-
  Challenge: the Salem tower — three headline theorems, stated Mathlib-only.

  To a monic integer polynomial `P` attach the tower of 2-power cyclotomic
  resultant values; its arithmetic is governed by Dickson polynomials
  (`Polynomial.dickson 1 1`, the trace coordinates `D_n(u + u⁻¹) = uⁿ + u⁻ⁿ`).

  1. `tower_eq_lucasLehmer`: the Dickson doubling tower evaluated at the atom 4
     (the trace of the fundamental unit 2 + √3) IS Mathlib's certified
     Lucas–Lehmer sequence, term for term.

  2. `mersenne_prime_iff_tower_vanishes`: consequently, for every exponent
     `p = p' + 3 ≥ 3`, the Mersenne number `2^p − 1` is prime iff the tower
     value `D_{2^(p−2)}(4)` vanishes in `ZMod (2^p − 1)`.

  3. `cyclotomic_sq_dvd_iff_orderOf_eq` (the rung-local Wieferich theorem): for
     a prime `q` dividing `Φ_n(a)` with `q ∤ n`, `q ∤ a`, the SQUARE `q²` divides
     `Φ_n(a)` exactly when the multiplicative order of `a` fails to grow from
     `ZMod q` to `ZMod q²` — i.e. squared primes in cyclotomic values are
     precisely order-lift failures (Wieferich phenomena localized to the rung).
-/
import Mathlib

open Polynomial

/-- The Salem/Dickson tower at atom 4 is Mathlib's Lucas–Lehmer sequence. -/
theorem tower_eq_lucasLehmer :
    ∀ k : ℕ, (dickson 1 (1 : ℤ) (2 ^ k)).eval 4 = LucasLehmer.s k := sorry

/-- Mersenne primality is decided by the tower: `2^(p'+3) − 1` is prime iff
    `D_{2^(p'+1)}(4)` vanishes mod it. -/
theorem mersenne_prime_iff_tower_vanishes (p' : ℕ) :
    (mersenne (p' + 3)).Prime ↔
      (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : ZMod (2 ^ (p' + 3) - 1)) = 0 := sorry

/-- The rung-local Wieferich theorem: `q² ∣ Φ_n(a)` iff the order of `a` fails
    to lift from `q` to `q²` (i.e. stays exactly `n`). -/
theorem cyclotomic_sq_dvd_iff_orderOf_eq {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hqa : ¬ q ∣ a)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval (a : ℤ) ↔
      orderOf ((a : ZMod (q ^ 2))) = n := sorry

/-- The trace–antiperiod dictionary: over any commutative ring, the Dickson
    trace zero at rung n is exactly the antiperiod, `D_n(u + u⁻¹) = 0 ↔ u^(2n) = −1`. -/
theorem dickson_zero_iff_pow_eq_neg_one {R : Type*} [CommRing R] (u : Rˣ) (n : ℕ) :
    (dickson 1 (1 : R) n).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) = 0 ↔
      ((u : R)) ^ (2 * n) = -1 := sorry

/-- A Mersenne prime is a rung split of the seed polynomial: `2^(p'+3) − 1` prime
    forces a unit of multiplicative order exactly `2^(p'+3)` in
    `AdjoinRoot (x² − 4x + 1)` over `ZMod (2^(p'+3) − 1)` — the Lucas–Lehmer seed. -/
theorem mersenne_prime_seed_order (p' : ℕ) (hp : (mersenne (p' + 3)).Prime) :
    ∃ u : (AdjoinRoot (C 1 * X ^ 2 + C (-4) * X + C 1 :
        Polynomial (ZMod (2 ^ (p' + 3) - 1))))ˣ,
      orderOf u = 2 ^ (p' + 3) := sorry

/-- The Zsygmondy reduction: if `2^d − 1` has no primitive prime divisor at
    index d, then `|Φ_d(2)|` divides the radical of d. -/
theorem no_primitive_cyclotomic_dvd_rad {d : ℕ} (hd : 1 < d)
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (cyclotomic d ℤ).eval 2 →
      orderOf ((2 : ℕ) : ZMod q) ≠ d) :
    ((cyclotomic d ℤ).eval 2).natAbs ∣ ∏ p ∈ d.primeFactors, p := sorry
