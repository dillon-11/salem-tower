/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.DicksonTraceTest

/-!
# the antiperiod calculus: the generic ring mechanism under
the Lucas–Lehmer test, typed at full generality.
A unit `u` has ANTIPERIOD `n` when `uⁿ = −1`.  Three laws govern it:
  • `dickson_zero_iff_pow_eq_neg_one` — the trace–antiperiod dictionary (iff):
    `D_n(u + u⁻¹) = 0  ↔  u^(2n) = −1`, over ANY commutative ring — the Dickson
    trace vanishing at rung n IS the antiperiod 2n, with no domain hypothesis
    (unit cancellation runs both directions);
  • `factorization_orderOf_of_pow_eq_neg_one` — the 2-adic pin: an antiperiod n
    with −1 ≠ 1 fixes the 2-part of the order exactly, v₂(ord u) = v₂(n) + 1;
  • `pow_orderOf_half_eq_neg_one` — the converse (needs no zero divisors): even
    order 2m forces the antiperiod, `u^m = −1`.
Specializing n = 2^(k+1) (`orderOf_eq_two_pow_of_pow_eq_neg_one`) recovers the
Lucas–Lehmer order mechanism: the certificate is the rung-2^k instance of the
dictionary + pin.  The Nat engine is `Nat.factorization` arithmetic: `d ∣ 2n`
and `d ∤ n` leave exactly one place to disagree, and it is the prime 2, by one.
-/

namespace SalemTower

open Polynomial

/-! ### The Nat engine: divides-double-but-not-single pins the 2-adic place -/

/-- **Divides 2n but not n pins v₂ exactly**: `d ∣ 2n` and `d ∤ n` force
    `v₂(d) = v₂(n) + 1` (and a fortiori agreement at every odd place). -/
theorem Nat.factorization_two_of_dvd_two_mul {d n : ℕ} (hn : n ≠ 0)
    (hd : d ∣ 2 * n) (hnd : ¬ d ∣ n) :
    d.factorization 2 = n.factorization 2 + 1 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : 2 * n = 0 := Nat.eq_zero_of_zero_dvd hd
    omega
  have h2n : (2 * n : ℕ) ≠ 0 := by positivity
  have hle : d.factorization ≤ (2 * n).factorization :=
    (Nat.factorization_le_iff_dvd hd0 h2n).mpr hd
  have hmul : (2 * n).factorization = (2 : ℕ).factorization + n.factorization :=
    Nat.factorization_mul two_ne_zero hn
  have h2fact : (2 : ℕ).factorization = Finsupp.single 2 1 :=
    Nat.Prime.factorization Nat.prime_two
  -- pointwise bound: d.factorization p ≤ n.factorization p + (single 2 1) p
  have hpt : ∀ p : ℕ, d.factorization p ≤ n.factorization p + (Finsupp.single 2 1 : ℕ →₀ ℕ) p := by
    intro p
    have := hle p
    rw [hmul, h2fact] at this
    simpa [Finsupp.add_apply, add_comm] using this
  -- failure of d ∣ n gives a place where d exceeds n; it must be 2, by exactly one
  have hex : ∃ p, ¬ d.factorization p ≤ n.factorization p := by
    by_contra hall
    push Not at hall
    exact hnd ((Nat.factorization_le_iff_dvd hd0 hn).mp (Finsupp.le_def.mpr hall))
  obtain ⟨p, hp⟩ := hex
  have hp2 : p = 2 := by
    by_contra hne
    have h0 : (Finsupp.single 2 1 : ℕ →₀ ℕ) p = 0 := Finsupp.single_eq_of_ne hne
    have hb := hpt p
    rw [h0] at hb
    exact hp (by omega)
  subst hp2
  have hub := hpt 2
  rw [Finsupp.single_eq_same] at hub
  omega

variable {R : Type*} [CommRing R]

/-! ### The trace–antiperiod dictionary -/

/-- **The Dickson trace zero at rung n IS the antiperiod 2n** (iff, any
    commutative ring): `D_n(u + u⁻¹) = 0 ↔ u^(2n) = −1`.  Forward: the trace
    `uⁿ + u⁻ⁿ = 0` multiplied by the unit `uⁿ`; backward: divide it back out. -/
theorem dickson_zero_iff_pow_eq_neg_one (u : Rˣ) (n : ℕ) :
    (dickson 1 (1 : R) n).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) = 0 ↔
      ((u : R)) ^ (2 * n) = -1 := by
  have hD := dickson_eval_unit_add_inv u n
  have hBA : ((u ^ n : Rˣ) : R) * (((u ^ n)⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((u ^ n : Rˣ) : R) = ((u : R)) ^ n := Units.val_pow_eq_pow_val u n
  constructor
  · intro h
    rw [h] at hD
    have ha : ((u ^ n : Rˣ) : R) + (((u ^ n)⁻¹ : Rˣ) : R) = 0 := hD.symm
    have hmul := congrArg (· * ((u ^ n : Rˣ) : R)) ha
    simp only [add_mul, zero_mul] at hmul
    have hinv : (((u ^ n)⁻¹ : Rˣ) : R) * ((u ^ n : Rˣ) : R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hinv] at hmul
    have : ((u : R)) ^ n * ((u : R)) ^ n = -1 := by
      have hneg : (((u ^ n)⁻¹ : Rˣ) : R) = -((u ^ n : Rˣ) : R) :=
        eq_neg_of_add_eq_zero_right ha
      rw [hneg] at hBA
      calc ((u : R)) ^ n * ((u : R)) ^ n
          = ((u ^ n : Rˣ) : R) * ((u ^ n : Rˣ) : R) := by rw [hval]
        _ = -1 := by linear_combination -hBA
    calc ((u : R)) ^ (2 * n) = ((u : R)) ^ (n + n) := by ring_nf
      _ = ((u : R)) ^ n * ((u : R)) ^ n := pow_add _ _ _
      _ = -1 := this
  · intro h
    rw [hD]
    -- (uⁿ + u⁻ⁿ) · uⁿ = u^(2n) + 1 = 0, and uⁿ is a unit
    have hsum : (((u ^ n : Rˣ) : R) + (((u ^ n)⁻¹ : Rˣ) : R)) * ((u ^ n : Rˣ) : R) = 0 := by
      have hinv : (((u ^ n)⁻¹ : Rˣ) : R) * ((u ^ n : Rˣ) : R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hsq : ((u ^ n : Rˣ) : R) * ((u ^ n : Rˣ) : R) = -1 := by
        rw [hval, ← pow_add]
        calc ((u : R)) ^ (n + n) = ((u : R)) ^ (2 * n) := by ring_nf
          _ = -1 := h
      calc (((u ^ n : Rˣ) : R) + (((u ^ n)⁻¹ : Rˣ) : R)) * ((u ^ n : Rˣ) : R)
          = ((u ^ n : Rˣ) : R) * ((u ^ n : Rˣ) : R)
            + (((u ^ n)⁻¹ : Rˣ) : R) * ((u ^ n : Rˣ) : R) := by ring
        _ = -1 + 1 := by rw [hsq, hinv]
        _ = 0 := by ring
    have := congrArg (· * (((u ^ n)⁻¹ : Rˣ) : R)) hsum
    simp only [zero_mul, mul_assoc] at this
    rwa [show ((u ^ n : Rˣ) : R) * (((u ^ n)⁻¹ : Rˣ) : R) = 1 from hBA, mul_one] at this

/-! ### The 2-adic pin -/

/-- Antiperiod n gives `ord(u) ∣ 2n`. -/
theorem orderOf_dvd_two_mul_of_pow_eq_neg_one {u : Rˣ} {n : ℕ}
    (h : ((u : R)) ^ n = -1) : orderOf u ∣ 2 * n := by
  apply orderOf_dvd_of_pow_eq_one
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  calc ((u : R)) ^ (2 * n) = (((u : R)) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    _ = 1 := by rw [h]; ring

/-- Antiperiod n with `−1 ≠ 1` gives `ord(u) ∤ n`. -/
theorem not_orderOf_dvd_of_pow_eq_neg_one {u : Rˣ} {n : ℕ}
    (h : ((u : R)) ^ n = -1) (hne : (-1 : R) ≠ 1) : ¬ orderOf u ∣ n := by
  intro hdvd
  apply hne
  have h1 : u ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have := congrArg (Units.val) h1
  rw [Units.val_pow_eq_pow_val, Units.val_one, h] at this
  exact this

/-- **The 2-adic pin**: an antiperiod n (with `−1 ≠ 1`) fixes the 2-part of the
    order exactly, `v₂(ord u) = v₂(n) + 1`. -/
theorem factorization_orderOf_of_pow_eq_neg_one {u : Rˣ} {n : ℕ} (hn : n ≠ 0)
    (h : ((u : R)) ^ n = -1) (hne : (-1 : R) ≠ 1) :
    (orderOf u).factorization 2 = n.factorization 2 + 1 :=
  Nat.factorization_two_of_dvd_two_mul hn
    (orderOf_dvd_two_mul_of_pow_eq_neg_one h)
    (not_orderOf_dvd_of_pow_eq_neg_one h hne)

/-- The 2-power specialization (the Lucas–Lehmer case): antiperiod `2^(k+1)`
    pins the whole order, `ord(u) = 2^(k+2)`. -/
theorem orderOf_eq_two_pow_of_pow_eq_neg_one {u : Rˣ} {k : ℕ}
    (h : ((u : R)) ^ (2 ^ (k + 1)) = -1) (hne : (-1 : R) ≠ 1) :
    orderOf u = 2 ^ (k + 2) := by
  have hdvd : orderOf u ∣ 2 ^ (k + 2) := by
    have := orderOf_dvd_two_mul_of_pow_eq_neg_one h
    rwa [show 2 * 2 ^ (k + 1) = 2 ^ (k + 2) by ring] at this
  obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hfact := factorization_orderOf_of_pow_eq_neg_one (by positivity) h hne
  rw [hje, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Finsupp.single_eq_same] at hfact
  rw [hje, show j = k + 2 by omega]

/-! ### The converse: even order forces the antiperiod (no zero divisors) -/

/-- **Even order forces the antiperiod**: with no zero divisors, `ord(u) = 2m`
    (`m ≠ 0`) gives `u^m = −1` — the square root of 1 that is not 1. -/
theorem pow_orderOf_half_eq_neg_one [NoZeroDivisors R] {u : Rˣ} {m : ℕ}
    (hm : m ≠ 0) (h : orderOf u = 2 * m) : ((u : R)) ^ m = -1 := by
  have hsq : ((u : R)) ^ m * ((u : R)) ^ m = 1 := by
    rw [← pow_add]
    have h1 : u ^ (m + m) = 1 := by
      rw [show m + m = 2 * m by ring, ← h]
      exact pow_orderOf_eq_one u
    have := congrArg (Units.val) h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exfalso
    have hu1 : u ^ m = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h1
    have := orderOf_dvd_of_pow_eq_one hu1
    rw [h] at this
    have hle : 2 * m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) this
    omega
  · exact h1

end SalemTower
