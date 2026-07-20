/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.DicksonTower

/-!
# the Wieferich trace test IS a Dickson evaluation on trace atoms
The bridge from the unit-Wieferich census engine (the trace test
`tr(αᵖ) ≡ tr(α) (mod p²)` run at the degree-10 companion level) to the certified
Dickson tower (DicksonTower): for a reciprocal polynomial, every power trace
is a Dickson evaluation at the trace atoms `y = α + α⁻¹`,
    αⁿ + α⁻ⁿ = D_n(α + α⁻¹),
so the Wieferich trace test lives at the TRACE-polynomial level (degree d/2), not
the companion level (degree d) — the certificate ladder can run in a ring of half
the dimension, with the doubling rung `D_{2n} = D_n² − 2` (DicksonTower.dickson_double)
as the square-and-multiply step.
  • `dickson_eval_unit_add_inv` — the unit form over any commutative ring:
    `D_n(u + u⁻¹) = uⁿ + u⁻ⁿ` for a unit `u` (from Mathlib's
    `dickson_one_one_eval_add_inv`);
  • `dickson_frobenius_guard` — over `ZMod p` the p-th Dickson map is Frobenius,
    `D_p(y) = yᵖ` (Mathlib's `dickson_one_one_zmod_p`, eval form): the census's
    mod-p guard `tr(αᵖ) ≡ tr(α) (mod p)` is the Frobenius identity on atoms;
  • `dickson_eval_double` — the ladder rung at eval level:
    `D_{2n}(y) = D_n(y)² − 2` in any commutative ring (the trace-level
    square-and-multiply of the O(log p) Wieferich certificate).
Verified computationally: the 720847 Lehmer–Wieferich certificate re-runs at the
degree-5 trace level (ZMod p²[y]/(P_tr), Dickson fast-doubling) and reproduces
Σ D_p(y_j) = tr(αᵖ) ≡ −1 (mod p²) — half the matrix dimension of BSDLehmerLadder.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace SalemTower

open Polynomial

variable {R : Type*} [CommRing R]

/-- **The unit trace-atom identity**: for a unit `u` of a commutative ring,
    `D_n(u + u⁻¹) = uⁿ + u⁻ⁿ`.  The power traces of a reciprocal polynomial are
    Dickson evaluations at its trace atoms. -/
theorem dickson_eval_unit_add_inv (u : Rˣ) (n : ℕ) :
    (dickson 1 (1 : R) n).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) =
      ((u ^ n : Rˣ) : R) + (((u ^ n)⁻¹ : Rˣ) : R) := by
  have h := dickson_one_one_eval_add_inv (R := R) (u : R) ((u⁻¹ : Rˣ) : R)
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) n
  simpa [← Units.val_pow_eq_pow_val, ← inv_pow] using h

/-- **The Frobenius guard**: over `ZMod p` (`p` prime) the `p`-th Dickson
    evaluation is the Frobenius, `D_p(y) = yᵖ`.  This is the reason the census
    guard `tr(αᵖ) ≡ tr(α) (mod p)` holds at every prime: on trace atoms it is
    the Frobenius endomorphism. -/
theorem dickson_frobenius_guard (p : ℕ) [Fact p.Prime] (y : ZMod p) :
    (dickson 1 (1 : ZMod p) p).eval y = y ^ p := by
  rw [dickson_one_one_zmod_p, eval_pow, eval_X]

/-- **The trace-level ladder rung**: `D_{2n}(y) = D_n(y)² − 2` in any commutative
    ring — the square-and-multiply step of the Wieferich certificate, run at the
    trace-polynomial level (half the companion dimension).  Eval form of
    `DicksonTower.dickson_double`. -/
theorem dickson_eval_double (n : ℕ) (y : R) :
    (dickson 1 (1 : R) (2 * n)).eval y = ((dickson 1 (1 : R) n).eval y) ^ 2 - 2 := by
  rw [SalemTower.dickson_double]
  simp

end SalemTower
