/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.DicksonTraceTest

/-!
# the TERNARY (3-adic) Salem tower: square law and tripling ascent
The first odd-prime tower (preregistered census):
N_k = |Res(P, Φ_{3^(k+1)})| is a perfect square at every rung, with the exact atom law
    (v² + v + 1)·(v⁻² + v⁻¹ + 1) = (D_s(y) + 1)²,    v = uˢ, s = 3^k, y = u + u⁻¹,
so √N_k = ∏_atoms |D_{3^k}(y_j) + 1|, and the tower ascends by the TRIPLING Dickson
map D₃(t) = t³ − 3t: the ×3 side that the 2-adic (doubling) tower could not see.
Census: Lehmer generates 163 (rung 3, split, ≡ 1 mod 81) and 19100773 (rung 4,
≡ 1 mod 243); the massless cyclotomic control collapses to 1 above the lawful
cyclotomic-resultant seed.
  • `ternary_pair_sq` — the pair identity for a unit `u` in any commutative ring:
    `(u² + u + 1)(u⁻² + u⁻¹ + 1) = (u + u⁻¹ + 1)²`;
  • `ternary_rung_sq` — the rung form at `v = uˢ`: the pair product equals
    `(Dₛ(u + u⁻¹) + 1)²` (via `dickson_eval_unit_add_inv`) — the square law of
    every ternary rung, atom by atom;
  • `tripling_ascent` — `D₃` evaluates to `t³ − 3t`: one ternary rung triples the
    rapidity (`2cosh u ↦ 2cosh 3u`); with Mathlib's `dickson_one_one_mul`,
    `D_{3^(k+1)} = D₃ ∘ D_{3^k}` — the tower is the tripling orbit.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace SalemTower

open Polynomial

variable {R : Type*} [CommRing R]

/-- **The ternary pair identity**: for a unit `u`,
    `(u² + u + 1)(u⁻² + u⁻¹ + 1) = (u + u⁻¹ + 1)²` — the ternary cyclotomic pair
    product is the perfect square of the shifted trace atom. -/
theorem ternary_pair_sq (u : Rˣ) :
    (((u : R)) ^ 2 + (u : R) + 1) * ((((u⁻¹ : Rˣ) : R)) ^ 2 + ((u⁻¹ : Rˣ) : R) + 1)
      = ((u : R) + ((u⁻¹ : Rˣ) : R) + 1) ^ 2 := by
  have h : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((u : R) * ((u⁻¹ : Rˣ) : R) + (u : R) + ((u⁻¹ : Rˣ) : R)) * h

/-- **The rung square law**: at the rung unit `v = uˢ` (`s = 3^k`), the ternary pair
    product is `(Dₛ(y) + 1)²` where `y = u + u⁻¹` — `√N_k = ∏ |D_{3^k}(y_j) + 1|`. -/
theorem ternary_rung_sq (u : Rˣ) (s : ℕ) :
    ((((u ^ s : Rˣ) : R)) ^ 2 + ((u ^ s : Rˣ) : R) + 1)
        * (((((u ^ s)⁻¹ : Rˣ) : R)) ^ 2 + (((u ^ s)⁻¹ : Rˣ) : R) + 1)
      = ((dickson 1 (1 : R) s).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) + 1) ^ 2 := by
  rw [ternary_pair_sq (u ^ s), SalemTower.dickson_eval_unit_add_inv]

/-- **Tripling ascent**: `D₃(t) = t³ − 3t` — one ternary rung triples the rapidity. -/
theorem tripling_ascent (t : R) :
    (dickson 1 (1 : R) 3).eval t = t ^ 3 - 3 * t := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, dickson_add_two]
  simp [dickson_one]
  ring

end SalemTower
