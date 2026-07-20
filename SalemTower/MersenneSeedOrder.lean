/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.DicksonTraceTest
import SalemTower.MersenneCapstone
import SalemTower.UnitAntiperiod

/-!
# a Mersenne prime forces a unit of order 2^p.
When `M_p = 2^p − 1` is prime, the trace value 4 = u + u⁻¹ splits in the
quadratic extension `AdjoinRoot (X² − 4X + 1)` over `ZMod M_p`, and the
tower vanishing `D_{2^(p−2)}(4) ≡ 0` says — by the trace–antiperiod
dictionary (`dickson_zero_iff_pow_eq_neg_one`) — exactly that the unit `u`
satisfies `u^(2^(p−1)) = −1`, hence has multiplicative order `2^p`
(`orderOf_eq_two_pow_of_pow_eq_neg_one`). The Lucas–Lehmer test is a
membership certificate for the tower of `x² − 4x + 1` at its top level;
the underlying calculus is `UnitAntiperiod.lean`.
  • `mersenne_prime_seed_order` — `M_(p'+3)` prime forces a unit of order
    exactly `2^(p'+3)` in the seed extension.
-/

namespace SalemTower

open Polynomial

/-- The seed polynomial `x² − 4x + 1` over an arbitrary commutative ring. -/
noncomputable def seedPoly (F : Type*) [CommRing F] : F[X] :=
  C 1 * X ^ 2 + C (-4) * X + C 1

/-- **A Mersenne prime is a rung split of the seed polynomial**: if `2^(p'+3) − 1`
    is prime, the extension `AdjoinRoot (x² − 4x + 1)` over `ZMod (2^(p'+3) − 1)`
    contains a unit of multiplicative order exactly `2^(p'+3)` — the Lucas–Lehmer
    seed, at rung `p' + 2`. -/
theorem mersenne_prime_seed_order (p' : ℕ) (hp : (mersenne (p' + 3)).Prime) :
    ∃ u : (AdjoinRoot (seedPoly (ZMod (2 ^ (p' + 3) - 1))))ˣ,
      orderOf u = 2 ^ (p' + 3) := by
  haveI hMfact : Fact (Nat.Prime (2 ^ (p' + 3) - 1)) := ⟨by
    have : mersenne (p' + 3) = 2 ^ (p' + 3) - 1 := rfl
    rwa [this] at hp⟩
  set F := ZMod (2 ^ (p' + 3) - 1) with hF
  set f : F[X] := seedPoly F with hf
  set R := AdjoinRoot f with hR
  -- the root relation r² − 4r + 1 = 0
  have hroot : (AdjoinRoot.root f) ^ 2 - 4 * (AdjoinRoot.root f) + 1 = 0 := by
    have h0 := AdjoinRoot.eval₂_root f
    simp only [hf, seedPoly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_neg, eval₂_ofNat, eval₂_one, map_one, map_neg, map_ofNat, one_mul] at h0
    linear_combination h0
  set r := AdjoinRoot.root f with hr
  -- the seed unit
  refine ⟨⟨r, 4 - r, by linear_combination -hroot, by linear_combination -hroot⟩, ?_⟩
  set u : Rˣ := ⟨r, 4 - r, by linear_combination -hroot, by linear_combination -hroot⟩ with hu
  have hsum : (u : R) + ((u⁻¹ : Rˣ) : R) = 4 := by
    change r + (4 - r) = 4
    ring
  -- the tower vanishing, transported into R
  have hvanF : (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : F) = 0 :=
    (mersenne_prime_iff_tower_vanishes p').mp hp
  have hvanR : (dickson 1 (1 : R) (2 ^ (p' + 1))).eval (4 : R) = 0 := by
    have hmap : (dickson 1 (1 : R) (2 ^ (p' + 1)))
        = ((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).map (Int.castRingHom R)) := by
      rw [map_dickson]
      norm_num
    have hcast : (dickson 1 (1 : R) (2 ^ (p' + 1))).eval (4 : R)
        = (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : R) := by
      rw [hmap, show (4 : R) = (Int.castRingHom R) (4 : ℤ) by norm_num, eval_map,
        eval₂_at_apply]
      rfl
    rw [hcast,
      show (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : R)
        = algebraMap F R (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : F) by
          rw [map_intCast],
      hvanF, map_zero]
  rw [show (4 : R) = (u : R) + ((u⁻¹ : Rˣ) : R) from hsum.symm] at hvanR
  -- the dictionary: trace zero at rung 2^(p'+1) IS the antiperiod 2^(p'+2)
  have hneg : ((u : R)) ^ (2 ^ (p' + 2)) = -1 := by
    have := (dickson_zero_iff_pow_eq_neg_one u (2 ^ (p' + 1))).mp hvanR
    rwa [show 2 * 2 ^ (p' + 1) = 2 ^ (p' + 2) by ring] at this
  -- −1 ≠ 1 in R: nontriviality + odd characteristic
  have hM7 : 7 ≤ 2 ^ (p' + 3) - 1 := by
    have : (8 : ℕ) ≤ 2 ^ (p' + 3) := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (p' + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI : Nontrivial R := AdjoinRoot.nontrivial f (by
    rw [hf]
    unfold seedPoly
    rw [degree_quadratic (one_ne_zero)]
    norm_num)
  have hne : (-1 : R) ≠ 1 := by
    intro hc
    have h2 : (2 : R) = 0 := by linear_combination -hc
    have hinj : Function.Injective (algebraMap F R) := (algebraMap F R).injective
    have h2F : (2 : F) = 0 := by
      apply hinj
      rw [map_ofNat, map_zero]
      exact_mod_cast h2
    have hdvd : (2 ^ (p' + 3) - 1) ∣ 2 := by
      have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2F
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  -- the 2-adic pin: antiperiod 2^(p'+2) = 2^((p'+1)+1) pins ord = 2^(p'+3)
  have := orderOf_eq_two_pow_of_pow_eq_neg_one (u := u) (k := p' + 1) hneg hne
  simpa [show p' + 1 + 2 = p' + 3 by omega] using this

end SalemTower
