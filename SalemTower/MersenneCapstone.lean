/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.MersenneBridge

/-!
# MERSENNE PRIMALITY IS DECIDED BY THE SALEM TOWER
The end-to-end theorem: chaining the tower–Lucas-Lehmer bridge
(`tower_eq_lucasLehmer`, our Dickson doubling tower at atom 4 IS Mathlib's certified
sequence) through Mathlib's own `lucas_lehmer_sufficiency` / `lucas_lehmer_necessity`
gives the full equivalence:
    M_p = 2^p − 1 is prime   ⟺   the Salem tower vanishes mod M_p
                                  (D_{2^(p−2)}(4) ≡ 0 in ZMod (2^p − 1)),  p ≥ 3.
  • `tower_eq_lucasLehmerResidue` — the tower residue IS `LucasLehmer.lucasLehmerResidue`;
  • `mersenne_prime_iff_tower_vanishes` — the capstone equivalence (p = p' + 3 form,
    covering every p ≥ 3);
  • `mersenne_prime_of_tower_vanishes` / `tower_vanishes_of_mersenne_prime` — the
    two directions unbundled for downstream use.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace SalemTower

open Polynomial

/-- **The tower residue is the Lucas–Lehmer residue**: cast into `ZMod (2^(p'+2) − 1)`,
    the tower value `D_{2^p'}(4)` equals `LucasLehmer.lucasLehmerResidue (p'+2)` — the
    quantity whose vanishing decides Mersenne primality. -/
theorem tower_eq_lucasLehmerResidue (p' : ℕ) :
    (((dickson 1 (1 : ℤ) (2 ^ p')).eval 4 : ℤ) : ZMod (2 ^ (p' + 2) - 1))
      = LucasLehmer.lucasLehmerResidue (p' + 2) := by
  have h := SalemTower.tower_eq_lucasLehmer p'
  unfold LucasLehmer.lucasLehmerResidue
  rw [show p' + 2 - 2 = p' by omega, LucasLehmer.sZMod_eq_s, ← h]

/-- **The capstone**: for `p = p' + 3` (every exponent `p ≥ 3`), the Mersenne number
    `M_p` is prime iff the Salem tower vanishes mod `M_p`. -/
theorem mersenne_prime_iff_tower_vanishes (p' : ℕ) :
    (mersenne (p' + 3)).Prime ↔
      (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : ZMod (2 ^ (p' + 3) - 1)) = 0 := by
  have hres := tower_eq_lucasLehmerResidue (p' + 1)
  constructor
  · intro hp
    have ht := lucas_lehmer_necessity (p' + 3) (by omega) hp
    unfold LucasLehmer.LucasLehmerTest at ht
    rw [show p' + 1 + 2 = p' + 3 from rfl] at hres
    rw [hres]
    exact ht
  · intro h
    refine lucas_lehmer_sufficiency (p' + 3) (by omega) ?_
    unfold LucasLehmer.LucasLehmerTest
    rw [show p' + 1 + 2 = p' + 3 from rfl] at hres
    rw [← hres]
    exact h

/-- Sufficiency unbundled: tower vanishing certifies Mersenne primality. -/
theorem mersenne_prime_of_tower_vanishes (p' : ℕ)
    (h : (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : ZMod (2 ^ (p' + 3) - 1)) = 0) :
    (mersenne (p' + 3)).Prime :=
  (mersenne_prime_iff_tower_vanishes p').mpr h

/-- Necessity unbundled: a Mersenne prime forces the tower to vanish. -/
theorem tower_vanishes_of_mersenne_prime (p' : ℕ) (hp : (mersenne (p' + 3)).Prime) :
    (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : ZMod (2 ^ (p' + 3) - 1)) = 0 :=
  (mersenne_prime_iff_tower_vanishes p').mp hp

end SalemTower
