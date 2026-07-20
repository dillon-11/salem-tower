import SalemTower.LucasLehmerTower

/-!
# THE SALEM TOWER AT ATOM 4 IS MATHLIB'S LUCAS–LEHMER SEQUENCE.
The Salem tower, specialized to the quadratic-unit trace
atom 4 (= (2+√3)+(2+√3)⁻¹), reproduces the Lucas–Lehmer Mersenne test. Here that
is made a Lean identity against Mathlib's own certified Lucas–Lehmer sequence:
  (D_{2^k})(4) = LucasLehmer.s k          for all k,
where `D` is the Dickson polynomial (our tower generator, DicksonTower) and
`LucasLehmer.s` is Mathlib's sequence (s₀ = 4, s_{i+1} = s_i² − 2) whose residue
mod `2^p − 1` decides Mersenne primality (`LucasLehmer.lucasLehmerTest`). So the
Salem tower's doubling backbone and the certified primality test are literally the
same sequence — the new construction lands on existing certified infrastructure.
-/

namespace SalemTower

open Polynomial

/-- **The Salem tower at atom 4 IS Mathlib's Lucas–Lehmer sequence.**
`D_{2^k}(4) = LucasLehmer.s k`. Our Dickson doubling tower (ascent y ↦ y²−2,
DicksonTower.dickson_double) evaluated at the vacuum-adjacent atom 4 coincides,
term for term, with Mathlib's certified Lucas–Lehmer sequence. -/
theorem tower_eq_lucasLehmer :
    ∀ k : ℕ, (dickson 1 (1 : ℤ) (2 ^ k)).eval 4 = LucasLehmer.s k
  | 0 => by
    rw [SalemTower.TowerLL.atom_four_base]
    simp [LucasLehmer.s]
  | (k + 1) => by
    rw [SalemTower.TowerLL.atom_lucas_lehmer_step, tower_eq_lucasLehmer k]
    simp [LucasLehmer.s]

/-- **The tower carries the Lucas–Lehmer recurrence at atom 4, over ℤ.** A
restatement making the s ↦ s²−2 step explicit on the tower side (from
`SalemTower.TowerLL.atom_lucas_lehmer_step`): the sequence `Dₖ := D_{2^k}(4)`
satisfies `D_{k+1} = Dₖ² − 2`, i.e. it is a Lucas–Lehmer sequence, and by
`tower_eq_lucasLehmer` it is *the* one whose 2^p−1 residue tests Mersenne
primality. -/
theorem tower_step_at_four (k : ℕ) :
    (dickson 1 (1 : ℤ) (2 ^ (k + 1))).eval 4
      = ((dickson 1 (1 : ℤ) (2 ^ k)).eval 4) ^ 2 - 2 :=
  SalemTower.TowerLL.atom_lucas_lehmer_step 4 k

/-- **The Salem tower computes the Mersenne primality residue.** Reduced in
`ZMod (2^p − 1)`, our tower value `D_{2^(p-2)}(4)` equals Mathlib's Lucas–Lehmer
term `s (p-2)`. Mathlib's Mersenne-primality decision is the vanishing of exactly
this residue (`LucasLehmer.lucasLehmerResidue`, via `LucasLehmer.s`); hence the
Salem tower, reduced mod the Mersenne number, IS the primality-deciding quantity.
-/
theorem tower_residue (p : ℕ) :
    ((((dickson 1 (1 : ℤ) (2 ^ (p - 2))).eval 4 : ℤ)) : ZMod (2 ^ p - 1))
      = ((LucasLehmer.s (p - 2) : ℤ) : ZMod (2 ^ p - 1)) :=
  congrArg (fun z : ℤ => (z : ZMod (2 ^ p - 1))) (tower_eq_lucasLehmer (p - 2))

end SalemTower
