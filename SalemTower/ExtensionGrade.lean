/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib

/-!
# the r > 1 (extension) Dedekind grade of tower primes
The remainder of the Dedekind grade  after the split case
(`TowerSplitCriterion`, r = 1): a tower prime whose witness root lives in a proper
extension.  If the polynomial has an irreducible factor `g` of degree `m` over `ZMod q`
and a root of `g` has multiplicative order `n` in the extension field
`F_{q^m} = AdjoinRoot g`, then
    n ∣ q^m − 1        (Lagrange in the extension field),   and hence
    ord_n(q) ∣ m       (the grade: r divides the factor degree),
which is the census law verified with zero exceptions across 3 units ×
7 rungs  — for the tower index n = 2^(k+1) it explains the Mersenne
entries of Lehmer's tower (3, 31, 127 at r = 2, 4, …) and, in the ternary tower,
the entries 2 (r = 2 in F₄) and 881 (r = 2, ≡ −1 mod 9).
  • `adjoinRoot_natCard` — `|AdjoinRoot g| = q^deg g` (the extension-field card);
  • `order_dvd_extension_card_sub_one` — a root of order `n` forces `n ∣ q^m − 1`;
  • `extension_grade` — hence `orderOf (q : ZMod n) ∣ m`: the Dedekind grade,
    now theorem at every r.
Axiom-clean, `sorry`-free.
-/

namespace SalemTower

open Polynomial

variable {q : ℕ} [Fact q.Prime]

/-- **Extension-field cardinality**: `|AdjoinRoot g| = q ^ deg g` for `g ≠ 0`
    over `ZMod q`. -/
theorem adjoinRoot_natCard (g : Polynomial (ZMod q)) (hg : g ≠ 0) :
    Nat.card (AdjoinRoot g) = q ^ g.natDegree := by
  haveI : Module.Finite (ZMod q) (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg).basis
  rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  congr 1
  exact finrank_quotient_span_eq_natDegree

/-- **Lagrange in the extension**: an element of `AdjoinRoot g` (`g` irreducible of
    degree `m`) of multiplicative order `n > 0` forces `n ∣ q^m − 1`. -/
theorem order_dvd_extension_card_sub_one (g : Polynomial (ZMod q))
    [Fact (Irreducible g)] (x : AdjoinRoot g) {n : ℕ} (hn : 0 < n)
    (hord : orderOf x = n) : n ∣ q ^ g.natDegree - 1 := by
  have hg : g ≠ 0 := (Fact.out : Irreducible g).ne_zero
  haveI : Module.Finite (ZMod q) (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg).basis
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod q)
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  -- x is a unit: x · x^(n−1) = x^n = 1
  have hpow : x ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hux : IsUnit x := by
    have hmul : x * x ^ (n - 1) = 1 := by
      rw [← pow_succ', show n - 1 + 1 = n by omega]
      exact hpow
    exact isUnit_iff_exists.mpr ⟨x ^ (n - 1), hmul, by rwa [mul_comm] at hmul⟩
  have hcard : Fintype.card (AdjoinRoot g)ˣ = q ^ g.natDegree - 1 := by
    rw [Fintype.card_units]
    congr 1
    rw [← Nat.card_eq_fintype_card, adjoinRoot_natCard g hg]
  have hn_eq : n = orderOf hux.unit := by
    rw [← hord, ← orderOf_units, IsUnit.unit_spec]
  rw [hn_eq, ← hcard]
  exact orderOf_dvd_card

/-- **The extension Dedekind grade**: with additionally `q ∤ n`, the order
    `r = ord_n(q)` of `q` in `(ℤ/n)ˣ` divides the factor degree `m = deg g` —
    the grade law of now theorem at every `r`. -/
theorem extension_grade (g : Polynomial (ZMod q)) [Fact (Irreducible g)]
    (x : AdjoinRoot g) {n : ℕ} (hn : 0 < n) (hord : orderOf x = n)
    [NeZero n] :
    orderOf ((q : ZMod n)) ∣ g.natDegree := by
  have h1 : n ∣ q ^ g.natDegree - 1 :=
    order_dvd_extension_card_sub_one g x hn hord
  have hqp : q.Prime := Fact.out
  have hq1 : 1 ≤ q ^ g.natDegree := Nat.one_le_pow _ _ hqp.pos
  have hmod : q ^ g.natDegree ≡ 1 [MOD n] := ((Nat.modEq_iff_dvd' hq1).mpr h1).symm
  have hcast : ((q : ZMod n)) ^ g.natDegree = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at this
    exact this
  exact orderOf_dvd_of_pow_eq_one hcast

end SalemTower
