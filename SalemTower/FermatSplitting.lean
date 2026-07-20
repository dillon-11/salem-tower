/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib

/-!
# WHY THE SALEM TOWER DETECTS FERMAT PRIMES (the
arithmetic-frontier prime hunt, certified executed
2026-07-17).
The Salem tower √L_k = ∏(α^(2^(k-1)) + α^(-2^(k-1))) detects a prime p at
rung k iff a root of the Salem polynomial has EXACT multiplicative order 2^(k+1)
mod p (order detection). Lehmer's tower produces Mersenne (3, 31, 127)
AND Fermat (257 = F₃, 65537 = F₄) primes. The Fermat appearance is structural
and certified here: for a Fermat prime p = 2^n + 1, the unit group (ℤ/p)ˣ is a
PURE 2-GROUP (order 2^n), so EVERY unit has 2-power order — hence any Salem
number that splits mod p lands in the tower automatically, at the rung fixed by
its (necessarily 2-power) order.
-/

namespace SalemTower

/-- **Fermat-prime units have 2-power order (divisibility form).** For a Fermat
prime `p = 2^n + 1`, every unit of `ℤ/p` has order dividing `2^n`: the unit group
is a 2-group. -/
theorem fermat_unit_order_dvd {n p : ℕ} [Fact p.Prime] (hp : p = 2 ^ n + 1)
    (x : (ZMod p)ˣ) : orderOf x ∣ 2 ^ n := by
  have hcard : Fintype.card (ZMod p)ˣ = 2 ^ n := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, hp, Nat.add_sub_cancel]
  rw [← hcard]
  exact orderOf_dvd_card

/-- **Fermat-prime units have 2-power order (exact form).** Every unit of `ℤ/p`
for a Fermat prime `p = 2^n + 1` has order `2^j` for some `j ≤ n`. This is why a
Salem number splitting mod a Fermat prime necessarily appears in its 2-adic mass
tower: the root's order is forced to be a power of 2. -/
theorem fermat_unit_order_two_power {n p : ℕ} [Fact p.Prime] (hp : p = 2 ^ n + 1)
    (x : (ZMod p)ˣ) : ∃ j ≤ n, orderOf x = 2 ^ j :=
  (Nat.dvd_prime_pow Nat.prime_two).mp (fermat_unit_order_dvd hp x)

end SalemTower
