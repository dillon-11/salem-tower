/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# the split-case tower appearance criterion, certified
The r = 1 (completely split) half of the Dedekind grade , obtained by
composing two existing certified bricks: Mathlib's `isRoot_cyclotomic_iff` and the
Lagrange step of the master order theorem .  Statement: if a polynomial
polynomial `P` and the cyclotomic `Φ_n` share a root `x` in `ZMod q` (`q` prime,
`q ∤ n`) — the mod-q witness of `q ∣ Res(P, Φ_n)` in the split case — then
    x has multiplicative order exactly n,   and   n ∣ q − 1.
At the tower index `n = 2^(k+1)` this is the appearance criterion of the Salem
tower  in its split case: a completely split tower prime at rung
`k` is `≡ 1 (mod 2^(k+1))` — why Lehmer's tower catches the Fermat primes 257 and
65537 by splitting, while the Mersenne primes 3, 31, 127 enter through extensions
(`r > 1`, census-level pending resultants-over-extensions API).
  • `split_common_root_orderOf` — the shared root has order exactly `n`;
  • `split_common_root_dvd_sub_one` — hence `n ∣ q − 1`;
  • `tower_split_criterion` — the `n = 2^(k+1)` instantiation, with the unit
    hypothesis `P.IsRoot x` carried explicitly (the split witness of the rung).
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace SalemTower

open Polynomial

/-- A common root of the polynomial `P` and `Φ_n` over `ZMod q` (`q` prime, `q ∤ n`)
    has multiplicative order exactly `n`.  The split hypothesis is the
    witness: `x` is a root of `P` reduced mod `q` of exact 2-power order when
    `n` is the tower index. -/
theorem split_common_root_orderOf {q n : ℕ} [Fact q.Prime] (_hn : 0 < n)
    (hqn : ¬ q ∣ n) (P : Polynomial (ZMod q)) (x : ZMod q)
    (_hP : P.IsRoot x) (hc : (cyclotomic n (ZMod q)).IsRoot x) :
    orderOf x = n := by
  haveI : NeZero (n : ZMod q) := ⟨by
    rw [Ne, ← Nat.cast_zero, ZMod.natCast_eq_iff]
    rintro ⟨k, hk⟩
    exact hqn ⟨k, by simpa using hk⟩⟩
  exact ((isRoot_cyclotomic_iff.mp hc).eq_orderOf).symm

/-- Lagrange step: the shared root's order `n` divides `q − 1`. -/
theorem split_common_root_dvd_sub_one {q n : ℕ} [Fact q.Prime] (hn : 0 < n)
    (hqn : ¬ q ∣ n) (P : Polynomial (ZMod q)) (x : ZMod q)
    (hP : P.IsRoot x) (hc : (cyclotomic n (ZMod q)).IsRoot x) :
    n ∣ q - 1 := by
  have hord := split_common_root_orderOf hn hqn P x hP hc
  have hx : x ≠ 0 := by
    intro h0
    have hpow : x ^ n = 1 := by
      have := (split_common_root_orderOf hn hqn P x hP hc) ▸ pow_orderOf_eq_one x
      exact this
    rw [h0, zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  have := ZMod.orderOf_dvd_card_sub_one hx
  rwa [hord] at this

/-- **The split tower criterion** (`n = 2^(k+1)`): a completely split tower prime
    at rung `k` — witnessed by a common root of the polynomial `P` and `Φ_{2^(k+1)}`
    in `ZMod q` — has that root of exact order `2^(k+1)`, and `q ≡ 1 (mod 2^(k+1))`.
    The Fermat-prime entries of Lehmer's tower (257 at rung 7, 65537 at rung 14)
    are instances. -/
theorem tower_split_criterion {q k : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (P : Polynomial (ZMod q)) (x : ZMod q) (hP : P.IsRoot x)
    (hc : (cyclotomic (2 ^ (k + 1)) (ZMod q)).IsRoot x) :
    orderOf x = 2 ^ (k + 1) ∧ 2 ^ (k + 1) ∣ q - 1 := by
  have hq : q.Prime := Fact.out
  have hqn : ¬ q ∣ 2 ^ (k + 1) := by
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  have hn : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
  exact ⟨split_common_root_orderOf hn hqn P x hP hc,
    split_common_root_dvd_sub_one hn hqn P x hP hc⟩

end SalemTower
