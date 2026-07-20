import SalemTower.CyclotomicOrder
import SalemTower.OrderLift

/-!
# squared primes in the tower ARE the rung-local Wieferich locus
The bridge between the two 2026-07-17 arcs: the Salem/Salem tower's appearance
criterion (a prime q divides the rung value iff the base has order exactly n = 2^(k+1)
mod q) and the Wieferich order-lift dichotomy
(ord_{q²}(a) ∈ {ord_q(a), q·ord_q(a)}).  Composed, they say:
    q² ∣ Φ_n(a)   ⟺   the order n fails to lift from q to q²
— the Wieferich condition LOCALIZED TO THE TOWER RUNG.  The multiplicity grading of
the tower values is the depth grading of the Wieferich locus.  Census (Lehmer tower):
√L_k is squarefree for every rung k ≤ 10, and the global Lehmer–Wieferich prime
720847  is not a tower prime — both loci are rare and, so far, disjoint.
  • `proper_rung_not_dvd` — a prime at rung n divides NO proper rung d ∣ n
    (rungs are prime-disjoint down the divisor poset);
  • `sq_dvd_pow_sub_one_iff_sq_dvd_cyclotomic` — the q-adic valuation transfer:
    q² ∣ aⁿ − 1 ⟺ q² ∣ Φ_n(a)  (all other cyclotomic factors are prime to q);
  • `cyclotomic_sq_dvd_iff_orderOf_eq` — **the theorem**: for q ∣ Φ_n(a), q ∤ n,
    q² ∣ Φ_n(a) ⟺ ord_{q²}(a) = n  (the non-lift branch of the dichotomy);
  • `tower_rung_wieferich` — the tower instantiation n = 2^(k+1): a squared prime
    in the rung value is exactly a rung-local Wieferich prime.
Axiom-clean, `sorry`-free.
-/

namespace SalemTower

open Polynomial

/-- `(a : ZMod m)^n = 1` reads as the integer divisibility `m ∣ aⁿ − 1`. -/
lemma zmod_pow_eq_one_iff {m a n : ℕ} [NeZero m] :
    ((a : ZMod m)) ^ n = 1 ↔ ((m : ℤ)) ∣ (a : ℤ) ^ n - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]

/-- **Rung disjointness**: a prime `q` at rung `n` (i.e. `q ∣ Φ_n(a)`, `q ∤ n`)
    divides no proper rung: for `d` a proper divisor of `n`, `q ∤ Φ_d(a)`.
    (Otherwise the master order theorem would force `ord_q(a) = d < n = ord_q(a)`.) -/
theorem proper_rung_not_dvd {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    ∀ d ∈ n.properDivisors, ¬ (q : ℤ) ∣ (cyclotomic d ℤ).eval (a : ℤ) := by
  intro d hd hcon
  obtain ⟨hdn, hlt⟩ := Nat.mem_properDivisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hqd : ¬ q ∣ d := fun h => hqn (h.trans hdn)
  have h1 := SalemTower.cyclotomic_primeFactor_orderOf hn hq hqn hdvd
  have h2 := SalemTower.cyclotomic_primeFactor_orderOf hd0 hq hqd hcon
  omega

/-- **Valuation transfer at the rung**: for `q ∣ Φ_n(a)` with `q ∤ n`,
    `q² ∣ aⁿ − 1 ⟺ q² ∣ Φ_n(a)` — the whole `q`-depth of `aⁿ − 1` sits in the
    primitive cyclotomic factor. -/
theorem sq_dvd_pow_sub_one_iff_sq_dvd_cyclotomic {n a q : ℕ} (hn : 0 < n)
    (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    (q : ℤ) ^ 2 ∣ (a : ℤ) ^ n - 1 ↔ (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval (a : ℤ) := by
  -- aⁿ − 1 = Φ_n(a) * (product over proper divisors)
  have hprod : (a : ℤ) ^ n - 1 =
      (cyclotomic n ℤ).eval (a : ℤ) *
        ∏ d ∈ n.properDivisors, (cyclotomic d ℤ).eval (a : ℤ) := by
    have h := congrArg (Polynomial.eval (a : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
    rw [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at h
    rw [← h, ← Nat.cons_self_properDivisors hn.ne', Finset.prod_cons]
  -- q divides no proper-rung factor, hence not their product
  have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnotR : ¬ (q : ℤ) ∣ ∏ d ∈ n.properDivisors, (cyclotomic d ℤ).eval (a : ℤ) := by
    intro h
    obtain ⟨d, hd, hcon⟩ := hqprime.exists_mem_finset_dvd h
    exact proper_rung_not_dvd hn hq hqn hdvd d hd hcon
  have hcop : IsCoprime ((q : ℤ) ^ 2)
      (∏ d ∈ n.properDivisors, (cyclotomic d ℤ).eval (a : ℤ)) :=
    ((hqprime.coprime_iff_not_dvd).mpr hnotR).pow_left
  constructor
  · intro h
    rw [hprod] at h
    exact hcop.dvd_of_dvd_mul_right h
  · intro h
    rw [hprod]
    exact h.mul_right _

/-- **The rung-local Wieferich theorem**: let `q` be a prime at rung `n`
    (`q ∣ Φ_n(a)`, `q ∤ n`, `q ∤ a`).  Then

        `q² ∣ Φ_n(a)  ⟺  ord_{q²}(a) = n`

    — the squared primes of the rung value are exactly the primes where the order
    `n` FAILS TO LIFT from `q` to `q²`: the Wieferich condition localized to the
    rung.  The multiplicity grading of tower values IS the depth grading of the
    unit's Wieferich locus. -/
theorem cyclotomic_sq_dvd_iff_orderOf_eq {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hqa : ¬ q ∣ a)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval (a : ℤ) ↔
      orderOf ((a : ZMod (q ^ 2))) = n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have hordq : orderOf ((a : ZMod q)) = n :=
    SalemTower.cyclotomic_primeFactor_orderOf hn hq hqn hdvd
  have hdvd_int : ((q ^ 2 : ℕ) : ℤ) = (q : ℤ) ^ 2 := by push_cast; ring
  constructor
  · intro hsq
    -- q² ∣ Φ_n(a) ⟹ q² ∣ aⁿ − 1 ⟹ ord_{q²}(a) ∣ n; dichotomy kills the q·n branch
    have hpow : ((a : ZMod (q ^ 2))) ^ n = 1 := by
      rw [zmod_pow_eq_one_iff, hdvd_int]
      exact (sq_dvd_pow_sub_one_iff_sq_dvd_cyclotomic hn hq hqn hdvd).mpr hsq
    have hDn : orderOf ((a : ZMod (q ^ 2))) ∣ n := orderOf_dvd_of_pow_eq_one hpow
    rcases SalemTower.orderOf_lift_dichotomy hq hqa with h | h
    · rw [h, hordq]
    · exfalso
      rw [h, hordq] at hDn
      have : q * n ≤ n := Nat.le_of_dvd hn hDn
      nlinarith [hq.two_le]
  · intro hord
    -- ord_{q²}(a) = n ⟹ q² ∣ aⁿ − 1 ⟹ q² ∣ Φ_n(a)
    have hpow : ((a : ZMod (q ^ 2))) ^ n = 1 := by
      rw [← hord]; exact pow_orderOf_eq_one _
    rw [zmod_pow_eq_one_iff, hdvd_int] at hpow
    exact (sq_dvd_pow_sub_one_iff_sq_dvd_cyclotomic hn hq hqn hdvd).mp hpow

/-- **The tower instantiation** (`n = 2^(k+1)`, the rung index of the mass/Salem
    tower `√L_k`): an odd prime at rung `k` appears SQUARED iff its order
    `2^(k+1)` fails to lift to `q²` — a rung-local Wieferich prime.  For Lehmer's
    tower the accompanying census finds no squared prime through `k = 10` (√L_k squarefree),
    matching the expected ~1/q rarity of the non-lift branch. -/
theorem tower_rung_wieferich {k a q : ℕ} (hq : q.Prime) (hodd : q ≠ 2)
    (hqa : ¬ q ∣ a)
    (hdvd : (q : ℤ) ∣ (cyclotomic (2 ^ (k + 1)) ℤ).eval (a : ℤ)) :
    (q : ℤ) ^ 2 ∣ (cyclotomic (2 ^ (k + 1)) ℤ).eval (a : ℤ) ↔
      orderOf ((a : ZMod (q ^ 2))) = 2 ^ (k + 1) := by
  have hqn : ¬ q ∣ 2 ^ (k + 1) := by
    intro h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  exact cyclotomic_sq_dvd_iff_orderOf_eq (Nat.two_pow_pos _) hq hqn hqa hdvd

end SalemTower
