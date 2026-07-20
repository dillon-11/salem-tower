/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import SalemTower.ZsygmondyScaffold

/-!
# no primitive divisor forces Φ_d(2) ∣ rad(d).
The quantitative upgrade of the Zsygmondy scaffold: not only is every prime
factor of Φ_d(2) primitive or intrinsic (dividing d), but the intrinsic part
is SQUAREFREE — an intrinsic prime divides Φ_d(2) exactly once.  Hence if
2^d − 1 has no primitive prime divisor at index d, the whole cyclotomic value
divides the radical of d:
  • `sub_one_mul_cyclotomic_dvd` — the complementary product law: for a proper
    divisor m of d, (2^m − 1)·Φ_d(2) ∣ 2^d − 1;
  • `geom_sum_sq_modeq` — the elementary LTE step: for odd prime q and
    x ≡ 1 (mod q), the geometric sum 1 + x + … + x^(q−1) ≡ q (mod q²);
  • `intrinsic_sq_not_dvd` — an intrinsic prime (q ∣ d, q ∣ Φ_d(2)) never
    divides Φ_d(2) twice;
  • `no_primitive_cyclotomic_dvd_rad` — THE REDUCTION: no primitive prime at
    index d ⟹ |Φ_d(2)| divides rad(d) = ∏_{q ∣ d prime} q;
  • `exists_primitive_of_rad_lt` — existence from one inequality:
    rad(d) < |Φ_d(2)| forces a primitive prime (a prime q with ord_q(2) = d,
    hence q ≡ 1 mod d).  The remaining input for full Zsygmondy is exactly
    this size bound (the Birkhoff–Vandiver half).
-/

namespace SalemTower

open Polynomial

/-- `2^n − 1` is the product of the cyclotomic values `Φ_f(2)` over `f ∣ n`. -/
theorem two_pow_sub_one_eq_prod_cyclotomic_eval (n : ℕ) (hn : 0 < n) :
    (2 ^ n - 1 : ℤ) = ∏ d ∈ n.divisors, (cyclotomic d ℤ).eval 2 := by
  have h := congrArg (fun q : Polynomial ℤ => q.eval 2)
    (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at h
  exact h.symm

/-- **The complementary product law**: for a proper divisor `m` of `d`,
    `(2^m − 1) · Φ_d(2)` divides `2^d − 1`. -/
theorem sub_one_mul_cyclotomic_dvd {d m : ℕ} (hd : 0 < d) (hm : m ∈ d.properDivisors) :
    ((2 : ℤ) ^ m - 1) * (cyclotomic d ℤ).eval 2 ∣ (2 : ℤ) ^ d - 1 := by
  obtain ⟨hmd, hmlt⟩ := Nat.mem_properDivisors.mp hm
  have hm0 : 0 < m := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hmd, hd.ne'⟩)
  have hsub : m.divisors ⊆ d.divisors := Nat.divisors_subset_of_dvd hd.ne' hmd
  have hprod := two_pow_sub_one_eq_prod_cyclotomic_eval d hd
  have hprodm := two_pow_sub_one_eq_prod_cyclotomic_eval m hm0
  rw [hprod, ← Finset.prod_sdiff hsub, ← hprodm]
  have hdmem : d ∈ d.divisors \ m.divisors := by
    rw [Finset.mem_sdiff]
    refine ⟨Nat.mem_divisors_self d hd.ne', ?_⟩
    intro hc
    have : d ∣ m := (Nat.mem_divisors.mp hc).1
    exact absurd (Nat.le_of_dvd hm0 this) (by omega)
  have hΦdvd : (cyclotomic d ℤ).eval 2 ∣
      ∏ f ∈ d.divisors \ m.divisors, (cyclotomic f ℤ).eval 2 :=
    Finset.dvd_prod_of_mem _ hdmem
  rw [mul_comm ((2 : ℤ) ^ m - 1)]
  exact mul_dvd_mul hΦdvd dvd_rfl

/-- **The elementary LTE step**: for `q` an odd prime and `x ≡ 1 (mod q)`,
    the geometric sum `1 + x + … + x^(q−1)` is `≡ q (mod q²)`. -/
theorem geom_sum_sq_modeq {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : ℤ}
    (h : (q : ℤ) ∣ x - 1) :
    ((q : ℤ)) ^ 2 ∣ (∑ j ∈ Finset.range q, x ^ j) - q := by
  obtain ⟨c, hc⟩ := h
  have hx : x = 1 + q * c := by linarith
  -- per-term expansion: q² ∣ x^j − 1 − j·(q·c)
  have hterm : ∀ j : ℕ, ((q : ℤ)) ^ 2 ∣ x ^ j - 1 - j * ((q : ℤ) * c) := by
    intro j
    induction j with
    | zero => simp
    | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨x * w + n * c * c, ?_⟩
      push_cast
      linear_combination x * hw + (1 + (n : ℤ) * ((q : ℤ) * c)) * hc
  -- the odd half: ∑_{j<q} j = q·t with q = 2t + 1
  obtain ⟨t, ht⟩ := hq.odd_of_ne_two hq2
  have hsum_nat : (∑ j ∈ Finset.range q, j) = q * t := by
    have h2 : (∑ j ∈ Finset.range q, j) * 2 = q * (q - 1) := Finset.sum_range_id_mul_two q
    have hq1 : q - 1 = 2 * t := by omega
    rw [hq1] at h2
    have h3 : q * (2 * t) = q * t * 2 := by ring
    omega
  have hsum_id : (∑ j ∈ Finset.range q, (j : ℤ)) = (q : ℤ) * t := by
    have hcast := congrArg (Nat.cast (R := ℤ)) hsum_nat
    push_cast at hcast
    exact hcast
  -- split the sum
  have hsplit : (∑ j ∈ Finset.range q, x ^ j) - q
      = (∑ j ∈ Finset.range q, (x ^ j - 1 - j * ((q : ℤ) * c)))
        + ((q : ℤ) * c) * (∑ j ∈ Finset.range q, (j : ℤ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib,
      show ((q : ℤ)) = ∑ _j ∈ Finset.range q, (1 : ℤ) by
        simp [Finset.sum_const, Finset.card_range],
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit, hsum_id]
  refine dvd_add (Finset.dvd_sum fun j _ => hterm j) ⟨c * t, by ring⟩

/-- **Intrinsic primes divide `Φ_d(2)` exactly once**: if `q ∣ d` and
    `q ∣ Φ_d(2)`, then `q² ∤ Φ_d(2)`. -/
theorem intrinsic_sq_not_dvd {d q : ℕ} (hd : 1 < d) (hq : q.Prime) (hqd : q ∣ d)
    (hdvd : (q : ℤ) ∣ (cyclotomic d ℤ).eval 2) :
    ¬ ((q : ℤ)) ^ 2 ∣ (cyclotomic d ℤ).eval 2 := by
  intro hsq
  have hd0 : 0 < d := by omega
  -- q is odd: Φ_d(2) divides the odd number 2^d − 1
  have hΦdvd : (cyclotomic d ℤ).eval 2 ∣ (2 : ℤ) ^ d - 1 :=
    cyclotomic_eval_dvd_pow_sub_one hd0 2
  have hq2 : q ≠ 2 := by
    intro h2
    subst h2
    have h2dvd : (2 : ℤ) ∣ (2 : ℤ) ^ d - 1 := dvd_trans hdvd hΦdvd
    have : (2 : ℤ) ∣ (2 : ℤ) ^ d := dvd_pow_self 2 hd0.ne'
    have : (2 : ℤ) ∣ 1 := (dvd_sub_right this).mp h2dvd
    norm_num at this
  -- the proper divisor m = d / q
  obtain ⟨m, hm⟩ := hqd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · subst h0; omega
    · exact h
  have hmlt : m < d := by
    have := hq.two_le
    calc m < q * m := by nlinarith
      _ = d := hm.symm
  have hmmem : m ∈ d.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨⟨q, by rw [hm, Nat.mul_comm]⟩, hmlt⟩
  -- q ∣ 2^m − 1: the order of 2^m mod q divides both q and q − 1
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd_int : (q : ℤ) ∣ (2 : ℤ) ^ d - 1 := dvd_trans hdvd hΦdvd
  have hpow_d : (2 : ZMod q) ^ d = 1 := by
    have h0 : (((2 : ℤ) ^ d - 1 : ℤ) : ZMod q) = 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hqdvd_int
      exact hqdvd_int
    push_cast at h0
    linear_combination h0
  have hym : (2 : ZMod q) ^ m = 1 := by
    set y : ZMod q := (2 : ZMod q) ^ m with hy
    have hyq : y ^ q = 1 := by
      rw [hy, ← pow_mul, mul_comm m q, ← hm]
      exact hpow_d
    have hy0 : y ≠ 0 := by
      rw [hy]
      apply pow_ne_zero
      rw [show (2 : ZMod q) = ((2 : ℕ) : ZMod q) by norm_cast, Ne,
        ZMod.natCast_eq_zero_iff]
      exact fun hdd => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdd)
    have hordq : orderOf y ∣ q := orderOf_dvd_of_pow_eq_one hyq
    have hordq1 : orderOf y ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hy0
    have hord1 : orderOf y = 1 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hordq) with h1 | hqq
      · exact h1
      · exfalso
        rw [hqq] at hordq1
        have hle := Nat.le_of_dvd (by have := hq.two_le; omega) hordq1
        have := hq.two_le
        omega
    exact orderOf_eq_one_iff.mp hord1
  have hq_dvd_xm : (q : ℤ) ∣ (2 : ℤ) ^ m - 1 := by
    have h0 : (((2 : ℤ) ^ m - 1 : ℤ) : ZMod q) = 0 := by
      push_cast
      rw [hym]
      ring
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  -- Φ_d(2) divides the geometric sum
  set x : ℤ := (2 : ℤ) ^ m with hxdef
  have hgeom : (∑ j ∈ Finset.range q, x ^ j) * (x - 1) = (2 : ℤ) ^ d - 1 := by
    rw [geom_sum_mul, hxdef, ← pow_mul, mul_comm m q, ← hm]
  have hx1 : x - 1 ≠ 0 := by
    have : (2 : ℤ) ^ m ≥ 2 := by
      calc (2 : ℤ) ^ m ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hm0
        _ = 2 := by norm_num
    omega
  have hΦ_dvd_sum : (cyclotomic d ℤ).eval 2 ∣ (∑ j ∈ Finset.range q, x ^ j) := by
    have hA := sub_one_mul_cyclotomic_dvd hd0 hmmem
    rw [← hgeom] at hA
    have hA' : ((x - 1) * (cyclotomic d ℤ).eval 2) ∣ ((x - 1) * ∑ j ∈ Finset.range q, x ^ j) := by
      rw [mul_comm (x - 1) (∑ j ∈ Finset.range q, x ^ j)]
      exact hA
    exact (mul_dvd_mul_iff_left hx1).mp hA'
  -- q² divides the sum and the sum ≡ q mod q² ⟹ q² ∣ q, absurd
  have hq2sum : ((q : ℤ)) ^ 2 ∣ (∑ j ∈ Finset.range q, x ^ j) :=
    dvd_trans hsq hΦ_dvd_sum
  have hmodeq := geom_sum_sq_modeq hq hq2 (x := x) (by
    rwa [hxdef])
  have hqq : ((q : ℤ)) ^ 2 ∣ (q : ℤ) := by
    have hd2 := dvd_sub hq2sum hmodeq
    rwa [sub_sub_cancel] at hd2
  have h1 := Int.le_of_dvd (by exact_mod_cast hq.pos) hqq
  have := hq.two_le
  nlinarith

/-- **THE REDUCTION**: if `2^d − 1` has no primitive prime divisor at index `d`
    (no prime `q` with `ord_q(2) = d` dividing `Φ_d(2)`), then `|Φ_d(2)|`
    divides the radical `∏_{q ∣ d prime} q`. -/
theorem no_primitive_cyclotomic_dvd_rad {d : ℕ} (hd : 1 < d)
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (cyclotomic d ℤ).eval 2 →
      orderOf ((2 : ℕ) : ZMod q) ≠ d) :
    ((cyclotomic d ℤ).eval 2).natAbs ∣ ∏ p ∈ d.primeFactors, p := by
  have hd0 : 0 < d := by omega
  set N := ((cyclotomic d ℤ).eval 2).natAbs with hN
  have hΦdvd : (cyclotomic d ℤ).eval 2 ∣ (2 : ℤ) ^ d - 1 :=
    cyclotomic_eval_dvd_pow_sub_one hd0 2
  have hN0 : N ≠ 0 := by
    intro h0
    have : (cyclotomic d ℤ).eval 2 = 0 := Int.natAbs_eq_zero.mp h0
    rw [this] at hΦdvd
    have : (2 : ℤ) ^ d - 1 = 0 := zero_dvd_iff.mp hΦdvd
    have h2d : (2 : ℤ) ^ d ≥ 2 := by
      calc (2 : ℤ) ^ d ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hd0
        _ = 2 := by norm_num
    omega
  -- every prime factor of N divides d, to the first power
  have hpf : ∀ r : ℕ, r.Prime → r ∣ N → r ∣ d ∧ ¬ (r * r ∣ N) := by
    intro r hr hrN
    have hrZ : (r : ℤ) ∣ (cyclotomic d ℤ).eval 2 := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      simpa using hrN
    have hint : r ∣ d := by
      rcases primitive_or_intrinsic (a := 2) hd0 hr hrZ with hprim | hint
      · exact absurd hprim (h r hr hrZ)
      · exact hint
    refine ⟨hint, ?_⟩
    intro hsqN
    have hsqZ : ((r : ℤ)) ^ 2 ∣ (cyclotomic d ℤ).eval 2 := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast]
      simpa [pow_two] using hsqN
    exact intrinsic_sq_not_dvd hd hr hint hrZ hsqZ
  have hsf : Squarefree N := Nat.squarefree_iff_prime_squarefree.mpr
    (fun r hr hsq => (hpf r hr (dvd_trans (dvd_mul_right r r) hsq)).2 hsq)
  have hsub : N.primeFactors ⊆ d.primeFactors := by
    intro r hr
    obtain ⟨hrp, hrN, _⟩ := Nat.mem_primeFactors.mp hr
    exact Nat.mem_primeFactors.mpr ⟨hrp, (hpf r hrp hrN).1, by omega⟩
  calc N = ∏ p ∈ N.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsf).symm
    _ ∣ ∏ p ∈ d.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- **Existence from one inequality**: if `rad(d) < |Φ_d(2)|`, a primitive prime
    exists — a prime `q` with `ord_q(2) = d` (hence `q ≡ 1 (mod d)`, and `q` is a
    primitive prime divisor of `2^d − 1`).  The missing input for unconditional
    Zsygmondy is exactly this size bound. -/
theorem exists_primitive_of_rad_lt {d : ℕ} (hd : 1 < d)
    (hsize : (∏ p ∈ d.primeFactors, p) < ((cyclotomic d ℤ).eval 2).natAbs) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ (cyclotomic d ℤ).eval 2 ∧
      orderOf ((2 : ℕ) : ZMod q) = d := by
  by_contra hno
  push Not at hno
  have h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (cyclotomic d ℤ).eval 2 →
      orderOf ((2 : ℕ) : ZMod q) ≠ d := fun q hq hdvd => hno q hq hdvd
  have hdvd := no_primitive_cyclotomic_dvd_rad hd h
  have hrad0 : 0 < ∏ p ∈ d.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have := Nat.le_of_dvd hrad0 hdvd
  omega

end SalemTower
