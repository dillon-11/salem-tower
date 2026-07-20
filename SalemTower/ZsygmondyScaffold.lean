import SalemTower.RungWieferich

/-!
# the primitive/intrinsic dichotomy for cyclotomic values
Step 1 + scaffold of the merged Zsygmondy/BHV residue (`zsygmondy-bhv-one-residue`):
the existence half of Zsygmondy reduces to a size bound, because every prime factor
of `Φ_n(a)` is either PRIMITIVE (order exactly n — the master theorem) or
INTRINSIC (divides n).  What is proven here:
  • `cyclotomic_eval_dvd_pow_sub_one` — `Φ_n(a) ∣ aⁿ − 1` over ℤ (the rung divides
    the ledger);
  • `primitive_or_intrinsic` — a prime factor of `Φ_n(a)` has `ord_q(a) = n` or
    `q ∣ n`: the dichotomy that types every tower prime;
  • `two_rungs_dvd` — a prime dividing two rungs `Φ_n(a)` and `Φ_d(a)` (d a proper
    divisor of n) must be intrinsic (`q ∣ n`) — the separability face, contrapositive
    of `TowerRungWieferich.proper_rung_not_dvd`;
  • `exists_primitive_of_not_intrinsic_only` — the EXISTENCE REDUCTION: if some
    prime factor of `Φ_n(a)` fails to divide n, a primitive prime (order exactly n)
    exists, hence a prime `≡ 1 (mod n)`.
REMAINDER (the honest gap, typed in the residue): the Birkhoff–Vandiver valuation
bound — the intrinsic part of `Φ_n(a)` is at most the largest prime factor of n to
the first power — plus the size bound `|Φ_n(a)| > n` (Mathlib has
`sub_one_pow_totient_lt_cyclotomic_eval` for the archimedean face).  Together with
this file those force existence for n > 6; the LTE machinery for the valuation
bound is `multiplicity.Int.pow_sub_pow`.
Axiom-clean, `sorry`-free.
-/

namespace SalemTower

open Polynomial

/-- **The rung divides the ledger**: `Φ_n(a) ∣ aⁿ − 1` over ℤ. -/
theorem cyclotomic_eval_dvd_pow_sub_one {n : ℕ} (hn : 0 < n) (a : ℤ) :
    (cyclotomic n ℤ).eval a ∣ a ^ n - 1 := by
  have h := congrArg (Polynomial.eval a) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
  rw [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at h
  rw [← h, ← Nat.cons_self_properDivisors hn.ne', Finset.prod_cons]
  exact Dvd.intro _ rfl

/-- **The primitive/intrinsic dichotomy**: a prime factor `q` of `Φ_n(a)` either has
    `a` of multiplicative order exactly `n` mod `q` (primitive), or divides `n`
    (intrinsic).  Every tower prime is one of the two types. -/
theorem primitive_or_intrinsic {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    orderOf ((a : ZMod q)) = n ∨ q ∣ n := by
  by_cases hqn : q ∣ n
  · exact Or.inr hqn
  · exact Or.inl (SalemTower.cyclotomic_primeFactor_orderOf hn hq hqn hdvd)

/-- **Two rungs force intrinsic**: a prime dividing both `Φ_n(a)` and a proper-rung
    value `Φ_d(a)` (`d` a proper divisor of `n`) must divide `n`.  (Separability of
    `Xⁿ − 1` mod `q` fails only at `q ∣ n`.) -/
theorem two_rungs_dvd {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ))
    {d : ℕ} (hd : d ∈ n.properDivisors)
    (hdvd' : (q : ℤ) ∣ (cyclotomic d ℤ).eval (a : ℤ)) : q ∣ n := by
  by_contra hqn
  exact SalemTower.proper_rung_not_dvd hn hq hqn hdvd d hd hdvd'

/-- **The existence reduction**: if `Φ_n(a)` has any prime factor coprime to `n`,
    then a primitive prime exists — a prime `q` with `ord_q(a) = n`, hence
    `q ≡ 1 (mod n)`.  This reduces Zsygmondy existence to the size statement
    "`Φ_n(a)` is not intrinsic-only" (Birkhoff–Vandiver bound + `Φ_n(a) > n`). -/
theorem exists_primitive_of_not_intrinsic_only {n a : ℕ} (hn : 0 < n) (ha : 1 < a)
    (h : ¬ ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ) → q ∣ n) :
    ∃ q : ℕ, q.Prime ∧ orderOf ((a : ZMod q)) = n ∧ n ∣ q - 1 := by
  push_neg at h
  obtain ⟨q, hq, hdvd, hqn⟩ := h
  refine ⟨q, hq, SalemTower.cyclotomic_primeFactor_orderOf hn hq hqn hdvd, ?_⟩
  -- q ∤ a: q divides Φ_n(a) ∣ aⁿ − 1, so q ∣ a would give q ∣ 1
  have hqa' : ¬ q ∣ a := by
    intro hdvda
    have h1 : (q : ℤ) ∣ (a : ℤ) ^ n - 1 :=
      hdvd.trans (cyclotomic_eval_dvd_pow_sub_one hn (a : ℤ))
    have h2 : (q : ℤ) ∣ (a : ℤ) ^ n :=
      Int.natCast_dvd_natCast.mpr (hdvda.trans (dvd_pow_self a hn.ne'))
    have h3 : (q : ℤ) ∣ 1 := by
      have := dvd_sub h2 h1
      simpa using this
    have h4 : (q : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
    exact hq.one_lt.ne' (by exact_mod_cast h4)
  exact SalemTower.cyclotomic_primeFactor_dvd_sub_one hn hq hqn hqa' hdvd

end SalemTower
