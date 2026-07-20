import SalemTower.CyclotomicOrder
import SalemTower.OrderLift
import SalemTower.DicksonTower
import SalemTower.LucasLehmerTower
import SalemTower.MersenneBridge
import SalemTower.MersenneCapstone
import SalemTower.FermatSplitting
import SalemTower.RungWieferich
import SalemTower.SplitCriterion
import SalemTower.ExtensionGrade
import SalemTower.DicksonTraceTest
import SalemTower.TernaryTower
import SalemTower.ZsygmondyScaffold
import SalemTower.UnitAntiperiod
import SalemTower.MersenneSeedOrder
import SalemTower.ZsygmondyReduction

/-! Axiom audit: every theorem, discharged. -/
#print axioms SalemTower.cyclotomic_eval_cast
#print axioms SalemTower.cyclotomic_primeFactor_orderOf
#print axioms SalemTower.cyclotomic_primeFactor_dvd_sub_one
#print axioms SalemTower.sq_dvd_pow_mul_of_dvd
#print axioms SalemTower.wieferich_iff
#print axioms SalemTower.not_wieferich_two
#print axioms SalemTower.not_wieferich_three
#print axioms SalemTower.sq_dvd_two_pow_mul
#print axioms SalemTower.dvd_pow_orderOf_sub_one
#print axioms SalemTower.orderOf_lift_dichotomy
#print axioms SalemTower.dickson_two
#print axioms SalemTower.dickson_double
#print axioms SalemTower.dickson_cosh
#print axioms SalemTower.dickson_trace_atom
#print axioms SalemTower.TowerLL.tower_lucas_lehmer
#print axioms SalemTower.TowerLL.atom_lucas_lehmer_step
#print axioms SalemTower.TowerLL.atom_four_base
#print axioms SalemTower.TowerLL.tower_cosh
#print axioms SalemTower.tower_eq_lucasLehmer
#print axioms SalemTower.tower_step_at_four
#print axioms SalemTower.tower_residue
#print axioms SalemTower.tower_eq_lucasLehmerResidue
#print axioms SalemTower.mersenne_prime_iff_tower_vanishes
#print axioms SalemTower.mersenne_prime_of_tower_vanishes
#print axioms SalemTower.tower_vanishes_of_mersenne_prime
#print axioms SalemTower.fermat_unit_order_dvd
#print axioms SalemTower.fermat_unit_order_two_power
#print axioms SalemTower.zmod_pow_eq_one_iff
#print axioms SalemTower.proper_rung_not_dvd
#print axioms SalemTower.sq_dvd_pow_sub_one_iff_sq_dvd_cyclotomic
#print axioms SalemTower.cyclotomic_sq_dvd_iff_orderOf_eq
#print axioms SalemTower.tower_rung_wieferich
#print axioms SalemTower.split_common_root_orderOf
#print axioms SalemTower.split_common_root_dvd_sub_one
#print axioms SalemTower.tower_split_criterion
#print axioms SalemTower.adjoinRoot_natCard
#print axioms SalemTower.order_dvd_extension_card_sub_one
#print axioms SalemTower.extension_grade
#print axioms SalemTower.dickson_eval_unit_add_inv
#print axioms SalemTower.dickson_frobenius_guard
#print axioms SalemTower.dickson_eval_double
#print axioms SalemTower.ternary_pair_sq
#print axioms SalemTower.ternary_rung_sq
#print axioms SalemTower.tripling_ascent
#print axioms SalemTower.cyclotomic_eval_dvd_pow_sub_one
#print axioms SalemTower.primitive_or_intrinsic
#print axioms SalemTower.two_rungs_dvd
#print axioms SalemTower.exists_primitive_of_not_intrinsic_only
#print axioms SalemTower.dickson_zero_iff_pow_eq_neg_one
#print axioms SalemTower.factorization_orderOf_of_pow_eq_neg_one
#print axioms SalemTower.orderOf_eq_two_pow_of_pow_eq_neg_one
#print axioms SalemTower.pow_orderOf_half_eq_neg_one
#print axioms SalemTower.mersenne_prime_seed_order
#print axioms SalemTower.sub_one_mul_cyclotomic_dvd
#print axioms SalemTower.geom_sum_sq_modeq
#print axioms SalemTower.intrinsic_sq_not_dvd
#print axioms SalemTower.no_primitive_cyclotomic_dvd_rad
#print axioms SalemTower.exists_primitive_of_rad_lt

/-! The Challenge statements, re-declared at root level (comparator model). -/

open Polynomial in
/-- The Salem/Dickson tower at atom 4 is Mathlib's Lucas–Lehmer sequence. -/
theorem tower_eq_lucasLehmer :
    ∀ k : ℕ, (dickson 1 (1 : ℤ) (2 ^ k)).eval 4 = LucasLehmer.s k :=
  SalemTower.tower_eq_lucasLehmer

open Polynomial in
/-- Mersenne primality is decided by the tower: `2^(p'+3) − 1` is prime iff
    `D_{2^(p'+1)}(4)` vanishes mod it. -/
theorem mersenne_prime_iff_tower_vanishes (p' : ℕ) :
    (mersenne (p' + 3)).Prime ↔
      (((dickson 1 (1 : ℤ) (2 ^ (p' + 1))).eval 4 : ℤ) : ZMod (2 ^ (p' + 3) - 1)) = 0 :=
  SalemTower.mersenne_prime_iff_tower_vanishes p'

open Polynomial in
/-- The rung-local Wieferich theorem: `q² ∣ Φ_n(a)` iff the order of `a` fails
    to lift from `q` to `q²` (i.e. stays exactly `n`). -/
theorem cyclotomic_sq_dvd_iff_orderOf_eq {n a q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hqn : ¬ q ∣ n) (hqa : ¬ q ∣ a)
    (hdvd : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval (a : ℤ) ↔
      orderOf ((a : ZMod (q ^ 2))) = n :=
  SalemTower.cyclotomic_sq_dvd_iff_orderOf_eq hn hq hqn hqa hdvd

#print axioms tower_eq_lucasLehmer
#print axioms mersenne_prime_iff_tower_vanishes
#print axioms cyclotomic_sq_dvd_iff_orderOf_eq

open Polynomial in
/-- The trace–antiperiod dictionary: over any commutative ring, the Dickson
    trace zero at rung n is exactly the antiperiod, `D_n(u + u⁻¹) = 0 ↔ u^(2n) = −1`. -/
theorem dickson_zero_iff_pow_eq_neg_one {R : Type*} [CommRing R] (u : Rˣ) (n : ℕ) :
    (dickson 1 (1 : R) n).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) = 0 ↔
      ((u : R)) ^ (2 * n) = -1 :=
  SalemTower.dickson_zero_iff_pow_eq_neg_one u n

open Polynomial in
/-- A Mersenne prime is a rung split of the seed polynomial: `2^(p'+3) − 1` prime
    forces a unit of multiplicative order exactly `2^(p'+3)` in
    `AdjoinRoot (x² − 4x + 1)` over `ZMod (2^(p'+3) − 1)` — the Lucas–Lehmer seed. -/
theorem mersenne_prime_seed_order (p' : ℕ) (hp : (mersenne (p' + 3)).Prime) :
    ∃ u : (AdjoinRoot (C 1 * X ^ 2 + C (-4) * X + C 1 :
        Polynomial (ZMod (2 ^ (p' + 3) - 1))))ˣ,
      orderOf u = 2 ^ (p' + 3) :=
  SalemTower.mersenne_prime_seed_order p' hp

open Polynomial in
/-- The Zsygmondy reduction: if `2^d − 1` has no primitive prime divisor at
    index d, then `|Φ_d(2)|` divides the radical of d. -/
theorem no_primitive_cyclotomic_dvd_rad {d : ℕ} (hd : 1 < d)
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ (cyclotomic d ℤ).eval 2 →
      orderOf ((2 : ℕ) : ZMod q) ≠ d) :
    ((cyclotomic d ℤ).eval 2).natAbs ∣ ∏ p ∈ d.primeFactors, p :=
  SalemTower.no_primitive_cyclotomic_dvd_rad hd h

#print axioms dickson_zero_iff_pow_eq_neg_one
#print axioms mersenne_prime_seed_order
#print axioms no_primitive_cyclotomic_dvd_rad
