module

public import Compass.Basis
public import Compass.Equivalence
public import Mathlib.NumberTheory.Fermat
import all Init.Data.Nat.Power2.Basic

import Mathlib.Analysis.Complex.Angle

public section

open scoped Real IntermediateField

theorem Nat.isPowerOfTwo_mul_iff (m n : ℕ) :
    (m * n).isPowerOfTwo ↔ m.isPowerOfTwo ∧ n.isPowerOfTwo where
  mp h := by
    constructor
    · apply h.dvd
      simp
    · apply h.dvd
      simp
  mpr h := by
    rw [Nat.isPowerOfTwo] at ⊢ h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    use a + b
    rw [pow_add, ha, hb]

theorem Nat.isPowerOfTwo_prod_iff {ι : Type*} (f : ι → ℕ) (s : Finset ι) :
    (∏ i ∈ s, f i).isPowerOfTwo ↔ ∀ i ∈ s, (f i).isPowerOfTwo := by
  induction s using Finset.cons_induction with
  | empty => simpa using Nat.isPowerOfTwo_one
  | cons a s h ih =>
    simp [Nat.isPowerOfTwo_mul_iff, ih]

theorem Nat.isPowerOfTwo_pow_iff (m n : ℕ) :
    (m ^ n).isPowerOfTwo ↔ m.isPowerOfTwo ∨ n = 0 := by
  conv_lhs => rw [show n = (Finset.range n).card by simp]
  rw [← Finset.prod_const, Nat.isPowerOfTwo_prod_iff]
  constructor
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    left
    apply h 0
    simp [Nat.pos_iff_ne_zero, hn]
  · grind

theorem Nat.isPowerOfTwo_two : isPowerOfTwo 2 := by decide

theorem Nat.isPowerOfTwo_and_isPowerOfTwo_sub_one (n : ℕ) :
    n.isPowerOfTwo ∧ (n - 1).isPowerOfTwo ↔ n = 2 where
  mp h := by
    simp_rw [Nat.isPowerOfTwo] at h
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
    rw [Nat.sub_eq_iff_eq_add (by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      symm at hp
      simp [h0] at hp
    )] at hq
    rw [hq] at hp
    have hqp : q ≤ p := by
      rw [← (pow_right_strictMono₀ (show 1 < 2 by simp)).le_iff_le]
      simp [← hp]
    obtain ⟨r, rfl⟩ :=  Nat.exists_eq_add_of_le hqp
    have h := Nat.eq_sub_of_add_eq' hp
    rw [pow_add, ← mul_sub_one] at h
    rw [hq, Nat.eq_one_of_mul_eq_one_right h.symm]
  mpr h := by simp [h, isPowerOfTwo_two, isPowerOfTwo_one]

theorem Nat.fermatNumber_ne_zero (n : ℕ) :
    n.fermatNumber ≠ 0 := (zero_ne_add_one (2 ^ 2 ^ n)).symm


theorem Nat.isPowerOfTwo_totient_iff {n : ℕ} (hn : n ≠ 0) :
    n.totient.isPowerOfTwo ↔ ∃ (k : ℕ) (s : Finset ℕ), (∀ m ∈ s, (Nat.fermatNumber m).Prime) ∧
      n = 2 ^ k * ∏ m ∈ s, Nat.fermatNumber m := by
  rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.isPowerOfTwo_prod_iff]
  simp_rw [Nat.isPowerOfTwo_mul_iff, Nat.isPowerOfTwo_pow_iff]
  conv_lhs =>
    intro i
    rw [← Classical.imp_and_neg_imp_iff (i = 2) (q := i ∈ n.factorization.support → _)]
  rw [forall_and]
  simp_rw [forall_eq, Nat.isPowerOfTwo_two, true_or, show 2 - 1 = 1 by simp, Nat.isPowerOfTwo_one,
    true_and, implies_true, true_and]
  conv_lhs =>
    intro i hi2 hisupport
    rw [or_and_right, Nat.isPowerOfTwo_and_isPowerOfTwo_sub_one]
    simp only [hi2, false_or]
    rw [Nat.sub_eq_iff_eq_add (by
      rw [Nat.one_le_iff_ne_zero]
      rw [← Finsupp.mem_support_iff]
      exact hisupport
    ), show 0 + 1 = 1 by simp]
  constructor
  · intro h
    have hfermat : ∀ c ∈ n.factorization.support, c ≠ 2 → ∃ k, c = Nat.fermatNumber k := by
      intro c hc hc2
      specialize h c hc2 hc
      simp only [support_factorization, mem_primeFactors] at hc
      obtain ⟨hprime, hdvd, _⟩ := hc
      obtain ⟨r, hr⟩ := h.2
      rw [Nat.sub_eq_iff_eq_add (by
        rw [Nat.one_le_iff_ne_zero]
        intro hc0
        simp [hc0, Nat.not_prime_zero] at hprime
      )] at hr
      rw [hr] at hprime
      obtain ⟨k, hk⟩ := Nat.pow_of_pow_add_prime (by simp) (fun h ↦ by
        simp [hr, h] at hc2) hprime
      use k
      rw [hr, hk, fermatNumber]
    choose! k hk using hfermat
    use n.factorization 2, {c ∈ n.factorization.support | c ≠ 2}.image k
    constructor
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨c, hc, hcm⟩ := hm
      rw [Finset.mem_filter] at hc
      rw [← hcm, ← hk c hc.1 hc.2]
      simp only [support_factorization, mem_primeFactors] at hc
      exact hc.1.1
    · conv_lhs =>
        rw [← Nat.prod_factorization_pow_eq_self hn, Finsupp.prod]
        rw [← Finset.prod_filter_mul_prod_filter_not _ (· = 2)]
      congrm ?_ * ?_
      · rw [Finset.filter_eq']
        split_ifs with h2
        · simp
        · rw [Finsupp.notMem_support_iff.mp h2]
          simp
      · rw [Finset.prod_image (by
          intro x hx y hy h
          rw [Finset.mem_coe, Finset.mem_filter] at hx hy
          have hkx := hk x hx.1 hx.2
          have hky := hk y hy.1 hy.2
          rw [hkx, hky, h]
        )]
        refine Finset.prod_congr rfl fun c hc ↦ ?_
        rw [Finset.mem_filter] at hc
        rw [(h c hc.2 hc.1).1, ← hk c hc.1 hc.2, pow_one]
  · rintro ⟨k, s, hs, rfl⟩
    intro i hi2 hi
    have hi' : Prime i ∧ i ∣ 2 ^ k * ∏ m ∈ s, m.fermatNumber ∧ ¬∏ m ∈ s, m.fermatNumber = 0 := by
      simpa using hi
    obtain ⟨hprime, hdvd, hprod⟩ := hi'
    have hcoprime : Nat.Coprime i 2 := by
      rw [Nat.coprime_primes hprime Nat.prime_two]
      exact hi2
    have hdvd' : i ∣ ∏ m ∈ s, m.fermatNumber := by
      refine Nat.Coprime.dvd_of_dvd_mul_left ?_ hdvd
      exact Nat.Coprime.pow_right _ hcoprime
    rw [Prime.dvd_finsetProd_iff hprime.prime] at hdvd'
    obtain ⟨c, hcs, hic⟩ := hdvd'
    rw [← (Nat.Prime.coprime_iff_not_dvd hprime).not_left,
      (Nat.coprime_primes hprime (hs c hcs)).not, not_ne_iff] at hic
    constructor
    · rw [Nat.factorization_mul (by simp) hprod]
      rw [Nat.factorization_prod fun k _ ↦ Nat.fermatNumber_ne_zero k]
      rw [Nat.factorization_pow]
      suffices k * factorization 2 i + ∑ k ∈ s, k.fermatNumber.factorization i = 1 by simpa
      rw [(Nat.factorization_eq_zero_iff 2 i).mpr (by
        by_contra!
        have : Prime i ∧ i ∣ 2 := by simpa using this
        exact (Nat.Prime.coprime_iff_not_dvd this.1).mp hcoprime this.2)]
      rw [mul_zero, zero_add]
      rw [Finset.sum_eq_single c (fun b hb hbc ↦ by
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [← Nat.Prime.coprime_iff_not_dvd hprime,
          (Nat.coprime_primes hprime (hs b hb)), hic,
          Nat.fermatNumber_injective.ne_iff]
        exact hbc.symm
      ) (fun h ↦ (h hcs).elim)]
      rw [← hic, hprime.factorization_self]
    · rw [hic]
      use 2 ^ c
      simp [fermatNumber]

theorem exp_mem_constructibleClosure_iff {n : ℕ} (hn : n ≠ 0) :
    Complex.exp ((n⁻¹ : ℂ) * (2 * π * Complex.I)) ∈ constructibleClosure ℚ ℂ ↔
    ∃ (k : ℕ) (s : Finset ℕ), (∀ m ∈ s, (Nat.fermatNumber m).Prime) ∧
      n = 2 ^ k * ∏ m ∈ s, Nat.fermatNumber m := by
  rw [← Nat.isPowerOfTwo_totient_iff hn]
  have : NeZero n := ⟨hn⟩
  have : IsCyclotomicExtension {n} ℚ ℚ⟮Complex.exp ((n⁻¹ : ℂ) * (2 * π * Complex.I))⟯ := by
    refine (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin n
      ℚ ℂ ℚ⟮Complex.exp ((n⁻¹ : ℂ) * (2 * π * Complex.I))⟯ ?_).mpr rfl
    rw [IsPrimitiveRoot.iff_def]
    constructor
    · rw [← Complex.exp_nat_mul, mul_inv_cancel_left₀ (by simpa using hn),
        Complex.exp_two_pi_mul_I]
    · intro l
      rw [← Complex.exp_nat_mul, ← mul_assoc, Complex.exp_eq_one_iff]
      simp_rw [mul_left_inj' (show 2 * π * Complex.I ≠ 0 by simp)]
      simp_rw [mul_inv_eq_iff_eq_mul₀ (show (n : ℂ) ≠ 0 by simpa using hn)]
      norm_cast
      rintro ⟨m, h⟩
      rw [← Int.ofNat_dvd, h]
      simp
  have hsplit : Polynomial.IsSplittingField ℚ ℚ⟮Complex.exp ((n⁻¹ : ℂ) * (2 * π * Complex.I))⟯
      (Polynomial.cyclotomic n ℚ) := by
    apply IsCyclotomicExtension.splitting_field_cyclotomic
  have hgalois : IsGalois ℚ ℚ⟮Complex.exp ((n⁻¹ : ℂ) * (2 * π * Complex.I))⟯ :=
    IsGalois.of_separable_splitting_field (Polynomial.separable_cyclotomic n ℚ)
  rw [mem_constructibleClosure_iff_isPowerOfTwo_finrank_adjoin hgalois]
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.pos_iff_ne_zero.mpr hn)
  rw [IsCyclotomicExtension.finrank _ hirr]

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

theorem constructible_polygon {n : ℕ} (hn : 2 ≤ n) {a b : P} (h : a ≠ b) :
    (∃ (c : P), a ≠ c ∧ ConstructiblePoint {a, b} c ∧ ∠ b a c = 2 * π / n) ↔
    ∃ (k : ℕ) (s : Finset ℕ), (∀ m ∈ s, (Nat.fermatNumber m).Prime) ∧
      n = 2 ^ k * ∏ m ∈ s, Nat.fermatNumber m := by
  have hn0 : n ≠ 0 := fun h ↦ by simp [h] at hn
  rw [← exp_mem_constructibleClosure_iff hn0, constructibleClosure_transfer_ℚ_01,
    ← constructiblePoint_iff_mem_constructibleClosure (by grind)
    (ConstructiblePoint.given 0 (by simp)) (ConstructiblePoint.given 1 (by simp))]
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  have hab : ‖b -ᵥ a‖ ≠ 0 := by simpa using h.symm
  have hab' : ‖b -ᵥ a‖⁻¹ ≠ 0 := by simpa using h.symm
  let e : P ≃ᵃⁱ[ℝ] ℂ := equivComplex a (‖b -ᵥ a‖⁻¹ • (b -ᵥ a) +ᵥ a) (by
    simp [dist_eq_norm_vsub', norm_smul, hab]
  )
  have ha : e ((AffineMap.homothety a ‖b -ᵥ a‖⁻¹) a) = 0 := by
    rw [AffineMap.homothety_apply_same]
    rw [equivComplex_left]
  have hb : e ((AffineMap.homothety a ‖b -ᵥ a‖⁻¹) b) = 1 := by
    rw [AffineMap.homothety_apply]
    rw [equivComplex_right]
  have hangle (c : P) : ∠ b a c = ∠ 1 0 (e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c)) := by
    rw [← ha, ← hb]
    simp_rw [← AffineIsometryEquiv.coe_toAffineIsometry]
    rw [AffineIsometry.angle_map, EuclideanGeometry.angle_homothety _ _ _ _ hab']
  conv_lhs =>
    right; ext c
    rw [← constructiblePoint_iff_homothety a hab']
    rw [ConstructiblePoint.map_iff e]
    rw [Set.image_pair, Set.image_pair, ha, hb]
    rw [hangle]
  have hexp : ((↑n)⁻¹ * (2 * π * Complex.I)) = (2 * π / n : ℝ) * Complex.I := by
    push_cast; ring
  have h0 : ConstructiblePoint {0, 1} (0 : ℂ) := ConstructiblePoint.given 0 (by simp)
  have h1 : ConstructiblePoint {0, 1} (1 : ℂ) := ConstructiblePoint.given 1 (by simp)
  constructor
  · rintro ⟨c, hac, hc, hangle⟩
    apply ConstructiblePoint.lineCircle line[ℝ, 0, Complex.exp ((↑n)⁻¹ * (2 * π * Complex.I))]
      ⟨0, 1⟩
    · apply ConstructibleLine.twoPoints 0
        (‖e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c)‖ * Complex.exp ((↑n)⁻¹ * (2 * π * Complex.I))) h0
      · apply ConstructiblePoint.twoCircles ⟨0, ‖e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c)‖⟩
          ⟨1, dist 1 (e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c))⟩
        · apply ConstructibleCircle.centerRadius _ _ h0 hc
          simp [mem_sphere]
        · apply ConstructibleCircle.centerRadius _ _ h1 hc
          simp [mem_sphere']
        · simp
        · simp only [mem_sphere, dist_zero_right, Complex.norm_mul, Complex.norm_real, norm_norm]
          rw [hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
        · simp_rw [mem_sphere']

          sorry
      ·
        sorry
      · apply left_mem_affineSpan_pair
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use ‖e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c)‖
        simp [AffineMap.lineMap_apply_module]
      ·
        sorry
    · exact ConstructibleCircle.centerRadius _ 1 h0 h1 (by simp [mem_sphere])
    · apply right_mem_affineSpan_pair
    · rw [mem_sphere, dist_eq_norm_sub, sub_zero, hexp, Complex.norm_exp_ofReal_mul_I]
  · intro h
    refine ⟨(AffineMap.homothety a ‖b -ᵥ a‖) <| e.symm <|
      Complex.exp ((↑n)⁻¹ * (2 * π * Complex.I)), ?_, ?_, ?_⟩
    · rw [← (AffineMap.homothety_injective a hab').ne_iff]
      rw [← AffineMap.homothety_mul_apply, inv_mul_cancel₀ hab,
        AffineMap.homothety_one, AffineMap.id_apply]
      rw [← e.injective.ne_iff, AffineIsometryEquiv.apply_symm_apply]
      rw [ha]
      symm
      simp
    · rw [← AffineMap.homothety_mul_apply, inv_mul_cancel₀ hab, AffineMap.homothety_one,
        AffineMap.id_apply, AffineIsometryEquiv.apply_symm_apply]
      exact h
    · rw [← AffineMap.homothety_mul_apply, inv_mul_cancel₀ hab, AffineMap.homothety_one,
        AffineMap.id_apply, AffineIsometryEquiv.apply_symm_apply]
      rw [EuclideanGeometry.angle]
      simp_rw [vsub_eq_sub, sub_zero]
      rw [Complex.angle_one_left (by simp)]
      rw [hexp]
      rw [Complex.arg_exp_mul_I]
      rw [(toIocMod_eq_self _).mpr (by
        simp only [Set.mem_Ioc, le_neg_add_iff_add_le]
        constructor
        · trans 0
          · simpa using Real.pi_pos
          · positivity
        · rw [← le_sub_iff_add_le']
          conv_rhs => rw [two_mul, add_sub_cancel_right]
          rw [div_le_iff₀' (by simpa using Nat.pos_of_ne_zero hn0)]
          exact mul_le_mul_of_nonneg_right (by simpa using hn) Real.pi_nonneg
      )]
      rw [abs_eq_self]
      positivity

end EuclideanGeometry
