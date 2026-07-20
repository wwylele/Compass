module

public import Compass.ConstructibleNumber
public import Mathlib.NumberTheory.Fermat
import all Init.Data.Nat.Power2.Basic

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
