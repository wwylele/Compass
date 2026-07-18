module

public import Compass.Equivalence

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.FieldTheory.PrimeField
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat

/-!

# The Impossibility of Trisecting the Angle and Doubling the Cube

This file proves theorem #8 from Freek Wiedijk's list of 100 theorems.

## Main Declarations

- `EuclideanGeometry.not_exist_angle_trisection`: the impossibility of trisecting the angle.
- `EuclideanGeometry.not_exist_doubling_cube`: the impossibility of doubling the cube.

-/

public section

open ComplexConjugate
open scoped Real

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

theorem AffineIsometryEquiv.trans_apply {𝕜 : Type*} {V : Type*} {V₂ : Type*} {V₃ : Type*}
    {P : Type*} {P₂ : Type*} {P₃ : Type*}
    [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    [PseudoMetricSpace P] [NormedAddTorsor V P] [SeminormedAddCommGroup V₂]
    [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
    [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃]
    [NormedAddTorsor V₃ P₃] (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) (x : P) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

@[simp]
theorem arccos_half : Real.arccos 2⁻¹ = π / 3 := by
  apply Real.arccos_eq_of_eq_cos
  · exact div_nonneg Real.pi_nonneg (by simp)
  · grind [Real.pi_nonneg]
  · simp

theorem irreducible_861 :
    Irreducible (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℚ) := by
  have hdegeee :
      (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℚ).natDegree = 3 := by
    compute_degree!
  have hdegree' :
      (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℤ).natDegree = 3 := by
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdegeee]
  intro x h
  have haeval : (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℤ).aeval x = 0 := by
    simpa [map_ofNat, Polynomial.IsRoot.def] using h
  have hnum : IsFractionRing.num ℤ x ∣ 1 := by simpa using num_dvd_of_is_root haeval
  have hnum : x.num = 1 ∨ x.num = -1 := by
    simpa [← isUnit_iff_dvd_one, Int.isUnit_iff] using x.isFractionRingNum.symm.dvd.trans hnum
  have hden := den_dvd_of_is_root haeval
  rw [Polynomial.leadingCoeff, hdegree', Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
    Polynomial.coeff_one] at hden
  have hden : (IsFractionRing.den ℤ x).val ∣ 8 := by simpa using hden
  have hden : x.den ∣ 8 := by
    simpa using x.isFractionRingDen.symm.dvd.trans (Int.natAbs_dvd_natAbs.mpr hden)
  have hdenle : x.den ≤ 8 := Nat.le_of_dvd (by simp) hden
  interval_cases hdeneq : x.den
  · simp at hden
  · rcases hnum with hnum | hnum
    · have hx : x = 1 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
  · rcases hnum with hnum | hnum
    · have hx : x = 1 / 2 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 / 2 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
  · simp at hden
  · rcases hnum with hnum | hnum
    · have hx : x = 1 / 4 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 / 4 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
  · simp at hden
  · simp at hden
  · simp at hden
  · rcases hnum with hnum | hnum
    · have hx : x = 1 / 8 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 / 8 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval

theorem irreducible_cube_2 :
    Irreducible (Polynomial.X ^ 3 - 2 : Polynomial ℚ) := by
  have hdegeee : (Polynomial.X ^ 3 - 2 : Polynomial ℚ).natDegree = 3 := by
    compute_degree!
  have hdegree' : (Polynomial.X ^ 3 - 2 : Polynomial ℤ).natDegree = 3 := by
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdegeee]
  intro x h
  have haeval : (Polynomial.X ^ 3 - 2 : Polynomial ℤ).aeval x = 0 := by
    simpa [map_ofNat, Polynomial.IsRoot.def] using h
  have hnum : IsFractionRing.num ℤ x ∣ 2 := by simpa using num_dvd_of_is_root haeval
  have hnum : x.num ∣ 2 := by simpa using x.isFractionRingNum.symm.dvd.trans hnum
  have hnum2 : x.num.natAbs ≤ 2 := by simpa using Int.natAbs_le_of_dvd_ne_zero hnum (by simp)
  have hden := den_dvd_of_is_root haeval
  rw [Polynomial.leadingCoeff, hdegree', Polynomial.coeff_sub] at hden
  have hden : (IsFractionRing.den ℤ x).val ∣ 1 := by simpa using hden
  have hden : x.den = 1 := by
    simpa using x.isFractionRingDen.symm.dvd.trans (Int.natAbs_dvd_natAbs.mpr hden)
  interval_cases hnumabs : x.num.natAbs
  · rcases x.num.natAbs_eq with h | h
    · have hx : x = 0 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = 0 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
  · rcases x.num.natAbs_eq with h | h
    · have hx : x = 1 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
  · rcases x.num.natAbs_eq with h | h
    · have hx : x = 2 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -2 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval

noncomputable
def ratEquivBot {K : Type*} [Field K] [CharZero K] : ℚ ≃+* (⊥ : Subfield K) :=
    (algebraMap ℚ K).rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr Subfield.bot_eq_of_charZero.symm)

theorem re_im_image_01 : Complex.re '' {0, 1} ∪ Complex.im '' {0, 1} = {0, 1} := by
  ext x
  simp
  grind

theorem Subfield.closrue_01 {K : Type*} [Field K] : Subfield.closure ({0, 1} : Set K) = ⊥ := by
  refine Subfield.closure_eq_of_le ?_ (by simp)
  apply Set.pair_subset (by simp) (by simp)

theorem not_exist_angle_trisection :
    ∃ p₁ p₂ p₃ : P, p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
    ¬ ∃ q₁ q₂ q₃ : P,
    ConstructiblePoint {p₁, p₂, p₃} q₁ ∧
    ConstructiblePoint {p₁, p₂, p₃} q₂ ∧
    ConstructiblePoint {p₁, p₂, p₃} q₃ ∧
    3 * ∠ q₁ q₂ q₃ = ∠ p₁ p₂ p₃ := by
  push Not
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  let o := Nonempty.some (show Nonempty P from inferInstance)
  let basis : OrthonormalBasis (Fin 2) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hrank.out)
  refine ⟨((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o, o, basis 0 +ᵥ o, ?_, ?_, ?_, ?_⟩
  · suffices ((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o ≠ (0 : V) +ᵥ o by simpa
    rw [(vadd_right_cancel_iff _).ne]
    intro h
    have h := congr(basis.repr $h 0)
    simp at h
  · suffices (0 : V) +ᵥ o ≠ basis 0 +ᵥ o by simpa
    rw [(vadd_right_cancel_iff _).ne]
    intro h
    have h := congr(basis.repr $h 0)
    simp at h
  · rw [(vadd_right_cancel_iff _).ne]
    intro h
    have h := congr(basis.repr $h 0)
    simp at h
  intro q₁ q₂ q₃
  let e : P ≃ᵃⁱ[ℝ] ℂ := (AffineIsometryEquiv.vaddConst ℝ o).symm.trans
    (basis.equiv Complex.orthonormalBasisOneI (Equiv.refl _)).toAffineIsometryEquiv
  have hp₁ : e (((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o) =
      2⁻¹ + 2⁻¹ * ↑√3 * Complex.I := by
    simp_rw [e, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
        vadd_vsub]
    simp
  have hp₂ : e o = 0 := by simp [e]
  have hp₃ : e (basis 0 +ᵥ o) = 1 := by
    simp_rw [e, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
        vadd_vsub]
    simp
  have hinit : e '' {((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o, o, basis 0 +ᵥ o} =
      {2⁻¹ + 2⁻¹ * √3 * Complex.I, 0, 1} := by
    simp_rw [Set.image_insert_eq, Set.image_singleton, hp₁, hp₂, hp₃]
  have hnorm : ‖2⁻¹ + 2⁻¹ * ↑√3 * Complex.I‖ = 1 := by
    rw [← sq_eq_sq₀ (by simp) (by simp), Complex.sq_norm]
    suffices 2⁻¹ * 2⁻¹ + 2⁻¹ * √3 * (2⁻¹ * √3) = 1 by simpa [Complex.normSq]
    grind
  have hcons : ConstructiblePoint {2⁻¹ + 2⁻¹ * √3 * Complex.I, 0, 1}
      = ConstructiblePoint {0, 1} := by
    apply constructiblePoint_insert
    apply ConstructiblePoint.twoCircles ⟨0, 1⟩ ⟨1, 1⟩
    · apply ConstructibleCircle.centerRadius _ 1 (ConstructiblePoint.given 0 (by simp))
        (ConstructiblePoint.given 1 (by simp))
      simp [EuclideanGeometry.mem_sphere]
    · apply ConstructibleCircle.centerRadius _ 0 (ConstructiblePoint.given 1 (by simp))
        (ConstructiblePoint.given 0 (by simp))
      simp [EuclideanGeometry.mem_sphere]
    · simp
    · rw [mem_sphere, dist_zero_right, hnorm]
    · rw [mem_sphere, Complex.dist_eq, ← sq_eq_sq₀ (by simp) (by simp), Complex.sq_norm]
      suffices (2⁻¹ - 1) * (2⁻¹ - 1) + 2⁻¹ * √3 * (2⁻¹ * √3) = 1 by simpa [Complex.normSq]
      grind
  simp_rw [ConstructiblePoint.map_iff e, hinit, hcons,
    ← AffineIsometry.angle_map e.toAffineIsometry,
    AffineIsometryEquiv.coe_toAffineIsometry, hp₁, hp₂, hp₃]
  have hangle : ∠ (2⁻¹ + 2⁻¹ * √3 * Complex.I) 0 1 = π / 3 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
    simp [hnorm]
  rw [hangle]
  intro ha hb hc hangle
  rw [mul_comm 3, ← eq_div_iff_mul_eq (by simp), div_div, (show 3 * 3 = (9 : ℝ) by norm_num)]
    at hangle
  set a := e q₁
  set b := e q₂
  set c := e q₃
  have hcbne : c ≠ b := by
    intro h
    rw [h, angle_self_right] at hangle
    rw [div_eq_div_iff (by simp) (by simp)] at hangle
    have hangle : 7 * π = 0 := by linear_combination hangle
    simp at hangle
  have habne : a ≠ b := by
    intro h
    rw [h, angle_self_left] at hangle
    rw [div_eq_div_iff (by simp) (by simp)] at hangle
    have hangle : 7 * π = 0 := by linear_combination hangle
    simp at hangle
  have hcb0 : ‖c - b‖ ≠ 0 := by
    intro h
    have : c = b := by simpa [sub_eq_zero] using h
    exact hcbne this
  have hab0 : ‖a - b‖ ≠ 0 := by
    intro h
    have : a = b := by simpa [sub_eq_zero] using h
    exact habne this
  set d := ‖a - b‖ / ‖c - b‖ * (c - b) + b
  have hdbne : d ≠ b := by simp [d, sub_eq_zero, habne, hcbne]
  have hd : ConstructiblePoint {0, 1} d := by
    apply ConstructiblePoint.lineCircle line[ℝ, c, b] ⟨b, ‖a - b‖⟩
    · apply ConstructibleLine.twoPoints c b hc hb hcbne
      · exact left_mem_affineSpan_pair ℝ c b
      · exact right_mem_affineSpan_pair ℝ c b
      · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton]
        rw [vsub_eq_zero_iff_eq.ne]
        exact hcbne
    · apply ConstructibleCircle.centerRadius _ a hb ha
      simp [mem_sphere, dist_eq_norm]
    · suffices (‖a - b‖ / ‖c - b‖) • (c -ᵥ b) +ᵥ b ∈ line[ℝ, c, b] by
        simpa using this
      apply vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
      · apply right_mem_affineSpan_pair
      · apply smul_vsub_mem_vectorSpan_pair
    · simp [d, mem_sphere, hcb0]
  have habd : ∠ a b c = ∠ a b d := by
    apply angle_smul_right_of_pos _ (show 0 < (‖c - b‖ / ‖a - b‖) by
      apply div_pos
      · simpa using hcb0
      · simpa using hab0
    )
    suffices ‖c - b‖ / ‖a - b‖ * (‖a - b‖ / ‖c - b‖ * (c - b)) = c - b by simpa [d]
    rw [← mul_assoc, ← mul_div_assoc, div_mul_cancel₀ _ (by simpa using hab0),
      div_self (by simpa using hcb0), one_mul]
  rw [habd, EuclideanGeometry.angle,
    Complex.angle_eq_abs_arg (by simpa [sub_eq_zero] using habne)
    (by simpa [sub_eq_zero] using hdbne), vsub_eq_sub, vsub_eq_sub] at hangle
  set w := (a - b) / (d - b)
  have hwnorm : ‖w‖ = 1 := by simp [w, d, hcb0, hab0]
  have hwre : w.re = Real.cos (π / 9) := by
    rw [← Complex.norm_mul_exp_arg_mul_I w, hwnorm,
      Complex.ofReal_one, one_mul, Complex.exp_ofReal_mul_I_re]
    rcases abs_cases w.arg with ⟨hw, _⟩ | ⟨hw, _⟩
    · rw [← hw, hangle]
    · rw [← hangle, hw, Real.cos_neg]
  have hstar : ∀ x ∈ ({0, 1} : Set ℂ), conj x ∈ ({0, 1} : Set ℂ) := by simp
  have ha := ConstructiblePoint.mem_constructibleClosure hstar ha
  have hb := ConstructiblePoint.mem_constructibleClosure hstar hb
  have hd := ConstructiblePoint.mem_constructibleClosure hstar hd
  have hw : w ∈ constructibleClosure (Subfield.closure ({0, 1} : Set ℂ)) ℂ :=
    div_mem (sub_mem ha hb) (sub_mem hd hb)
  have hwremem : w.re ∈ constructibleClosure (Subfield.closure ({0, 1} : Set ℝ)) ℝ := by
    rw [← re_im_image_01]
    exact re_mem_constructibleClosure hw
  rw [Subfield.closrue_01] at hwremem
  have hquad : (minpoly (⊥ : Subfield ℝ) w.re).natDegree.isPowerOfTwo :=
    isPowerOfTwo_natDegree_minpoly_of_mem_constructibleClosure hwremem
  let p : Polynomial (⊥ : Subfield ℝ) :=
    8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1
  have hp : Irreducible p := by
    suffices Irreducible (Polynomial.mapEquiv ratEquivBot
        (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1)) by
      convert this
      simp [p]
    exact Irreducible.map _ irreducible_861
  have hwp : minpoly (⊥ : Subfield ℝ) w.re ∣ p := by
    apply minpoly.dvd
    suffices 8 * Real.cos (π / 9) ^ 3 - 6 * Real.cos (π / 9) - 1 = 0 by simpa [p, hwre, map_ofNat]
    suffices 2 * (4 * Real.cos (π / 9) ^ 3 - 3 * Real.cos (π / 9)) - 1 = 0 by
      linear_combination this
    rw [← Real.cos_three_mul, show 3 * (π / 9) = π / 3 by ring]
    simp
  have hminpoly : (minpoly (⊥ : Subfield ℝ) w.re).natDegree = 3 := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Irreducible.dvd_iff hp] at hwp
    rw [← Polynomial.degree_eq_degree_of_associated <| Or.resolve_left hwp (minpoly.not_isUnit _ _)]
    unfold p
    compute_degree!
  rw [hminpoly] at hquad
  contrapose! hquad
  decide

theorem dist_homothety_homothety {V : Type*} {P : Type*}
    [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V]
    (c : P) (r : 𝕜) (a b : P) :
    dist (AffineMap.homothety c r a) (AffineMap.homothety c r b) = ‖r‖ * dist a b := by
  simp_rw [dist_eq_norm_vsub, AffineMap.homothety_apply, vadd_vsub_vadd_cancel_right,
    ← smul_sub, norm_smul, vsub_sub_vsub_cancel_right]

theorem not_exist_doubling_cube {a b : P} (h : a ≠ b) :
    ¬ ∃ c d : P, ConstructiblePoint {a, b} c ∧ ConstructiblePoint {a, b} d ∧
    dist c d ^ 3 = 2 * dist a b ^ 3 := by
  classical
  push Not
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  have hab : ‖b -ᵥ a‖ ≠ 0 := by simpa using h.symm
  have hab' : ‖b -ᵥ a‖⁻¹ ≠ 0 := by simpa using h.symm
  intro c d hc hd hdist
  have hc := hc.map_homothety a hab'
  have hd := hd.map_homothety a hab'
  have hinit : (AffineMap.homothety a ‖b -ᵥ a‖⁻¹) '' {a, b} =
      {a, ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) +ᵥ a} := by
    rw [Set.image_pair]
    simp [AffineMap.homothety_apply]
  rw [hinit] at hc hd
  let v : Set V := {‖b -ᵥ a‖⁻¹ • (b -ᵥ a)}
  have hv : Orthonormal ℝ ((↑) : v → V) := by
    rw [orthonormal_subsingleton_iff]
    simp [v, norm_smul, hab]
  obtain ⟨u, basis, hvu, hbasis⟩ := Orthonormal.exists_orthonormalBasis_extension hv
  have hfilter : (u.filter (· ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card = 1 := by
    have h1 : ((u.filter (¬ · ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card) = 1 := by
      rw [Finset.card_eq_one]
      use ‖b -ᵥ a‖⁻¹ • (b -ᵥ a)
      grind
    suffices (u.filter (· ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card +
      ((u.filter (¬ · ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card) = 2 by
      rw [h1] at this
      grind
    rw [Finset.card_filter_add_card_filter_not]
    rw [← Module.finrank_eq_card_finset_basis basis.toBasis]
    exact hrank.out
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hfilter
  obtain ⟨hjmem, hjne⟩ : j ∈ u ∧ j ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) := by simpa using hj.ge
  have hmemu : ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) ∈ u := by
    apply Set.mem_of_subset_of_mem hvu
    simp [v]
  let ie : u ≃ Fin 2 := {
    toFun i := if i = ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) then 0 else 1
    invFun := ![⟨‖b -ᵥ a‖⁻¹ • (b -ᵥ a), hmemu⟩, ⟨j, hjmem⟩]
    left_inv i := by
      by_cases hi : i = ‖b -ᵥ a‖⁻¹ • (b -ᵥ a)
      · ext
        simp [hi]
      · ext
        suffices j = i by simpa [hi]
        symm
        suffices i.val ∈ ({j} : Finset _) by simpa
        rw [← hj]
        simp [hi]
    right_inv i := by
      fin_cases i
      · simp
      · simpa using hjne
  }
  have hbasis0 : basis ⟨‖b -ᵥ a‖⁻¹ • (b -ᵥ a), hmemu⟩ = ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) := by
    simp [hbasis]
  let e : P ≃ᵃⁱ[ℝ] ℂ :=
    (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
    (basis.equiv Complex.orthonormalBasisOneI ie).toAffineIsometryEquiv
  rw [ConstructiblePoint.map_iff e] at hc hd
  have hinit' : e '' {a, ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) +ᵥ a} = {0, 1} := by
    rw [Set.image_pair]
    congrm {?_, ?_}
    · simp [e]
    simp_rw [e, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
      vadd_vsub, LinearIsometryEquiv.coe_toAffineIsometryEquiv]
    rw [← hbasis0, OrthonormalBasis.equiv_apply_basis]
    simp [ie]
  rw [hinit'] at hc hd
  set c' := e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c)
  set d' := e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ d)
  have hstar : ∀ x ∈ ({0, 1} : Set ℂ), conj x ∈ ({0, 1} : Set ℂ) := by simp
  have hc' := hc.mem_constructibleClosure hstar
  have hd' := hd.mem_constructibleClosure hstar
  have hcd : dist c' d' ∈ constructibleClosure (Subfield.closure ({0, 1} : Set ℝ)) ℝ := by
    rw [dist_eq_norm_sub]
    rw [← re_im_image_01]
    apply norm_mem_constructibleClosure
    exact sub_mem hc' hd'
  rw [Subfield.closrue_01] at hcd
  have hquad : (minpoly (⊥ : Subfield ℝ) (dist c' d')).natDegree.isPowerOfTwo :=
    isPowerOfTwo_natDegree_minpoly_of_mem_constructibleClosure hcd
  have hdist : dist c' d' ^ 3 = 2 := by
    simp_rw [c', d', Isometry.dist_eq (e.isometry), dist_homothety_homothety]
    rw [mul_pow, hdist, dist_eq_norm_vsub', norm_inv, norm_norm, inv_pow]
    rw [mul_comm 2, inv_mul_cancel_left₀ (by simpa using h.symm)]
  let p : Polynomial (⊥ : Subfield ℝ) := Polynomial.X ^ 3 - 2
  have hp : Irreducible p := by
    suffices Irreducible (Polynomial.mapEquiv ratEquivBot
        (Polynomial.X ^ 3 - 2)) by
      convert this
      simp [p]
    exact Irreducible.map _ irreducible_cube_2
  have hwp : minpoly (⊥ : Subfield ℝ) (dist c' d') ∣ p := by
    apply minpoly.dvd
    simp [p, hdist, map_ofNat]
  have hminpoly : (minpoly (⊥ : Subfield ℝ) (dist c' d')).natDegree = 3 := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Irreducible.dvd_iff hp] at hwp
    rw [← Polynomial.degree_eq_degree_of_associated <| Or.resolve_left hwp (minpoly.not_isUnit _ _)]
    unfold p
    compute_degree!
  rw [hminpoly] at hquad
  contrapose! hquad
  decide

end EuclideanGeometry
