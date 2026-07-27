module

public import Compass.ConstructiblePoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

public section

attribute [instance] FiniteDimensional.of_fact_finrank_eq_two
attribute [instance] Complex.finrank_real_complex_fact

open EuclideanGeometry

theorem AffineIsometryEquiv.trans_apply {𝕜 : Type*} {V : Type*} {V₂ : Type*} {V₃ : Type*}
    {P : Type*} {P₂ : Type*} {P₃ : Type*}
    [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    [PseudoMetricSpace P] [NormedAddTorsor V P] [SeminormedAddCommGroup V₂]
    [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
    [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃]
    [NormedAddTorsor V₃ P₃] (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) (x : P) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

noncomputable def basis2D {v : V} (h : ‖v‖ = 1) :=
  (Orthonormal.exists_orthonormalBasis_extension_of_card_eq (v := ![v, 0]) (𝕜 := ℝ) (s := {0})
    (by simp [hrank.out]) (by simpa using h)).choose

theorem basis2D_self {v : V} (h : ‖v‖ = 1) : basis2D h 0 = v :=
  (Orthonormal.exists_orthonormalBasis_extension_of_card_eq (v := ![v, 0]) (𝕜 := ℝ) (s := {0})
    (by simp [hrank.out]) (by simpa using h)).choose_spec 0 (by simp)

noncomputable def equivComplex (a b : P) (hab : dist a b = 1) : P ≃ᵃⁱ[ℝ] ℂ :=
  haveI hv : ‖b -ᵥ a‖ = 1 := by simpa [dist_eq_norm_vsub'] using hab
  (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
  ((basis2D hv).equiv Complex.orthonormalBasisOneI (Equiv.refl _)).toAffineIsometryEquiv

@[simp]
theorem equivComplex_left {a b : P} (hab : dist a b = 1) : equivComplex a b hab a = 0 := by
  simp [equivComplex]

@[simp]
theorem equivComplex_right {a b : P} (hab : dist a b = 1) : equivComplex a b hab b = 1 := by
  have hv : ‖b -ᵥ a‖ = 1 := by simpa [dist_eq_norm_vsub'] using hab
  simp_rw [equivComplex, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  conv_lhs =>
    right
    rw [← basis2D_self hv]
  rw [OrthonormalBasis.equiv_apply_basis]
  simp

noncomputable def equivComplexScaled (a b : P) (hab : a ≠ b) : P ≃ᵃ[ℝ] ℂ :=
    (AffineEquiv.homothetyUnitsMulHom a (Units.mk0 (dist a b)⁻¹ (by simpa using hab))).trans
    (equivComplex a ((dist a b)⁻¹ • (b -ᵥ a) +ᵥ a) ?_).toAffineEquiv
  where finally
    have : ‖b -ᵥ a‖ ≠ 0 := by simpa using hab.symm
    simp [dist_eq_norm_vsub', norm_smul, this]

@[simp]
theorem equivComplexScaled_left {a b : P} (hab : a ≠ b) :
    equivComplexScaled a b hab a = 0 := by
  simp [equivComplexScaled]

@[simp]
theorem equivComplexScaled_right {a b : P} (hab : a ≠ b) :
    equivComplexScaled a b hab b = 1 := by
  simp only [equivComplexScaled, AffineEquiv.trans_apply,
    AffineEquiv.coe_homothetyUnitsMulHom_apply, Units.val_mk0,
    AffineIsometryEquiv.coe_toAffineEquiv]
  rw [AffineMap.homothety_apply]
  apply equivComplex_right

theorem equivComplexScaled_apply {a b c : P} (hab : a ≠ b) :
    equivComplexScaled a b hab c = equivComplex a ((dist a b)⁻¹ • (b -ᵥ a) +ᵥ a)
    (by
      have : ‖b -ᵥ a‖ ≠ 0 := by simpa using hab.symm
      simp [dist_eq_norm_vsub', norm_smul, this])
    (AffineMap.homothety a (dist a b)⁻¹ c) := by
  simp [equivComplexScaled]

theorem angle_equivComplexScaled {a b : P} (hab : a ≠ b) (p q r : P) :
    ∠ (equivComplexScaled a b hab p) (equivComplexScaled a b hab q) (equivComplexScaled a b hab r) =
    ∠ p q r := by
  simp only [equivComplexScaled, AffineEquiv.trans_apply,
    AffineEquiv.coe_homothetyUnitsMulHom_apply, Units.val_mk0,
    AffineIsometryEquiv.coe_toAffineEquiv]
  simp_rw [← AffineIsometryEquiv.coe_toAffineIsometry]
  rw [AffineIsometry.angle_map, EuclideanGeometry.angle_homothety _ _ _ _ (by simpa using hab)]

theorem constructiblePoint_iff_equivComplexScaled {a b : P} (hab : a ≠ b)
    {initial : Set P} {p : P} :
    ConstructiblePoint (equivComplexScaled a b hab '' initial) (equivComplexScaled a b hab p) ↔
    ConstructiblePoint initial p := by
  unfold equivComplexScaled
  rw [AffineEquiv.coe_trans, Set.image_comp, Function.comp_apply]
  rw [AffineIsometryEquiv.coe_toAffineEquiv, AffineEquiv.coe_homothetyUnitsMulHom_apply]
  rw [← ConstructiblePoint.map_iff, constructiblePoint_iff_homothety _ (Units.ne_zero _)]
