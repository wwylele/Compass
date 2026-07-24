module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

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
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  (Orthonormal.exists_orthonormalBasis_extension_of_card_eq (v := ![v, 0]) (𝕜 := ℝ) (s := {0})
    (by simp [hrank.out]) (by simpa using h)).choose

theorem basis2D_self {v : V} (h : ‖v‖ = 1) : basis2D h 0 = v :=
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  (Orthonormal.exists_orthonormalBasis_extension_of_card_eq (v := ![v, 0]) (𝕜 := ℝ) (s := {0})
    (by simp [hrank.out]) (by simpa using h)).choose_spec 0 (by simp)

noncomputable def equivComplex (a b : P) (hab : dist a b = 1) : P ≃ᵃⁱ[ℝ] ℂ :=
  haveI hv : ‖b -ᵥ a‖ = 1 := by simpa [dist_eq_norm_vsub'] using hab
  (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
  ((basis2D hv).equiv Complex.orthonormalBasisOneI (Equiv.refl _)).toAffineIsometryEquiv

theorem equivComplex_left {a b : P} (hab : dist a b = 1) : equivComplex a b hab a = 0 := by
  simp [equivComplex]

theorem equivComplex_right {a b : P} (hab : dist a b = 1) : equivComplex a b hab b = 1 := by
  have hv : ‖b -ᵥ a‖ = 1 := by simpa [dist_eq_norm_vsub'] using hab
  simp_rw [equivComplex, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  conv_lhs =>
    right
    rw [← basis2D_self hv]
  rw [OrthonormalBasis.equiv_apply_basis]
  simp
