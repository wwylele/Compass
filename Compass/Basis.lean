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

omit hrank in
theorem orthonormal_singleton {v : V} (h : ‖v‖ = 1) :
    Orthonormal ℝ ((↑) : ({v} : Finset V) → V) := by
  rw [orthonormal_subsingleton_iff]
  intro i
  have hi := i.prop
  rw [Finset.mem_singleton] at hi
  rw [← hi] at h
  exact h

theorem orthBasis2D_exist {v : V} (h : ‖v‖ = 1) :
    ∃ (u : Finset V) (b : OrthonormalBasis u ℝ V), {v} ⊆ u ∧ ⇑b = Subtype.val :=
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  Orthonormal.exists_orthonormalBasis_extension (orthonormal_singleton h)

noncomputable def b2u (v : V) (h : ‖v‖ = 1) : Finset V := (orthBasis2D_exist h).choose
noncomputable def basis2D (v : V) (h : ‖v‖ = 1) :
  OrthonormalBasis (b2u v h) ℝ V := (orthBasis2D_exist h).choose_spec.choose

theorem b2uspec {v : V} (h : ‖v‖ = 1) : {v} ⊆ b2u v h :=
    (orthBasis2D_exist h).choose_spec.choose_spec.1

theorem b2umem {v : V} (h : ‖v‖ = 1) : v ∈ b2u v h := by
  simpa using b2uspec h

theorem basis2Dspec {v : V} (h : ‖v‖ = 1) : ⇑(basis2D v h) = Subtype.val :=
    (orthBasis2D_exist h).choose_spec.choose_spec.2

theorem basis2D_self {v : V} (h : ‖v‖ = 1) : basis2D v h ⟨v, b2umem h⟩ = v := by
  simp [basis2Dspec]

theorem b2ufilter [DecidableEq V] {v : V} (h : ‖v‖ = 1) : ((b2u v h).filter (· ≠ v)).card = 1 := by
  have h1 : ((b2u v h).filter (¬ · ≠ v)).card = 1 := by
    rw [Finset.card_eq_one]
    use v
    grind [b2uspec]
  suffices ((b2u v h).filter (· ≠ v)).card +
    ((b2u v h).filter (¬ · ≠ v)).card = 2 by
    rw [h1] at this
    grind
  rw [Finset.card_filter_add_card_filter_not]
  rw [← Module.finrank_eq_card_finset_basis (basis2D v h).toBasis]
  exact hrank.out

noncomputable def b2uj [DecidableEq V] (v : V) (h : ‖v‖ = 1) :=
    (Finset.card_eq_one.mp (b2ufilter h)).choose

theorem b2uj_spec [DecidableEq V] {v : V} (h : ‖v‖ = 1) :
    (b2u v h).filter (· ≠ v) = {b2uj v h} :=
    (Finset.card_eq_one.mp (b2ufilter h)).choose_spec

theorem b2uj_mem [DecidableEq V] {v : V} (h : ‖v‖ = 1) :
    b2uj v h ∈ b2u v h := by
  have h := (b2uj_spec h).ge
  grind

theorem b2uj_ne [DecidableEq V] {v : V} (h : ‖v‖ = 1) :
    b2uj v h ≠ v := by
  have h := (b2uj_spec h).ge
  grind

open Classical in
noncomputable def b2uEquiv (v : V) (h : ‖v‖ = 1) : b2u v h ≃ Fin 2 := {
    toFun i := if i = v then 0 else 1
    invFun := ![⟨v, b2umem h⟩, ⟨b2uj v h, b2uj_mem h⟩]
    left_inv i := by
      by_cases hi : i = v
      · ext
        simp [hi]
      · ext
        suffices b2uj v h = i by simpa [hi]
        symm
        suffices i.val ∈ ({b2uj v h} : Finset _) by simpa
        rw [← b2uj_spec]
        simp [hi]
    right_inv i := by
      fin_cases i
      · simp
      · simpa using b2uj_ne h
  }

noncomputable def equivComplex (a b : P) (hab : dist a b = 1) :
  P ≃ᵃⁱ[ℝ] ℂ :=
  haveI hv : ‖b -ᵥ a‖ = 1 := by simpa [dist_eq_norm_vsub'] using hab
  (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
  ((basis2D _ hv).equiv Complex.orthonormalBasisOneI (b2uEquiv _ hv)).toAffineIsometryEquiv

theorem equivComplex_left {a b : P} (hab : dist a b = 1) :
    (equivComplex a b hab) a = 0 := by
  simp [equivComplex]

theorem equivComplex_right {a b : P} (hab : dist a b = 1) :
    (equivComplex a b hab) b = 1 := by
  have hv : ‖b -ᵥ a‖ = 1 := by simpa [dist_eq_norm_vsub'] using hab
  simp_rw [equivComplex, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
      LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  conv_lhs =>
    right
    rw [← basis2D_self hv]
  rw [OrthonormalBasis.equiv_apply_basis]
  simp [b2uEquiv]
