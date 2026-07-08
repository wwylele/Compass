import Mathlib

/-!
-/


namespace EuclideanGeometry

variable {V V₂ P P₂ : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [Fact (Module.finrank ℝ V₂ = 2)]
  [MetricSpace P] [NormedAddTorsor V P]
  [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

mutual

inductive ConstructiblePoint [Fact (Module.finrank ℝ V = 2)] (initial : Set P) : P → Prop
| given (p : P) (h : p ∈ initial) : ConstructiblePoint initial p
| twoLines (l₁ l₂ : AffineSubspace ℝ P)
    (hl₁ : ConstructibleLine initial l₁) (hl₂ : ConstructibleLine initial l₂)
    (h : l₁ ≠ l₂) (p : P) (hpl₁ : p ∈ l₁) (hpl₂ : p ∈ l₂) :
    ConstructiblePoint initial p
| lineCircle (l : AffineSubspace ℝ P) (o : Sphere P)
    (hl : ConstructibleLine initial l) (ho : ConstructibleCircle initial o)
    (p : P) (hpl : p ∈ l) (hpo : p ∈ o) :
    ConstructiblePoint initial p
| twoCircles (o₁ o₂ : Sphere P)
    (ho₁ : ConstructibleCircle initial o₁) (ho₂ : ConstructibleCircle initial o₂)
    (h : o₁ ≠ o₂) (p : P) (hpo₁ : p ∈ o₁) (hpo₂ : p ∈ o₂) :
    ConstructiblePoint initial p

inductive ConstructibleLine [Fact (Module.finrank ℝ V = 2)] (initial : Set P) :
    AffineSubspace ℝ P → Prop
| twoPoints (p₁ p₂ : P) (hp₁ : ConstructiblePoint initial p₁) (hp₂ : ConstructiblePoint initial p₂)
    (h : p₁ ≠ p₂) (l : AffineSubspace ℝ P) (hp₁l : p₁ ∈ l) (hp₂l : p₂ ∈ l)
    (hrank : Module.finrank ℝ l.direction = 1) :
    ConstructibleLine initial l

inductive ConstructibleCircle [Fact (Module.finrank ℝ V = 2)] (initial : Set P) :
    Sphere P → Prop
| centerRadius (o : Sphere P) (radius : P) (hcenter : ConstructiblePoint initial o.center)
    (hradius : ConstructiblePoint initial radius) (horadius : o.radius = dist o.center radius) :
    ConstructibleCircle initial o

end

mutual

theorem ConstructiblePoint.map (f : P →ᵃⁱ[ℝ] P₂) {initial : Set P} {p : P}
    (h : ConstructiblePoint initial p) :
    ConstructiblePoint (f '' initial) (f p) :=
  match h with
  | ConstructiblePoint.given p h => by
    apply ConstructiblePoint.given
    simpa using h
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ h p hpl₁ hpl₂ => by
    refine ConstructiblePoint.twoLines (l₁.map f.toAffineMap) (l₂.map f.toAffineMap)
      (hl₁.map f) (hl₂.map f) ?_ (f p) (by simpa using hpl₁) (by simpa using hpl₂)
    contrapose h
    ext x
    rw [SetLike.ext_iff] at h
    simpa using h (f x)
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo => by
    apply ConstructiblePoint.lineCircle (l.map f.toAffineMap) (Sphere.mk (f o.center) o.radius)
      (hl.map f) (ho.map f) (f p) (by simpa using hpl)
    simpa [← EuclideanGeometry.Sphere.mem_coe'] using hpo
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ h p hpo₁ hpo₂ => by
    apply ConstructiblePoint.twoCircles (Sphere.mk (f o₁.center) o₁.radius)
      (Sphere.mk (f o₂.center) o₂.radius) (ho₁.map f) (ho₂.map f)
      (by simpa [Sphere.ext_iff] using h) (f p)
    · simpa [← EuclideanGeometry.Sphere.mem_coe'] using hpo₁
    · simpa [← EuclideanGeometry.Sphere.mem_coe'] using hpo₂

theorem ConstructibleLine.map (f : P →ᵃⁱ[ℝ] P₂) {initial : Set P} {l : AffineSubspace ℝ P}
    (h : ConstructibleLine initial l) :
    ConstructibleLine (f '' initial) (l.map f.toAffineMap) :=
  match h with
  | ConstructibleLine.twoPoints p₁ p₂ hp₁ hp₂ h l hp₁l hp₂l hrank => by
    apply ConstructibleLine.twoPoints (f p₁) (f p₂) (hp₁.map f) (hp₂.map f) (f.injective.ne h)
      (l.map f.toAffineMap) (by simpa using hp₁l) (by simpa using hp₂l)
    rw [AffineSubspace.map_direction]
    rw [Module.finrank_eq_spanFinrank_of_free, Submodule.spanFinrank_top] at hrank
    rw [Module.finrank_eq_spanFinrank_of_free, Submodule.spanFinrank_top,
      Submodule.spanFinrank_map_eq_of_injective _
      ((AffineMap.linear_injective_iff _).mpr f.injective)]
    exact hrank

theorem ConstructibleCircle.map (f : P →ᵃⁱ[ℝ] P₂) {initial : Set P} {o : Sphere P}
    (h : ConstructibleCircle initial o) :
    ConstructibleCircle (f '' initial) (Sphere.mk (f o.center) o.radius) :=
  match h with
  | ConstructibleCircle.centerRadius o radius hcenter hradius horadius => by
    apply ConstructibleCircle.centerRadius (Sphere.mk (f o.center) o.radius) (f radius)
      (hcenter.map f) (hradius.map f)
    simpa using horadius

end

theorem not_exist_angle_trisection :
    ∃ p₁ p₂ p₃ : P, ∀ q₁ q₂ q₃ : P,
    ConstructiblePoint {p₁, p₂, p₃} q₁ →
    ConstructiblePoint {p₁, p₂, p₃} q₂ →
    ConstructiblePoint {p₁, p₂, p₃} q₃ →
    3 * ∠ q₁ q₂ q₃ ≠ ∠ p₁ p₂ p₃ := by
  sorry

end EuclideanGeometry
