module

public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

import Mathlib.Algebra.Module.SpanRank

/-!

# Constructible Points

This file defines three predicates for constructibility using straightedge and compass
* `EuclideanGeometry.ConstructiblePoint`
* `EuclideanGeometry.ConstructibleLine`
* `EuclideanGeometry.ConstructibleCircle`

All these predicates have a paramter `initial : Set P`, the set of initial points one
can start drawing lines and circles with. Our definition of constructibility does not
permit arbitrarily choosing a free point on the plane, on a line, or on a circle. nly
initial points and intersections are considered constructible points.

-/


public section

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

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
| centerRadius (o : Sphere P) (r : P) (hcenter : ConstructiblePoint initial o.center)
    (hradius : ConstructiblePoint initial r) (h : r ∈ o) :
    ConstructibleCircle initial o

end

variable {V₂ P₂ : Type*}
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [hrank₂ : Fact (Module.finrank ℝ V₂ = 2)]
  [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

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
    simpa [← Sphere.mem_coe'] using hpo
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ h p hpo₁ hpo₂ => by
    apply ConstructiblePoint.twoCircles (Sphere.mk (f o₁.center) o₁.radius)
      (Sphere.mk (f o₂.center) o₂.radius) (ho₁.map f) (ho₂.map f)
      (by simpa [Sphere.ext_iff] using h) (f p)
    · simpa [← Sphere.mem_coe'] using hpo₁
    · simpa [← Sphere.mem_coe'] using hpo₂

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
  | ConstructibleCircle.centerRadius o r hcenter hradius h => by
    apply ConstructibleCircle.centerRadius (Sphere.mk (f o.center) o.radius) (f r)
      (hcenter.map f) (hradius.map f)
    simpa [← Sphere.mem_coe'] using h

end

theorem ConstructiblePoint.map_iff (f : P ≃ᵃⁱ[ℝ] P₂) {initial : Set P} {p : P} :
    ConstructiblePoint initial p ↔ ConstructiblePoint (f '' initial) (f p) where
  mp h := ConstructiblePoint.map f.toAffineIsometry h
  mpr h := by
    convert ConstructiblePoint.map f.symm.toAffineIsometry h
    · rw [Set.image_image]
      simp
    · simp

mutual
theorem ConstructiblePoint.mono {i1 i2 : Set P} (hi : i1 ⊆ i2) {p : P}
    (h : ConstructiblePoint i1 p) :
    ConstructiblePoint i2 p :=
  match h with
  | ConstructiblePoint.given p h =>
    ConstructiblePoint.given p (Set.mem_of_mem_of_subset h hi)
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ h p hpl₁ hpl₂ =>
    ConstructiblePoint.twoLines l₁ l₂ (hl₁.mono hi) (hl₂.mono hi) h p hpl₁ hpl₂
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo =>
    ConstructiblePoint.lineCircle l o (hl.mono hi) (ho.mono hi) p hpl hpo
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ h p hpo₁ hpo₂ =>
    ConstructiblePoint.twoCircles o₁ o₂ (ho₁.mono hi) (ho₂.mono hi) h p hpo₁ hpo₂

theorem ConstructibleLine.mono {i1 i2 : Set P} (hi : i1 ⊆ i2) {l : AffineSubspace ℝ P}
    (h : ConstructibleLine i1 l) :
    ConstructibleLine i2 l :=
  match h with
  | ConstructibleLine.twoPoints p₁ p₂ hp₁ hp₂ h l hp₁l hp₂l hrank =>
    ConstructibleLine.twoPoints p₁ p₂ (hp₁.mono hi) (hp₂.mono hi) h l hp₁l hp₂l hrank

theorem ConstructibleCircle.mono {i1 i2 : Set P} (hi : i1 ⊆ i2) {o : Sphere P}
    (h : ConstructibleCircle i1 o) :
    ConstructibleCircle i2 o :=
  match h with
  | ConstructibleCircle.centerRadius o r hcenter hradius h =>
    ConstructibleCircle.centerRadius o r (hcenter.mono hi) (hradius.mono hi) h
end

mutual
theorem ConstructiblePoint.of_insert {initial : Set P} {q p : P} (hq : ConstructiblePoint initial q)
    (h : ConstructiblePoint (initial.insert q) p) :
    ConstructiblePoint initial p :=
  match h with
  | ConstructiblePoint.given p h => by
    rcases Set.mem_insert_iff.mp h with h | h
    · simpa [h] using hq
    exact ConstructiblePoint.given p h
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ h p hpl₁ hpl₂ =>
    ConstructiblePoint.twoLines l₁ l₂ (hl₁.of_insert hq) (hl₂.of_insert hq) h p hpl₁ hpl₂
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo =>
    ConstructiblePoint.lineCircle l o (hl.of_insert hq) (ho.of_insert hq) p hpl hpo
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ h p hpo₁ hpo₂ =>
    ConstructiblePoint.twoCircles o₁ o₂ (ho₁.of_insert hq) (ho₂.of_insert hq) h p hpo₁ hpo₂

theorem ConstructibleLine.of_insert {initial : Set P} {q : P} (hq : ConstructiblePoint initial q)
    {l : AffineSubspace ℝ P} (h : ConstructibleLine (initial.insert q) l) :
    ConstructibleLine initial l :=
  match h with
  | ConstructibleLine.twoPoints p₁ p₂ hp₁ hp₂ h l hp₁l hp₂l hrank =>
    ConstructibleLine.twoPoints p₁ p₂
      (ConstructiblePoint.of_insert hq hp₁) (ConstructiblePoint.of_insert hq hp₂)
      h l hp₁l hp₂l hrank

theorem ConstructibleCircle.of_insert {initial : Set P} {q : P} (hq : ConstructiblePoint initial q)
    {o : Sphere P} (h : ConstructibleCircle (initial.insert q) o) :
    ConstructibleCircle initial o :=
  match h with
  | ConstructibleCircle.centerRadius o r hcenter hradius h =>
    ConstructibleCircle.centerRadius o r
      (ConstructiblePoint.of_insert hq hcenter) (ConstructiblePoint.of_insert hq hradius) h
end

theorem constructiblePoint_insert {initial : Set P} {p : P} (h : ConstructiblePoint initial p) :
    ConstructiblePoint (initial.insert p) = ConstructiblePoint initial := by
  ext q
  constructor
  · apply ConstructiblePoint.of_insert h
  · intro h
    apply h.mono (Set.subset_insert _ _)

open AffineMap

omit hrank in
theorem homothety_mem_sphere (c : P) (r : ℝ) {p : P} {o : Sphere P} (h : p ∈ o) :
    homothety c r p ∈ Sphere.mk (homothety c r o.center) (|r| * o.radius) := by
  rw [mem_sphere, dist_eq_norm_vsub] at ⊢ h
  simp only
  rw [← linearMap_vsub, homothety_linear]
  simp [norm_smul, h]

mutual

theorem ConstructiblePoint.map_homothety (c : P) {r : ℝ} (hr : r ≠ 0) {initial : Set P} {p : P}
    (h : ConstructiblePoint initial p) :
    ConstructiblePoint (homothety c r '' initial) (homothety c r p) :=
  match h with
  | ConstructiblePoint.given p h => by
    apply ConstructiblePoint.given
    rw [Set.mem_image]
    use p
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ h p hpl₁ hpl₂ => by
    refine ConstructiblePoint.twoLines (l₁.map (homothety c r)) (l₂.map (homothety c r))
      (hl₁.map_homothety c hr) (hl₂.map_homothety c hr) ?_ (homothety c r p)
      (AffineSubspace.mem_map_of_mem _ hpl₁) (AffineSubspace.mem_map_of_mem _ hpl₂)
    contrapose h
    ext x
    rw [SetLike.ext_iff] at h
    specialize h (homothety c r x)
    rw [AffineSubspace.mem_map_iff_mem_of_injective (homothety_injective c hr),
      AffineSubspace.mem_map_iff_mem_of_injective (homothety_injective c hr)] at h
    exact h
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo => by
    apply ConstructiblePoint.lineCircle (l.map (homothety c r))
      (Sphere.mk (homothety c r o.center) (|r| * o.radius))
      (hl.map_homothety c hr) (ho.map_homothety c hr) (homothety c r p)
    · exact AffineSubspace.mem_map_of_mem _ hpl
    · exact homothety_mem_sphere c r hpo
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ h p hpo₁ hpo₂ => by
    refine ConstructiblePoint.twoCircles (Sphere.mk (homothety c r o₁.center) (|r| * o₁.radius))
      (Sphere.mk (homothety c r o₂.center) (|r| * o₂.radius)) (ho₁.map_homothety c hr)
      (ho₂.map_homothety c hr) ?_ (homothety c r p) ?_ ?_
    · contrapose h
      rw [Sphere.ext_iff]
      simpa [(homothety_injective c hr).eq_iff, hr] using h
    · exact homothety_mem_sphere c r hpo₁
    · exact homothety_mem_sphere c r hpo₂

theorem ConstructibleLine.map_homothety (c : P) {r : ℝ} (hr : r ≠ 0) {initial : Set P}
    {l : AffineSubspace ℝ P} (h : ConstructibleLine initial l) :
    ConstructibleLine (homothety c r '' initial) (l.map (homothety c r)) :=
  match h with
  | ConstructibleLine.twoPoints p₁ p₂ hp₁ hp₂ h l hp₁l hp₂l hrank => by
    apply ConstructibleLine.twoPoints (homothety c r p₁) (homothety c r p₂)
      (hp₁.map_homothety c hr) (hp₂.map_homothety c hr) ((homothety_injective c hr).ne h)
      (l.map (homothety c r)) (AffineSubspace.mem_map_of_mem _ hp₁l)
      (AffineSubspace.mem_map_of_mem _ hp₂l)
    rw [AffineSubspace.map_direction]
    rw [Module.finrank_eq_spanFinrank_of_free, Submodule.spanFinrank_top] at hrank
    rw [Module.finrank_eq_spanFinrank_of_free, Submodule.spanFinrank_top,
      Submodule.spanFinrank_map_eq_of_injective _
      ((AffineMap.linear_injective_iff _).mpr (homothety_injective c hr))]
    exact hrank

theorem ConstructibleCircle.map_homothety (c : P) {r : ℝ} (hr : r ≠ 0) {initial : Set P}
    {o : Sphere P} (h : ConstructibleCircle initial o) :
    ConstructibleCircle (homothety c r '' initial)
    (Sphere.mk (homothety c r o.center) (|r| * o.radius)) :=
  match h with
  | ConstructibleCircle.centerRadius o radius hcenter hradius h => by
    apply ConstructibleCircle.centerRadius (Sphere.mk (homothety c r o.center) (|r| * o.radius))
      (homothety c r radius)
      (hcenter.map_homothety c hr) (hradius.map_homothety c hr)
    exact homothety_mem_sphere c r h

end

end EuclideanGeometry
