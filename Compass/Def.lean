module

public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

import Mathlib.Algebra.Module.SpanRank
import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

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

open scoped Real

nonrec
theorem ConstructiblePoint.midpoint {initial : Set P} {a b : P} (ha : ConstructiblePoint initial a)
    (hb : ConstructiblePoint initial b) :
    ConstructiblePoint initial (midpoint ℝ a b) := by
  have : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree ℝ V
  by_cases! hab : a = b
  · simpa [hab, midpoint_self] using hb
  have ho1 : ConstructibleCircle initial ⟨a, dist a b⟩ := by
    apply ConstructibleCircle.centerRadius _ b ha hb
    rw [dist_comm, mem_sphere]
  have ho2 : ConstructibleCircle initial ⟨b, dist a b⟩ := by
    apply ConstructibleCircle.centerRadius _ a hb ha
    rw [mem_sphere]
  have hoo : (⟨a, dist a b⟩ : Sphere P) ≠ ⟨b, dist a b⟩ := by simp [hab]
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  let : Module.Oriented ℝ V _ :=
    ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ V hrank.out)⟩
  have hnorm : ‖√3 / 2‖ ^ 2 + ‖(2⁻¹ : ℝ)‖ ^ 2 = 1 := by
    rw [Real.norm_eq_abs, ← abs_pow, div_pow]
    norm_num
  apply ConstructiblePoint.twoLines line[ℝ, a, b] (AffineSubspace.perpBisector a b)
  · apply ConstructibleLine.twoPoints a b ha hb hab
    · apply left_mem_affineSpan_pair
    · apply right_mem_affineSpan_pair
    · rw [direction_affineSpan, vectorSpan_pair]
      apply finrank_span_singleton
      simpa using hab
  · apply ConstructibleLine.twoPoints ((√3 / 2) • o.rotation (π / 2 : ℝ) (b -ᵥ a) +ᵥ midpoint ℝ a b)
        (-(√3 / 2) • o.rotation (π / 2 : ℝ) (b -ᵥ a) +ᵥ midpoint ℝ a b)
    · apply ConstructiblePoint.twoCircles _ _ ho1 ho2 hoo
      · rw [mem_sphere]
        simp only
        rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
        rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a b) _).mpr ?_]
        · rw [← sq, ← sq]
          rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
            mul_pow, (o.rotation ↑(π / 2)).norm_map, left_vsub_midpoint, norm_smul, mul_pow,
            ← neg_vsub_eq_vsub_rev b a, norm_neg, ← add_mul, invOf_eq_inv]
          rw [hnorm]
          simp
        · apply angle_eq_pi_div_two_of_oangle_eq_pi_div_two
          rw [EuclideanGeometry.oangle, vadd_vsub, left_vsub_midpoint, ← neg_vsub_eq_vsub_rev b a,
            smul_neg, o.oangle_neg_right (by simpa using hab.symm) (by simpa using hab.symm),
            o.oangle_smul_left_of_pos _ _ (by simp),
            o.oangle_smul_right_of_pos _ _ (by simp),
            o.oangle_rotation_self_left (by simpa using hab.symm)]
          rw [← Real.Angle.coe_neg, ← Real.Angle.coe_add]
          congr
          ring
      · rw [mem_sphere]
        simp only
        rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
        rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a b) _).mpr ?_]
        · rw [← sq, ← sq]
          rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
            mul_pow, (o.rotation ↑(π / 2)).norm_map, right_vsub_midpoint, norm_smul, mul_pow,
            ← neg_vsub_eq_vsub_rev b a, norm_neg, ← add_mul, invOf_eq_inv]
          rw [hnorm]
          simp
        · apply angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
          rw [EuclideanGeometry.oangle, vadd_vsub, right_vsub_midpoint,
            o.oangle_smul_left_of_pos _ _ (by simp),
            o.oangle_smul_right_of_pos _ _ (by simp),
            o.oangle_rotation_self_left (by simpa using hab.symm)]
          rw [neg_div, Real.Angle.coe_neg]
    · apply ConstructiblePoint.twoCircles _ _ ho1 ho2 hoo
      · rw [mem_sphere]
        simp only
        rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
        rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a b) _).mpr ?_]
        · rw [← sq, ← sq]
          rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
            mul_pow, (o.rotation ↑(π / 2)).norm_map, left_vsub_midpoint, norm_smul, mul_pow,
            ← neg_vsub_eq_vsub_rev b a, norm_neg, norm_neg, ← add_mul, invOf_eq_inv]
          rw [hnorm]
          simp
        · apply angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
          rw [EuclideanGeometry.oangle, vadd_vsub, left_vsub_midpoint,
            o.oangle_smul_left_of_neg _ _ (by simp),
            ← neg_vsub_eq_vsub_rev b a,
            smul_neg, ← neg_smul,
            o.oangle_smul_right_of_neg _ _ (by simp),
            o.oangle_neg_neg,
            o.oangle_rotation_self_left (by simpa using hab.symm)]
          rw [neg_div, Real.Angle.coe_neg]
      · rw [mem_sphere]
        simp only
        rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
        rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a b) _).mpr ?_]
        · rw [← sq, ← sq]
          rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
            mul_pow, (o.rotation ↑(π / 2)).norm_map, right_vsub_midpoint, norm_smul, mul_pow,
            ← neg_vsub_eq_vsub_rev b a, norm_neg, norm_neg, ← add_mul, invOf_eq_inv]
          rw [hnorm]
          simp
        · apply angle_eq_pi_div_two_of_oangle_eq_pi_div_two
          rw [EuclideanGeometry.oangle, vadd_vsub, right_vsub_midpoint,
            o.oangle_smul_left_of_neg _ _ (by simp),
            o.oangle_smul_right_of_pos _ _ (by simp),
            o.neg_rotation,
            o.oangle_rotation_self_left (by simpa using hab.symm)]
          rw [neg_add, Real.Angle.neg_coe_pi, ← Real.Angle.coe_neg, ← Real.Angle.coe_add]
          congr
          ring
    · rw [ne_eq, vadd_right_cancel_iff, neg_smul, self_eq_neg]
      simpa using hab.symm
    · apply AffineSubspace.vadd_mem_of_mem_direction
      · apply Submodule.smul_mem
        rw [AffineSubspace.direction_perpBisector, Submodule.mem_orthogonal]
        intro u hu
        obtain ⟨v, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [real_inner_smul_left, Orientation.inner_rotation_pi_div_two_right, mul_zero]
      · exact AffineSubspace.midpoint_mem_perpBisector a b
    · apply AffineSubspace.vadd_mem_of_mem_direction
      · apply Submodule.smul_mem
        rw [AffineSubspace.direction_perpBisector, Submodule.mem_orthogonal]
        intro u hu
        obtain ⟨v, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [real_inner_smul_left, Orientation.inner_rotation_pi_div_two_right, mul_zero]
      · exact AffineSubspace.midpoint_mem_perpBisector a b
    · rw [AffineSubspace.direction_perpBisector]
      apply Submodule.finrank_orthogonal_span_singleton
      simpa using hab.symm
  · intro heq
    have heq := congr(AffineSubspace.direction $heq)
    rw [direction_affineSpan, vectorSpan_pair_rev, AffineSubspace.direction_perpBisector] at heq
    have : ℝ ∙ (b -ᵥ a) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
      rw [← inner_self_eq_zero (𝕜 := ℝ) (x := x)]
      apply Submodule.inner_left_of_mem_orthogonal hx
      simpa [← heq] using hx
    absurd this
    simpa using hab.symm
  · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    use ⅟2
    rfl
  · exact AffineSubspace.midpoint_mem_perpBisector a b

end EuclideanGeometry
