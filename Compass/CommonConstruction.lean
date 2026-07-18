module

public import Compass.ConstructiblePoint

import Mathlib.Algebra.Module.SpanRank
import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!

# Common Geometric Constructions

This file shows the constructibility of common geometric objects

-/


public section

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

open scoped Real

theorem ConstructiblePoint.perpBisector {initial : Set P} {a b : P}
    (ha : ConstructiblePoint initial a) (hb : ConstructiblePoint initial b) (hab : a ≠ b) :
    ConstructibleLine initial (AffineSubspace.perpBisector a b) := by
  have : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree ℝ V
  have ho1 : ConstructibleCircle initial ⟨a, dist a b⟩ := by
    apply ConstructibleCircle.centerRadius _ b ha hb
    rw [dist_comm, mem_sphere]
  have ho2 : ConstructibleCircle initial ⟨b, dist a b⟩ := by
    apply ConstructibleCircle.centerRadius _ a hb ha
    rw [mem_sphere]
  have hoo : (⟨a, dist a b⟩ : Sphere P) ≠ ⟨b, dist a b⟩ := by simp [hab]
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  let : Module.Oriented ℝ V _ :=
    ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ V hrank.out)⟩
  have hnorm : ‖√3 / 2‖ ^ 2 + ‖(2⁻¹ : ℝ)‖ ^ 2 = 1 := by
    rw [Real.norm_eq_abs, ← abs_pow, div_pow]
    norm_num
  apply ConstructibleLine.twoPoints ((√3 / 2) • o.rotation (π / 2 : ℝ) (b -ᵥ a) +ᵥ midpoint ℝ a b)
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

nonrec
theorem ConstructiblePoint.midpoint {initial : Set P} {a b : P} (ha : ConstructiblePoint initial a)
    (hb : ConstructiblePoint initial b) :
    ConstructiblePoint initial (midpoint ℝ a b) := by
  have : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree ℝ V
  by_cases! hab : a = b
  · simpa [hab, midpoint_self] using hb
  apply ConstructiblePoint.twoLines line[ℝ, a, b] (AffineSubspace.perpBisector a b)
  · apply ConstructibleLine.twoPoints a b ha hb hab
    · apply left_mem_affineSpan_pair
    · apply right_mem_affineSpan_pair
    · rw [direction_affineSpan, vectorSpan_pair]
      apply finrank_span_singleton
      simpa using hab
  · exact ConstructiblePoint.perpBisector ha hb hab
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

theorem ConstructibleLine.pair {initial : Set P} {p q : P}
    (hp : ConstructiblePoint initial p) (hq : ConstructiblePoint initial q) (hpq : p ≠ q) :
    ConstructibleLine initial line[ℝ, p, q] := by
  apply ConstructibleLine.twoPoints p q hp hq hpq
  · apply left_mem_affineSpan_pair
  · apply right_mem_affineSpan_pair
  · rw [direction_affineSpan, vectorSpan_pair]
    apply finrank_span_singleton
    simpa using hpq

theorem vsub_reflection_mem {𝕜 V P : Type*}
    [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [MetricSpace P]
    [NormedAddTorsor V P] (s : AffineSubspace 𝕜 P) [Nonempty ↥s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    p -ᵥ reflection s p ∈ s.directionᗮ := by
  rw [reflection_apply, vsub_vadd_eq_vsub_sub]
  rw [← Submodule.reflection_eq_self_iff, Submodule.reflection_orthogonal_apply]
  simp

theorem mem_reflection_plane
    {a b : P} {l : AffineSubspace ℝ P} (hl : Module.finrank ℝ l.direction = 1) [Nonempty l]
    [l.direction.HasOrthogonalProjection] (hbl : b ∉ l)
    (h : dist a b = dist a (reflection l b)) :
    a ∈ l := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have h2 : ‖a -ᵥ reflection l a + (reflection l a -ᵥ reflection l b)‖ ^ 2 =
      ‖a -ᵥ reflection l a + (reflection l a -ᵥ b)‖ ^ 2 := by
    congrm ?_ ^ 2
    simpa [dist_eq_norm_vsub] using h.symm
  simp_rw [← real_inner_self_eq_norm_sq, real_inner_add_add_self, add_assoc, add_right_inj] at h2
  simp_rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, ← dist_reflection] at h2
  rw [reflection_reflection, ← h, ← sub_eq_zero] at h2
  have h3 : inner ℝ (a -ᵥ (reflection l) a) (b -ᵥ (reflection l) b) = 0 := by
    simpa [← mul_sub, ← inner_sub_right] using h2
  have hrank : Module.finrank ℝ l.directionᗮ = 1 := by
    have := l.direction.finrank_add_finrank_orthogonal
    rw [hrank.out, hl] at this
    linear_combination this
  have haml := vsub_reflection_mem l a
  have hbml := vsub_reflection_mem l b
  have hbb : b ≠ (reflection l) b := by
    symm
    simpa [reflection_eq_self_iff] using hbl
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hrank hbml (by simpa using hbb),
    Submodule.mem_span_singleton] at haml
  obtain ⟨k, hk⟩ := haml
  symm at hk
  rw [hk, inner_smul_left] at h3
  have hk0 : k = 0 := by simpa [hbb] using h3
  rw [hk0, zero_smul, vsub_eq_zero_iff_eq] at hk
  exact (reflection_eq_self_iff _).mp hk.symm

theorem ConstructibleLine.ortho {initial : Set P} {l m : AffineSubspace ℝ P} {p : P}
    (hl : ConstructibleLine initial l) (hp : ConstructiblePoint initial p) (hpm : p ∈ m)
    (hlm : m.direction = l.directionᗮ) :
    ConstructibleLine initial m := by
  have : Nonempty m := ⟨p, hpm⟩
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have hm : Module.finrank ℝ m.direction = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (l.direction)
    rw [hl.finrank, hrank.out, ← hlm] at h
    linear_combination h
  classical
  have hl' := hl
  cases hl with | twoPoints a b ha hb hab l hal hbl hl
  have : FiniteDimensional ℝ l.direction := FiniteDimensional.of_finrank_pos (by simp [hl])
  have hlm' : l.direction.IsOrtho m.direction := by
    rw [Submodule.isOrtho_iff_le, hlm, Submodule.orthogonal_orthogonal]
  obtain ⟨q, hq⟩ := AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl (hl'.nonempty)
    ⟨p, hpm⟩
    ((Submodule.isCompl_iff_disjoint _ _ (by simp [hrank.out, hl, hm])).mpr hlm'.disjoint)
  let c := if a ∈ m then b else a
  let d := EuclideanGeometry.reflection m c
  have hc : ConstructiblePoint initial c := by
    unfold c
    split_ifs
    · exact hb
    · exact ha
  have hcl : c ∈ l := by
    unfold c
    split_ifs
    · exact hbl
    · exact hal
  have hcd : c ≠ d := by
    symm
    unfold d
    rw [ne_eq, (EuclideanGeometry.reflection_eq_self_iff c).not]
    unfold c
    split_ifs with ham
    · contrapose hab with hbm
      have halm : a ∈ (l ∩ m : Set P) := ⟨hal, ham⟩
      have hblm : b ∈ (l ∩ m : Set P) := ⟨hbl, hbm⟩
      rw [hq, Set.mem_singleton_iff] at halm hblm
      rw [halm, hblm]
    · exact ham
  have hcm : c ∉ m := by
    rw [← (EuclideanGeometry.reflection_eq_self_iff c).not]
    exact hcd.symm
  have hd : ConstructiblePoint initial d := by
    apply ConstructiblePoint.lineCircle l ⟨p, dist p c⟩ hl'
    · apply ConstructibleCircle.centerRadius _ c hp hc
      simp [mem_sphere']
    · simp_rw [d, EuclideanGeometry.reflection_apply']
      apply AffineSubspace.vadd_mem_of_mem_direction
      · convert EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal m c
        rw [hlm, Submodule.orthogonal_orthogonal]
      · convert EuclideanGeometry.orthogonalProjection_mem_orthogonal m c
        apply AffineSubspace.ext_of_direction_eq
        · rw [AffineSubspace.direction_mk', hlm, Submodule.orthogonal_orthogonal]
        · use c
          simp [hcl]
    · rw [mem_sphere']
      apply EuclideanGeometry.dist_reflection_eq_of_mem _ hpm
  convert hc.perpBisector hd hcd
  ext k
  simp_rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
  constructor
  · intro h
    symm
    apply EuclideanGeometry.dist_reflection_eq_of_mem _ h
  · intro h
    simp_rw [d] at h
    apply mem_reflection_plane hm hcm h

theorem ConstructibleLine.parallel {initial : Set P} {l m : AffineSubspace ℝ P} {p : P}
    (hl : ConstructibleLine initial l) (hp : ConstructiblePoint initial p) (hpm : p ∈ m)
    (hlm : m.direction = l.direction) :
    ConstructibleLine initial m := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have hortho : ConstructibleLine initial (AffineSubspace.mk' p l.directionᗮ) :=
    hl.ortho hp (AffineSubspace.self_mem_mk' p _) (by rw [AffineSubspace.direction_mk'])
  apply hortho.ortho hp hpm
  rw [AffineSubspace.direction_mk', Submodule.orthogonal_orthogonal, hlm]

theorem ConstructibleCircle.centerRadius' {initial : Set P} {o : Sphere P} {q r : P}
    (ho : ConstructiblePoint initial o.center) (hq : ConstructiblePoint initial q)
    (hr : ConstructiblePoint initial r) (hor : o.radius = dist q r) :
    ConstructibleCircle initial o := by
  apply ConstructibleCircle.centerRadius o ((r -ᵥ q) +ᵥ o.center) ho
  · have hm := ho.midpoint hr
    by_cases hmq : midpoint ℝ o.center r = q
    · convert hq
      rw [midpoint_eq_iff, AffineEquiv.pointReflection_apply] at hmq
      symm at ⊢ hmq
      rw [eq_vadd_iff_vsub_eq] at ⊢ hmq
      exact hmq.symm
    · apply ConstructiblePoint.lineCircle line[ℝ, midpoint ℝ o.center r, q]
        ⟨midpoint ℝ o.center r, dist (midpoint ℝ o.center r) q⟩
      · exact ConstructibleLine.pair hm hq hmq
      · apply ConstructibleCircle.centerRadius _ q hm hq
        simp [mem_sphere']
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use -1
        rw [AffineMap.lineMap_apply, neg_one_smul, neg_vsub_eq_vsub_rev,
          ← AffineEquiv.pointReflection_apply ℝ]
        rw [← midpoint_eq_iff, midpoint_eq_midpoint_iff_vsub_eq_vsub]
        rw [vsub_vadd_comm, ← neg_vsub_eq_vsub_rev _ r, vadd_vsub, neg_vsub_eq_vsub_rev]
      · rw [mem_sphere]
        simp only
        rw [dist_eq_norm_vsub, dist_eq_norm_vsub, vsub_midpoint, midpoint_vsub]
        simp_rw [← smul_add, norm_smul]
        congrm _ * ‖?_‖
        rw [vadd_vsub, vadd_vsub_assoc, add_comm _ (o.center -ᵥ r), vsub_add_vsub_cancel,
          add_comm]
  · rw [mem_sphere, dist_eq_norm_vsub, vadd_vsub, hor, dist_eq_norm_vsub']

theorem ConstructibleCircle.threePoints {initial : Set P} {o : Sphere P} (p q r : P)
    (hp : ConstructiblePoint initial p) (hq : ConstructiblePoint initial q)
    (hr : ConstructiblePoint initial r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpo : p ∈ o) (hqo : q ∈ o) (hro : r ∈ o) :
    ConstructibleCircle initial o := by
  refine ConstructibleCircle.centerRadius _ p ?_ hp hpo
  apply ConstructiblePoint.twoLines (AffineSubspace.perpBisector p q)
    (AffineSubspace.perpBisector q r) (ConstructiblePoint.perpBisector hp hq hpq)
    (ConstructiblePoint.perpBisector hq hr hqr)
  · contrapose hpr
    have hpr := congr((AffineSubspace.direction $hpr)ᗮ)
    simp_rw [AffineSubspace.direction_perpBisector, Submodule.orthogonal_orthogonal] at hpr
    have hpl : p ∈ AffineSubspace.mk' q (ℝ ∙ (q -ᵥ p)) := by
      rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
      use -1
      simp
    have hrl : r ∈ AffineSubspace.mk' q (ℝ ∙ (q -ᵥ p)) := by
      rw [hpr, AffineSubspace.mem_mk']
      apply Submodule.mem_span_singleton_self
    have hpeq := (Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hqo hpl).mpr hpo
    have hreq := (Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hqo hrl).mpr hro
    rw [hpeq.resolve_left hpq, hreq.resolve_left hqr.symm]
  · rw [AffineSubspace.mem_perpBisector_iff_dist_eq']
    rw [mem_sphere.mp hqo, mem_sphere.mp hpo]
  · rw [AffineSubspace.mem_perpBisector_iff_dist_eq']
    rw [mem_sphere.mp hqo, mem_sphere.mp hro]

end EuclideanGeometry
