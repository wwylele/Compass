module

public import Compass.CommonConstruction
public import Mathlib.Geometry.Euclidean.Inversion.Basic

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Similarity
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Inversion.ImageHyperplane
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!

# Compass-only construction and Mohr–Mascheroni theorem

In this file we define compass-only constructibility:
* `EuclideanGeometry.CompassConstructiblePoint`
* `EuclideanGeometry.CompassConstructibleCircle`

and prove the Mohr–Mascheroni theorem: they are equivalent to `EuclideanGeometry.ConstructiblePoint`
and `EuclideanGeometry.ConstructibleCircle`, respectively.


-/

public section

open Real

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

mutual

inductive CompassConstructiblePoint [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]
    (initial : Set P) : P → Prop
| given (p : P) (h : p ∈ initial) : CompassConstructiblePoint initial p
| twoCircles (o₁ o₂ : Sphere P)
    (ho₁ : CompassConstructibleCircle initial o₁) (ho₂ : CompassConstructibleCircle initial o₂)
    (h : o₁ ≠ o₂) (p : P) (hpo₁ : p ∈ o₁) (hpo₂ : p ∈ o₂) :
    CompassConstructiblePoint initial p

inductive CompassConstructibleCircle [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]
    (initial : Set P) : Sphere P → Prop
| centerRadius (o : Sphere P) (r : P) (hcenter : CompassConstructiblePoint initial o.center)
    (hradius : CompassConstructiblePoint initial r) (h : r ∈ o) :
    CompassConstructibleCircle initial o

end

theorem CompassConstructibleCircle.compassConstructiblePoint_center {initial : Set P}
    {o : Sphere P} (ho : CompassConstructibleCircle initial o) :
    CompassConstructiblePoint initial o.center := match ho with
  | CompassConstructibleCircle.centerRadius o _ hcenter _ ho =>
    hcenter

theorem CompassConstructibleCircle.compassConstructiblePoint_radius {initial : Set P}
    {o : Sphere P} (ho : CompassConstructibleCircle initial o) :
    ∃ r, CompassConstructiblePoint initial r ∧ r ∈ o := match ho with
  | CompassConstructibleCircle.centerRadius o r _ hr ho =>
    ⟨r, hr, ho⟩

theorem CompassConstructibleCircle.radius_nonneg {initial : Set P}
    {o : Sphere P} (ho : CompassConstructibleCircle initial o) :
    0 ≤ o.radius := match ho with
  | CompassConstructibleCircle.centerRadius o r hcenter hr ho => by
    rw [mem_sphere] at ho
    simp [← ho]

@[simp]
theorem _root_.EuclideanGeometry_reflection_perpBisector {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (a b : P) [(AffineSubspace.perpBisector a b).direction.HasOrthogonalProjection] :
    haveI : Nonempty ↥(AffineSubspace.perpBisector a b) :=
      AffineSubspace.perpBisector_nonempty.to_subtype
    reflection (AffineSubspace.perpBisector a b) a = b := by
  have : Nonempty ↥(AffineSubspace.perpBisector a b) :=
    AffineSubspace.perpBisector_nonempty.to_subtype
  rw [reflection_apply_of_mem _ _ (AffineSubspace.midpoint_mem_perpBisector a b)]
  simp only [AffineSubspace.direction_perpBisector, left_vsub_midpoint, invOf_eq_inv, map_smul]
  rw [Submodule.reflection_orthogonal_apply]
  rw [← map_neg, neg_vsub_eq_vsub_rev]
  rw [(Submodule.reflection_eq_self_iff _).mpr (by simp)]
  symm
  rw [eq_vadd_iff_vsub_eq]
  simp

theorem CompassConstructiblePoint.reflection {initial : Set P} {a b c : P}
    (ha : CompassConstructiblePoint initial a)
    (hb : CompassConstructiblePoint initial b) (hc : CompassConstructiblePoint initial c)
    (hbc : b ≠ c) :
    CompassConstructiblePoint initial (reflection line[ℝ, b, c] a) := by
  refine CompassConstructiblePoint.twoCircles ⟨b, dist a b⟩ ⟨c, dist a c⟩ ?_ ?_ ?_ _ ?_ ?_
  · exact CompassConstructibleCircle.centerRadius _ a hb ha (by simp [mem_sphere])
  · exact CompassConstructibleCircle.centerRadius _ a hc ha (by simp [mem_sphere])
  · simp [hbc]
  · simp [dist_comm a b, mem_sphere',
      EuclideanGeometry.dist_reflection_eq_of_mem line[ℝ, b, c] (left_mem_affineSpan_pair _ _ _ )]
  · simp [dist_comm a c, mem_sphere',
      EuclideanGeometry.dist_reflection_eq_of_mem line[ℝ, b, c] (right_mem_affineSpan_pair _ _ _ )]

theorem CompassConstructibleCircle.centerRadius' {initial : Set P} {a : Sphere P} {b r : P}
    (ha : CompassConstructiblePoint initial a.center) (hb : CompassConstructiblePoint initial b)
    (hr : CompassConstructiblePoint initial r) (hor : a.radius = dist b r) :
    CompassConstructibleCircle initial a := by
  by_cases! hab : a.center = b
  · apply CompassConstructibleCircle.centerRadius _ r ha hr
    rw [mem_sphere', hab, hor]
  let : Module.Oriented ℝ V _ :=
    ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ V hrank.out)⟩
  have hnorm : ‖√3 / 2‖ ^ 2 + ‖(2⁻¹ : ℝ)‖ ^ 2 = 1 := by
    rw [Real.norm_eq_abs, ← abs_pow, div_pow]
    norm_num
  let c := (√3 / 2) • o.rotation (π / 2 : ℝ) (b -ᵥ a.center) +ᵥ midpoint ℝ a.center b
  let d := (-(√3 / 2) • o.rotation (π / 2 : ℝ) (b -ᵥ a.center) +ᵥ midpoint ℝ a.center b)
  have ho1 : CompassConstructibleCircle initial ⟨a.center, dist a.center b⟩ := by
    apply CompassConstructibleCircle.centerRadius ⟨a.center, dist a.center b⟩ b ha hb
    rw [dist_comm, mem_sphere]
  have ho2 : CompassConstructibleCircle initial ⟨b, dist a.center b⟩ := by
    apply CompassConstructibleCircle.centerRadius ⟨b, dist a.center b⟩ a.center hb ha
    rw [mem_sphere]
  have hoo : (⟨a.center, dist a.center b⟩ : Sphere P) ≠ ⟨b, dist a.center b⟩ := by simp [hab]
  have hca : dist c a.center = dist a.center b := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
    rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a.center b) _).mpr ?_]
    · rw [← sq, ← sq]
      rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
        mul_pow, (o.rotation ↑(π / 2)).norm_map, left_vsub_midpoint, norm_smul, mul_pow,
        ← neg_vsub_eq_vsub_rev b a.center, norm_neg, ← add_mul, invOf_eq_inv]
      rw [hnorm]
      simp
    · apply angle_eq_pi_div_two_of_oangle_eq_pi_div_two
      rw [EuclideanGeometry.oangle, vadd_vsub, left_vsub_midpoint,
        ← neg_vsub_eq_vsub_rev b a.center,
        smul_neg, o.oangle_neg_right (by simpa using hab.symm) (by simpa using hab.symm),
        o.oangle_smul_left_of_pos _ _ (by simp),
        o.oangle_smul_right_of_pos _ _ (by simp),
        o.oangle_rotation_self_left (by simpa using hab.symm)]
      rw [← Real.Angle.coe_neg, ← Real.Angle.coe_add]
      congr
      ring
  have hcb : dist c b = dist a.center b := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
    rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a.center b) _).mpr ?_]
    · rw [← sq, ← sq]
      rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
        mul_pow, (o.rotation ↑(π / 2)).norm_map, right_vsub_midpoint, norm_smul, mul_pow,
        ← neg_vsub_eq_vsub_rev b a.center, norm_neg, ← add_mul, invOf_eq_inv]
      rw [hnorm]
      simp
    · apply angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
      rw [EuclideanGeometry.oangle, vadd_vsub, right_vsub_midpoint,
        o.oangle_smul_left_of_pos _ _ (by simp),
        o.oangle_smul_right_of_pos _ _ (by simp),
        o.oangle_rotation_self_left (by simpa using hab.symm)]
      rw [neg_div, Real.Angle.coe_neg]
  have hc : CompassConstructiblePoint initial c := by
    apply CompassConstructiblePoint.twoCircles _ _ ho1 ho2 hoo
    · simpa [mem_sphere] using hca
    · simpa [mem_sphere] using hcb
  have hda : dist d a.center = dist a.center b := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
    rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a.center b) _).mpr ?_]
    · rw [← sq, ← sq]
      rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
        mul_pow, (o.rotation ↑(π / 2)).norm_map, left_vsub_midpoint, norm_smul, mul_pow,
        ← neg_vsub_eq_vsub_rev b a.center, norm_neg, norm_neg, ← add_mul, invOf_eq_inv]
      rw [hnorm]
      simp
    · apply angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
      rw [EuclideanGeometry.oangle, vadd_vsub, left_vsub_midpoint,
        o.oangle_smul_left_of_neg _ _ (by simp),
        ← neg_vsub_eq_vsub_rev b a.center,
        smul_neg, ← neg_smul,
        o.oangle_smul_right_of_neg _ _ (by simp),
        o.oangle_neg_neg,
        o.oangle_rotation_self_left (by simpa using hab.symm)]
      rw [neg_div, Real.Angle.coe_neg]
  have hdb : dist d b = dist a.center b := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, sq]
    rw [(dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ (midpoint ℝ a.center b) _).mpr ?_]
    · rw [← sq, ← sq]
      rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub, vadd_vsub, norm_smul,
        mul_pow, (o.rotation ↑(π / 2)).norm_map, right_vsub_midpoint, norm_smul, mul_pow,
        ← neg_vsub_eq_vsub_rev b a.center, norm_neg, norm_neg, ← add_mul, invOf_eq_inv]
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
  have hd : CompassConstructiblePoint initial d := by
    apply CompassConstructiblePoint.twoCircles _ _ ho1 ho2 hoo
    · simpa [mem_sphere] using hda
    · simpa [mem_sphere] using hdb
  let ho3 : CompassConstructibleCircle initial ⟨c, dist r c⟩ := by
    apply CompassConstructibleCircle.centerRadius _ r hc hr
    simp [mem_sphere]
  let ho4 : CompassConstructibleCircle initial ⟨d, dist r d⟩ := by
    apply CompassConstructibleCircle.centerRadius _ r hd hr
    simp [mem_sphere]
  have hcd : c ≠ d := by
    contrapose hab with h
    simp only [neg_smul, vadd_right_cancel_iff, c, d] at h
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℝ] at h
    symm
    simpa using h
  have : Nonempty ↥(AffineSubspace.perpBisector a.center b) :=
     AffineSubspace.perpBisector_nonempty.to_subtype
  let e := reflection (AffineSubspace.perpBisector a.center b) r
  have he : CompassConstructiblePoint initial e := by
    refine CompassConstructiblePoint.twoCircles _ _ ho3 ho4 (by simp [hcd]) _ ?_ ?_
    · simp only [mem_sphere']
      rw [dist_comm r c]
      apply EuclideanGeometry.dist_reflection_eq_of_mem
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
      rw [hca, hcb]
    · simp only [mem_sphere']
      rw [dist_comm r d]
      apply EuclideanGeometry.dist_reflection_eq_of_mem
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
      rw [hda, hdb]
  apply CompassConstructibleCircle.centerRadius _ e ha he
  rw [mem_sphere, hor, ← dist_reflection, dist_comm b r]
  simp

theorem CompassConstructiblePoint.double {initial : Set P} {a b : P}
    (ha : CompassConstructiblePoint initial a) (hb : CompassConstructiblePoint initial b) :
    CompassConstructiblePoint initial (2 • (b -ᵥ a) +ᵥ a) := by
  by_cases! hab : a = b
  · simpa [hab] using ha
  let : Module.Oriented ℝ V _ :=
    ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ V hrank.out)⟩
  have hnorm : ‖√3 / 2‖ ^ 2 + ‖(2⁻¹ : ℝ)‖ ^ 2 = 1 := by
    rw [Real.norm_eq_abs, ← abs_pow, div_pow]
    norm_num
  let c := (√3 / 2) • o.rotation (π / 2 : ℝ) (b -ᵥ a) +ᵥ midpoint ℝ a b
  let d := (b -ᵥ a) +ᵥ c
  have ho1 : CompassConstructibleCircle initial ⟨a, dist a b⟩ := by
    apply CompassConstructibleCircle.centerRadius _ b ha hb
    rw [dist_comm, mem_sphere]
  have ho2 : CompassConstructibleCircle initial ⟨b, dist a b⟩ := by
    apply CompassConstructibleCircle.centerRadius _ a hb ha
    rw [mem_sphere]
  have hoo : (⟨a, dist a b⟩ : Sphere P) ≠ ⟨b, dist a b⟩ := by simp [hab]
  have hca : dist c a = dist a b := by
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
  have hcb : dist c b = dist a b := by
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
  have hc : CompassConstructiblePoint initial c := by
    apply CompassConstructiblePoint.twoCircles _ _ ho1 ho2 hoo
    · simpa [mem_sphere] using hca
    · simpa [mem_sphere] using hcb
  have ho3 : CompassConstructibleCircle initial ⟨c, dist a b⟩ := by
    rw [← hcb]
    apply CompassConstructibleCircle.centerRadius _ b hc hb
    simp [mem_sphere']
  have hbc : b ≠ c := by
    intro h
    simp_all
  have hoo' : (⟨b, dist a b⟩: Sphere P) ≠ ⟨c, dist a b⟩ := by simp [hbc]
  have hdb : dist d b = dist a b := by
    simp only [dist_eq_norm_vsub, vadd_vsub_assoc, d]
    rw [add_comm, vsub_add_vsub_cancel, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hca]
  have hdc : dist d c = dist a b := by
    simp [d, dist_eq_norm_vsub' V a b]
  have hd : CompassConstructiblePoint initial d := by
    apply CompassConstructiblePoint.twoCircles _ _ ho2 ho3 hoo'
    · simpa [mem_sphere] using hdb
    · simpa [mem_sphere] using hdc
  have heb : dist (2 • (b -ᵥ a) +ᵥ a) b = dist a b := by
    simp only [two_smul, dist_eq_norm_vsub, vadd_vsub_assoc]
    rw [add_assoc, vsub_add_vsub_cancel, vsub_self, add_zero, ← dist_eq_norm_vsub,
      ← dist_eq_norm_vsub']
  have hed : dist (2 • (b -ᵥ a) +ᵥ a) d = dist a b := by
    simp only [two_smul, dist_eq_norm_vsub, vadd_vsub_vadd_comm, add_sub_cancel_right,
      vsub_add_vsub_cancel, d]
    rw [← dist_eq_norm_vsub', hcb, ← dist_eq_norm_vsub]
  have ho4 : CompassConstructibleCircle initial ⟨d, dist a b⟩ := by
    rw [← hdc]
    apply CompassConstructibleCircle.centerRadius _ c hd hc
    simp [mem_sphere']
  have hbd : b ≠ d := by
    intro h
    simp_all
  have hoo'' : (⟨b, dist a b⟩: Sphere P) ≠ (⟨d, dist a b⟩: Sphere P) := by simp [hbd]
  apply CompassConstructiblePoint.twoCircles _ _ ho2 ho4 hoo''
  · simpa [mem_sphere] using heb
  · simpa [mem_sphere] using hed

theorem CompassConstructiblePoint.extend {initial : Set P} {a b : P}
    (ha : CompassConstructiblePoint initial a) (hb : CompassConstructiblePoint initial b)
    (n : ℕ) :
    CompassConstructiblePoint initial (n • (b -ᵥ a) +ᵥ a) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using ha
  | one => simpa using hb
  | more n ih1 ih2 =>
    convert CompassConstructiblePoint.double ih1 ih2 using 1
    simp only [vadd_vsub_vadd_cancel_right]
    simp_rw [← natCast_zsmul]
    rw [← sub_smul, smul_smul, vadd_vadd, ← add_smul]
    grind

theorem nonempty_sphere_inter_sphere {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)] [MetricSpace P]
    [NormedAddTorsor V P] {p : P} {o : Sphere P} (hr : 0 ≤ o.radius)
    (hpo : o.radius < dist o.center p) :
    Set.Nonempty ((o : Set P) ∩ (Sphere.mk p (dist p o.center) : Set P)) := by
  let f (q : P) := dist q o.center
  have hf : Continuous f := Continuous.dist (by fun_prop) (by fun_prop)
  have : IsConnected (Metric.sphere (0 : V) (dist o.center p)) :=
    isConnected_sphere (by
      apply Module.one_lt_rank_of_one_lt_finrank
      simp [‹Fact (Module.finrank ℝ V = 2)›.out]
    ) 0 (hr.trans hpo.le)
  have : IsConnected (Sphere.mk p (dist p o.center) : Set P) := by
    convert_to IsConnected (IsometryEquiv.vaddConst p '' Metric.sphere (0 : V) (dist o.center p))
    · rw [IsometryEquiv.image_sphere]
      simp [dist_comm o.center p]
    exact this.image _ (IsometryEquiv.continuous _).continuousOn
  let s := f '' (Sphere.mk p (dist p o.center) : Set P)
  have hs : IsConnected s := this.image f hf.continuousOn
  have hs0 : 0 ∈ s := (Set.mem_image _ _ _).mpr ⟨o.center, by simp [f, dist_comm o.center p]⟩
  let x := -(o.center -ᵥ p) +ᵥ p
  have hx : f x ∈ s := by
    apply Set.mem_image_of_mem
    simp [x, dist_eq_norm_vsub]
  have hx' : o.radius < f x := by
    simp only [dist_eq_norm_vsub, neg_vsub_eq_vsub_rev, vadd_vsub_assoc, f, x]
    rw [← two_smul ℝ, norm_smul, Real.norm_ofNat, ← dist_eq_norm_vsub']
    linarith
  have := hs.isPreconnected.ordConnected.out hs0 hx
    (show o.radius ∈ Set.Icc 0 (f x) by simp [hx'.le, hr])
  obtain ⟨y, hy1, hy2⟩ := this
  exact ⟨y, by simpa [f] using hy2, hy1⟩

theorem nontrivial_sphere_inter_sphere {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)] [MetricSpace P]
    [NormedAddTorsor V P] {p : P} {o : Sphere P} (hr : 0 < o.radius)
    (hpo : o.radius < dist o.center p) :
    Set.Nontrivial ((o : Set P) ∩ (Sphere.mk p (dist p o.center) : Set P)) := by
  obtain ⟨x, hx⟩ := nonempty_sphere_inter_sphere hr.le hpo
  have hx1 := hx.1
  have hx2 := hx.2
  simp only [Metric.mem_sphere, Sphere.mem_coe'] at hx1
  rw [mem_sphere'] at hx1
  simp only [Metric.mem_sphere'] at hx2
  refine ⟨x, hx, EuclideanGeometry.reflection line[ℝ, p, o.center] x, ?_, ?_⟩
  · constructor
    · simp only [Metric.mem_sphere, Sphere.mem_coe']
      rw [mem_sphere']
      rw [EuclideanGeometry.dist_reflection_eq_of_mem _ (right_mem_affineSpan_pair _ _ _)]
      exact hx1
    · simp only [Metric.mem_sphere']
      rw [EuclideanGeometry.dist_reflection_eq_of_mem _ (left_mem_affineSpan_pair _ _ _)]
      exact hx2
  · symm
    intro h
    rw [EuclideanGeometry.reflection_eq_self_iff] at h
    rcases (collinear_insert_of_mem_affineSpan_pair h).wbtw_or_wbtw_or_wbtw with h | h | h
      <;> have h := h.dist_add_dist
    · rw [dist_comm x o.center, dist_comm x p, hx1, hx2] at h
      contrapose! hpo
      rw [← h, dist_comm o.center p]
      simp
    · rw [hx1, hx2] at h
      simp_all
    · rw [hx1, dist_comm x p, hx2, dist_comm o.center p] at h
      simp_all

theorem CompassConstructiblePoint.inversion' {initial : Set P} {p : P}
    (hp : CompassConstructiblePoint initial p) {o : Sphere P}
    (ho : CompassConstructibleCircle initial o) (hpo : o.radius < dist o.center p) :
    CompassConstructiblePoint initial (inversion o.center o.radius p) := by
  have hr : 0 ≤ o.radius := ho.radius_nonneg
  rcases eq_or_lt_of_le hr with hr | hr
  · simpa [hr.symm] using ho.compassConstructiblePoint_center
  have hpo' : o.center ≠ p := by
    intro h
    have h1 := hr.trans hpo
    simp [h] at h1
  have hconssphere : CompassConstructibleCircle initial ⟨p, dist p o.center⟩ := by
    apply CompassConstructibleCircle.centerRadius _ o.center hp ho.compassConstructiblePoint_center
    simp [mem_sphere']
  have hnontrivial : Set.Nontrivial ((o : Set P) ∩ (Sphere.mk p (dist p o.center) : Set P)) :=
    nontrivial_sphere_inter_sphere hr hpo
  have hcons (q : P) (hq : q ∈ (o : Set P) ∩ (Sphere.mk p (dist p o.center) : Set P)) :
      CompassConstructiblePoint initial q := by
    refine CompassConstructiblePoint.twoCircles o _ ho hconssphere ?_ _ ?_ ?_
    · intro h
      exact hpo' congr(($h).center)
    · exact Set.mem_of_mem_inter_left hq
    · exact Set.mem_of_mem_inter_right hq
  have hcons' (q : P) (hq : q ∈ (o : Set P) ∩ (Sphere.mk p (dist p o.center) : Set P)) :
      CompassConstructibleCircle initial ⟨q, o.radius⟩ := by
    apply CompassConstructibleCircle.centerRadius _ o.center (hcons q hq)
      ho.compassConstructiblePoint_center
    have ha' := mem_sphere.mp <| Set.mem_of_mem_inter_left hq
    simpa [mem_sphere'] using ha'
  have hmem (q : P) (hq : q ∈ (o : Set P) ∩ (Sphere.mk p (dist p o.center) : Set P)) :
      inversion o.center o.radius p ∈ Sphere.mk q o.radius := by
    obtain ⟨hq1, hq2⟩ := (Set.mem_inter_iff _ _ _).mp hq
    simp only [Metric.mem_sphere] at hq1 hq2
    simp only [mem_sphere'] at ⊢
    conv_rhs => rw [← hq1]
    have hqo : q ≠ o.center := fun h ↦ by simp [hq1.symm, h] at hr
    have hcol : ¬ Collinear ℝ {q, o.center, p} := by
      intro h
      have h : Collinear ℝ {q, p, o.center} := by
        convert h using 1
        grind
      have h := (wbtw_of_collinear_of_dist_center_le_radius h
        ((Set.mem_inter_iff _ _ _).mp hq).2 (by simp) (by simp [mem_sphere']) hqo).dist_add_dist
      rw [hq2, hq1] at h
      rw [dist_comm o.center] at hpo
      have : dist p o.center < 0 := by simpa using h.trans_lt hpo
      exact (hpo.trans this).not_ge hr.le
    have hcol' : ¬ Collinear ℝ {inversion o.center o.radius p, o.center, q} := by
      contrapose hcol
      have h : inversion o.center o.radius p ∈ line[ℝ, q, o.center] :=
        hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hqo
      rw [inversion, vadd_right_mem_affineSpan_pair] at h
      obtain ⟨k, hk⟩ := h
      convert_to Collinear ℝ {p, q, o.center}
      · grind
      apply collinear_insert_of_mem_affineSpan_pair
      rw [← vsub_vadd p o.center]
      rw [vadd_right_mem_affineSpan_pair]
      use k / (o.radius / dist p o.center) ^ 2
      rw [div_eq_mul_inv, mul_comm, mul_smul, inv_smul_eq_iff₀ (by simp [hpo'.symm, hr.ne'])]
      exact hk
    apply EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi
    · have hsmul : (o.radius / dist p o.center) ^ 2 • (p -ᵥ o.center) =
          (inversion o.center o.radius p) -ᵥ o.center  := by
        simp [EuclideanGeometry.inversion_def]
      have hangle : ∠ q o.center (inversion o.center o.radius p) = ∠ q o.center p :=
        EuclideanGeometry.angle_smul_right_of_pos _
        (sq_pos_iff.mpr (div_ne_zero hr.ne' (by simp [hpo'.symm]))) hsmul
      rw [hangle]
      conv_rhs => rw [angle_comm, EuclideanGeometry.angle_eq_angle_of_dist_eq (by
        rw [← hq2, dist_comm])]
      refine (Similar.angle_eq_all ?_).2.2
      apply similar_of_side_angle_side hcol' hcol
      · rw [← hangle, angle_comm]
      · rw [dist_eq_norm_vsub, ← hsmul, norm_smul, ← dist_eq_norm_vsub, dist_comm p,
          dist_comm _ q, hq1]
        simp only [norm_pow, norm_div, Real.norm_eq_abs, abs_dist]
        rw [abs_of_nonneg hr.le]
        grind
    · contrapose hcol' with h
      convert EuclideanGeometry.collinear_of_angle_eq_pi h using 1
      grind
  obtain ⟨a, b, hab, habm⟩ := hnontrivial.pair_subset
  obtain ⟨ha, hb⟩ := Set.pair_subset_iff.mp habm
  refine CompassConstructiblePoint.twoCircles ⟨a, o.radius⟩ ⟨b, o.radius⟩ ?_ ?_ ?_ _ ?_ ?_
  · exact hcons' a ha
  · exact hcons' b hb
  · intro h
    have h := congr(($h).center)
    simp [hab] at h
  · exact hmem a ha
  · exact hmem b hb

theorem CompassConstructiblePoint.inversion {initial : Set P} {p : P}
    (hp : CompassConstructiblePoint initial p) {o : Sphere P}
    (ho : CompassConstructibleCircle initial o) :
    CompassConstructiblePoint initial (inversion o.center o.radius p) := by
  by_cases! hpo : p = o.center
  · simpa [← hpo] using hp
  have hpo : 0 < dist o.center p := by simpa [dist_pos] using hpo.symm
  obtain ⟨n, hn⟩ := exists_lt_nsmul hpo o.radius
  have hp' := ho.compassConstructiblePoint_center.extend  hp n
  have := hp'.inversion' ho (by
    convert! hn using 1
    simp [dist_eq_norm_vsub', ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
  )
  convert ho.compassConstructiblePoint_center.extend this n
  simp only [EuclideanGeometry.inversion, div_pow, ← Nat.cast_smul_eq_nsmul ℝ, dist_vadd_left,
    norm_smul, RCLike.norm_natCast, mul_pow, vadd_vsub, smul_smul, vadd_right_cancel_iff]
  rw [← dist_eq_norm_vsub]
  congr
  have hn : (n : ℝ) ≠ 0 := by
    intro h
    rw [Nat.cast_eq_zero] at h
    rw [h, zero_smul] at hn
    exact hn.not_ge ho.radius_nonneg
  grind

theorem Affine.Simplex.span_eq_top' {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    [FiniteDimensional k V] {n : ℕ} (T : Affine.Simplex k P n)
    (hrank : Module.finrank k V = n) : affineSpan k (Set.range T.points) = ⊤ := by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent,
    Fintype.card_fin, hrank]

theorem CompassConstructibleCircle.threePoints {initial : Set P} {a b c : P}
    {o : Sphere P} (ha : CompassConstructiblePoint initial a)
    (hb : CompassConstructiblePoint initial b) (hc : CompassConstructiblePoint initial c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hao : a ∈ o) (hbo : b ∈ o) (hco : c ∈ o) :
    CompassConstructibleCircle initial o := by
  have hind : AffineIndependent ℝ ![a, b, c] := by
    refine EuclideanGeometry.Cospherical.affineIndependent ?_ le_rfl ?_
    · use o.center, o.radius
      simp [hao, hbo, hco]
    · intro i j
      fin_cases i <;> fin_cases j <;> simp <;> grind
  have hoab : CompassConstructibleCircle initial ⟨a, dist b a⟩ :=
    CompassConstructibleCircle.centerRadius _ _ ha hb (by simp [mem_sphere])
  let d := inversion a (dist b a) c
  have hda : d ≠ a := by
    intro h
    rw [inversion_eq_center (by simpa using hab.symm)] at h
    exact hac.symm h
  have hd : CompassConstructiblePoint initial d := hc.inversion hoab
  let x := reflection line[ℝ, b, d] a
  have hxa : x ≠ a := by
    contrapose! hind with h
    rw [← collinear_iff_not_affineIndependent]
    convert_to Collinear ℝ {c, a, b}
    · simp
      grind
    apply collinear_insert_of_mem_affineSpan_pair
    rw [reflection_eq_self_iff] at h
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq, AffineMap.lineMap_apply] at h ⊢
    simp_rw [d, inversion] at h
    obtain ⟨r, hr⟩ := h
    have hr0 : r ≠ 0 := by
      intro hr0
      simp [hr0, hab.symm] at hr
    symm at hr
    rw [eq_vadd_iff_vsub_eq, vadd_vsub_assoc, smul_add, ← sub_eq_iff_eq_add] at hr
    nth_rw 1 [← one_smul ℝ (a -ᵥ b)] at hr
    rw [← sub_smul, smul_smul] at hr
    use (-(1 - r)) / (r * (dist b a / dist c a) ^ 2)
    symm
    rw [eq_vadd_iff_vsub_eq]
    rw [div_eq_mul_inv, mul_comm (-(1 - r)), ← smul_smul]
    symm
    rw [inv_smul_eq_iff₀ (by simp [hab.symm, hac.symm, hr0])]
    rw [← hr, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
  have hspan : affineSpan ℝ (Set.range (Affine.Simplex.mk ![a, b, c] hind).points) = ⊤ := by
    apply Affine.Simplex.span_eq_top'
    simp [‹Fact (Module.finrank ℝ V = 2)›.out]
  have : o.center = (Affine.Simplex.mk ![a, b, c] hind).circumcenter := by
    apply Affine.Simplex.eq_circumcenter_of_dist_eq (r := o.radius) _ ?_ ?_
    · rw [hspan]
      simp
    · intro i
      fin_cases i <;> simpa
  have hx : CompassConstructiblePoint initial x := by
    apply ha.reflection hb hd
    intro h
    have h := congr(inversion a (dist b a) $h)
    unfold d at h
    rw [inversion_inversion _ (by simpa using hab.symm), inversion_dist_center] at h
    exact hbc h
  refine CompassConstructibleCircle.centerRadius _ a ?_ ha hao
  rw [this]
  convert ← hx.inversion hoab
  apply Affine.Simplex.eq_circumcenter_of_dist_eq (r := dist b a ^ 2 / dist a x) _ ?_ ?_
  · rw [hspan]
    simp
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  intro i
  fin_cases i
  · simp [dist_center_inversion]
  · calc
      _ = dist b (inversion a (dist b a) x) := by simp
      _ = dist (inversion a (dist b a) b) (inversion a (dist b a) x) := by simp
      _ = dist b a ^ 2 / (dist b a * dist x a) * dist b x := by
        rw [dist_inversion_inversion hab.symm hxa]
      _ = dist b a ^ 2 / (dist b a * dist x a) * dist b a := by
        rw [dist_reflection_eq_of_mem _ (left_mem_affineSpan_pair _ _ _)]
      _ = _ := by
        rw [dist_comm a x]
        grind
  · calc
      _ = dist c (inversion a (dist b a) x) := by simp
      _ = dist (inversion a (dist b a) d) (inversion a (dist b a) x) := by
        rw [inversion_inversion _ (by simpa using hab.symm)]
      _ = dist b a ^ 2 / (dist d a * dist x a) * dist d x := by
        rw [dist_inversion_inversion hda hxa]
      _ = dist b a ^ 2 / (dist d a * dist x a) * dist d a := by
        rw [dist_reflection_eq_of_mem _ (right_mem_affineSpan_pair _ _ _)]
      _ = _ := by
        rw [dist_comm a x]
        have : dist d a ≠ 0 := by simpa using hda
        grind

theorem eq_affineSpan_pair_of_mem {a b : P} (hab : a ≠ b) {l : AffineSubspace ℝ P}
    (hl : Module.finrank ℝ l.direction = 1) (hal : a ∈ l) (hbl : b ∈ l) :
    l = line[ℝ, a, b] := by
  apply AffineSubspace.ext_of_direction_eq ?_ ⟨a, ⟨hal, left_mem_affineSpan_pair _ _ _⟩⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply AffineSubspace.direction_le
    apply affineSpan_le_of_subset_coe
    apply Set.pair_subset hal hbl
  rw [direction_affineSpan, hl]
  convert_to Module.finrank ℝ (vectorSpan ℝ (Set.range ![b, a])) = 1 using 1
  · congrm Module.finrank ℝ (vectorSpan ℝ ?_)
    simp
  apply AffineIndependent.finrank_vectorSpan
  · exact affineIndependent_of_ne _ hab.symm
  simp

theorem exists_compassConstructiblePoint_away_four {initial : Set P} {a b c d : P}
    (ha : CompassConstructiblePoint initial a)
    (hc : CompassConstructiblePoint initial c)
    (hal : a ∉ line[ℝ, c, d]) (hcl : c ∉ line[ℝ, a, b]) :
    ∃ p, CompassConstructiblePoint initial p ∧ p ∉ line[ℝ, a, b] ∧ p ∉ line[ℝ, c, d] := by
  refine ⟨_, ha.double hc, ?_, ?_⟩
  · contrapose hcl with h
    obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.mp h
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    use 2⁻¹ * r
    rw [AffineMap.lineMap_apply]
    symm
    rw [eq_vadd_iff_vsub_eq, ← smul_smul]
    symm
    rw [inv_smul_eq_iff₀ (by simp), hr, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat]
  · rw [two_smul, add_vadd, vsub_vadd]
    contrapose hal with h
    obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.mp h
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    use -r
    simp [AffineMap.lineMap_apply, hr]

omit hrank in
theorem _root_.Collinear.cospherical_inverse {a b c p : P} (r : ℝ) (h : Collinear ℝ {a, b, c})
    (hab : a ≠ b) (hp : p ∉ line[ℝ, a, b]) :
    Cospherical {p, inversion p r a, inversion p r b, inversion p r c} := by
  by_cases hr : r = 0
  · simpa [hr] using cospherical_singleton p
  let q := reflection line[ℝ, a, b] p
  have hqp : q ≠ p := by
    contrapose hp
    rw [EuclideanGeometry.reflection_eq_self_iff] at hp
    exact hp
  have ha : a ∈ AffineSubspace.perpBisector p q := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq,
      dist_reflection_eq_of_mem _ (left_mem_affineSpan_pair _ _ _)]
  have hb : b ∈ AffineSubspace.perpBisector p q := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq,
      dist_reflection_eq_of_mem _ (right_mem_affineSpan_pair _ _ _)]
  have hc : c ∈ AffineSubspace.perpBisector p q := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq,
      dist_reflection_eq_of_mem _ ?_]
    exact h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab
  have ha := Set.mem_image_of_mem (inversion p r) ha
  have hb := Set.mem_image_of_mem (inversion p r) hb
  have hc := Set.mem_image_of_mem (inversion p r) hc
  rw [EuclideanGeometry.image_inversion_perpBisector hr hqp] at ha hb hc
  use inversion p r q, (r ^ 2 / dist q p)
  simp only [Set.mem_sdiff, Metric.mem_sphere, Set.mem_singleton_iff, inversion_eq_center',
    not_or] at ha hb hc
  simp [dist_center_inversion, dist_comm p q, ha.1, hb.1, hc.1]

theorem _root_.EuclideanGeometry.image_inversion_sphere_dist_center' {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {c y : P} {R : ℝ} (hR : R ≠ 0) (hy : y ≠ c) :
    inversion c R '' (Sphere.mk y (dist y c) \ {c}) =
    AffineSubspace.perpBisector c (inversion c R y) := by
  rw [Set.image_sdiff (inversion_injective _ hR), image_inversion_sphere_dist_center hR hy]
  simp [hy, hR]

theorem _root_.EuclideanGeometry.midpoint_reflection_mem {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p : P) (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection] :
    midpoint ℝ p (reflection s p) ∈ s := by
  have h : midpoint ℝ p (reflection s p) = ↑(orthogonalProjection s p) := by
    rw [reflection_apply', midpoint_eq_iff, AffineEquiv.pointReflection_apply]
  rw [h]
  exact (orthogonalProjection s p).2

mutual

theorem ConstructiblePoint.compassConstructiblePoint {initial : Set P} {p : P}
    (hp : ConstructiblePoint initial p) :
    CompassConstructiblePoint initial p := match hp with
  | ConstructiblePoint.given p h =>
    CompassConstructiblePoint.given p h
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ hl p hpl₁ hpl₂ =>
    match hl₁ with
    | ConstructibleLine.twoPoints a b ha hb hab _ hal hbl hl₁r =>
    match hl₂ with
    | ConstructibleLine.twoPoints c d hc hd hcd _ hcl hdl hl₂r => by
      have ha := ha.compassConstructiblePoint
      have hb := hb.compassConstructiblePoint
      have hc := hc.compassConstructiblePoint
      have hd := hd.compassConstructiblePoint
      obtain rfl := eq_affineSpan_pair_of_mem hab hl₁r hal hbl
      obtain rfl := eq_affineSpan_pair_of_mem hcd hl₂r hcl hdl
      by_cases hacd : a ∈ line[ℝ, c, d]
      · convert ha
        contrapose! hl with hpa
        rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) hpl₁ hpa.symm]
        rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne hacd hpl₂ hpa.symm]
      by_cases hcab : c ∈ line[ℝ, a, b]
      · convert hc
        contrapose! hl with hpc
        rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) hpl₂ hpc.symm]
        rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne hcab hpl₁ hpc.symm]
      obtain ⟨q, hq, hqab, hqcd⟩ := exists_compassConstructiblePoint_away_four ha hc hacd hcab
      let o : Sphere P := ⟨q, dist a q⟩
      have haq : a ≠ q := by
        contrapose hqab
        simpa [← hqab] using left_mem_affineSpan_pair ℝ a b
      have hbq : b ≠ q := by
        contrapose hqab
        simpa [← hqab] using right_mem_affineSpan_pair ℝ a b
      have hcq : c ≠ q := by
        contrapose hqcd
        simpa [← hqcd] using left_mem_affineSpan_pair ℝ c d
      have hdq : d ≠ q := by
        contrapose hqcd
        simpa [← hqcd] using right_mem_affineSpan_pair ℝ c d
      have hr : o.radius ≠ 0 := by simpa [o] using haq
      have ho : CompassConstructibleCircle initial o := by
        apply CompassConstructibleCircle.centerRadius _ a hq ha
        simp [mem_sphere, o]
      have ha' := ha.inversion ho
      have hb' := hb.inversion ho
      have hc' := hc.inversion ho
      have hd' := hd.inversion ho
      have habp : Collinear ℝ {a, b, p} :=
        collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair _ _ _)
          (right_mem_affineSpan_pair _ _ _) hpl₁
      have hcdp : Collinear ℝ {c, d, p} :=
        collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair _ _ _)
          (right_mem_affineSpan_pair _ _ _) hpl₂
      have ⟨u, hu⟩ := cospherical_iff_exists_sphere.mp <|
        habp.cospherical_inverse (dist a q) hab hqab
      have ⟨v, hv⟩ := cospherical_iff_exists_sphere.mp <|
        hcdp.cospherical_inverse (dist a q) hcd hqcd
      simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff] at hu hv
      have hu' : CompassConstructibleCircle initial u := by
        refine CompassConstructibleCircle.threePoints ha' hb' hq ?_ ?_ ?_ hu.2.1 hu.2.2.1 hu.1
        · simpa [(inversion_injective _ hr).ne_iff] using hab
        · simp [o, haq]
        · simp [o, haq, hbq]
      have hv' : CompassConstructibleCircle initial v := by
        apply CompassConstructibleCircle.threePoints hc' hd' hq ?_ ?_ ?_ hv.2.1 hv.2.2.1 hv.1
        · simpa [(inversion_injective _ hr).ne_iff] using hcd
        · simp [o, haq, hcq]
        · simp [o, haq, hdq]
      have hp' : CompassConstructiblePoint initial (inversion o.center o.radius p) := by
        refine CompassConstructiblePoint.twoCircles _ _ hu' hv' ?_ _ hu.2.2.2 hv.2.2.2
        contrapose hl with huv
        have hup : u.radius = dist u.center q := by
          symm
          simpa [mem_sphere'] using hu.1
        rw [← huv] at hv
        have hau := hup ▸ inversion_inversion q hr _ ▸
          Set.mem_image_of_mem (inversion q (dist a q)) hu.2.1
        have hbu := hup ▸ inversion_inversion q hr _ ▸
          Set.mem_image_of_mem (inversion q (dist a q)) hu.2.2.1
        have hcu := hup ▸ inversion_inversion q hr _ ▸
          Set.mem_image_of_mem (inversion q (dist a q)) hv.2.1
        have hdu := hup ▸ inversion_inversion q hr _ ▸
          Set.mem_image_of_mem (inversion q (dist a q)) hv.2.2.1
        have huq : u.center ≠ q := by
          contrapose haq with huq
          simpa [huq] using hau
        rw [EuclideanGeometry.image_inversion_sphere_dist_center (by simpa using haq) huq]
          at hau hbu hcu hdu
        simp only [Set.mem_insert_iff, haq, SetLike.mem_coe, false_or] at hau
        simp only [Set.mem_insert_iff, hbq, SetLike.mem_coe, false_or] at hbu
        simp only [Set.mem_insert_iff, hcq, SetLike.mem_coe, false_or] at hcu
        simp only [Set.mem_insert_iff, hdq, SetLike.mem_coe, false_or] at hdu
        trans AffineSubspace.perpBisector q (inversion q (dist a q) u.center)
        · refine AffineSubspace.ext_of_direction_eq ?_ ⟨a, left_mem_affineSpan_pair _ _ _, hau⟩
          apply Submodule.eq_of_le_of_finrank_eq
          · apply AffineSubspace.direction_le
            apply affineSpan_pair_le_of_mem_of_mem hau hbu
          rw [direction_affineSpan, AffineSubspace.direction_perpBisector, vectorSpan_pair]
          rw [Submodule.finrank_orthogonal_span_singleton (n := 1) (by simp [huq, haq])]
          exact finrank_span_singleton (by simp [hab])
        · symm
          refine AffineSubspace.ext_of_direction_eq ?_ ⟨c, left_mem_affineSpan_pair _ _ _, hcu⟩
          apply Submodule.eq_of_le_of_finrank_eq
          · apply AffineSubspace.direction_le
            apply affineSpan_pair_le_of_mem_of_mem hcu hdu
          rw [direction_affineSpan, AffineSubspace.direction_perpBisector, vectorSpan_pair]
          rw [Submodule.finrank_orthogonal_span_singleton (n := 1) (by simp [huq, haq])]
          exact finrank_span_singleton (by simp [hcd])
      convert hp'.inversion ho
      rw [inversion_inversion _ hr]
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo => by
    match hl with
    | ConstructibleLine.twoPoints a b ha hb hab _ hal hbl hlr =>
    have ha := ha.compassConstructiblePoint
    have hb := hb.compassConstructiblePoint
    have ho := ho.compassConstructibleCircle
    by_cases hpoeq : p = o.center
    · exact hpoeq ▸ ho.compassConstructiblePoint_center
    obtain ⟨r, hr, hro⟩ := ho.compassConstructiblePoint_radius
    have hrone : o.center ≠ r := by
      intro h
      have ho0 : o.radius = 0 := by simpa [← h] using hro
      simp [mem_sphere, ho0, hpoeq] at hpo
    obtain rfl := eq_affineSpan_pair_of_mem hab hlr hal hbl
    by_cases hol : o.center ∈ line[ℝ, a, b]
    · by_cases hrl : r ∈ line[ℝ, a, b]
      · by_cases hrp : r = p
        · exact hrp ▸ hr
        convert hr.double ho.compassConstructiblePoint_center
        have h : AffineSubspace.mk' p (ℝ ∙ (a -ᵥ b)) = line[ℝ, a, b] := by
          apply AffineSubspace.ext_of_direction_eq
          · simp [direction_affineSpan, vectorSpan_pair]
          · use p
            simp [hpl]
        rw [← h] at hrl
        have : r = o.secondInter p (a -ᵥ b) :=
          ((Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hpo hrl).mpr hro)
            |>.resolve_left hrp
        have hmem : p -ᵥ o.center ∈ ℝ ∙ (a -ᵥ b) := by
          rw [← vectorSpan_pair, ← direction_affineSpan]
          apply AffineSubspace.vsub_mem_direction hpl hol
        obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
        have hk0 : k ≠ 0 := by
          contrapose hpoeq
          simpa [hpoeq] using hk.symm
        have hk' : a -ᵥ b = k⁻¹ • (p -ᵥ o.center) := by
          rw [← hk, smul_smul, inv_mul_cancel₀ hk0, one_smul]
        rw [two_smul, add_vadd, vsub_vadd, this, EuclideanGeometry.Sphere.secondInter,
          hk', real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq, mul_div_assoc, mul_comm _ (k⁻¹ * _), ← div_div,
          div_self (by simp [hk0, hpoeq]), div_inv_eq_mul, one_mul, smul_smul,
          mul_inv_cancel_right₀ hk0, neg_smul, two_smul, neg_add, neg_vsub_eq_vsub_rev, add_vadd,
          vsub_vadd, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_vsub_eq_vsub_rev, vsub_vadd]
      let r' := reflection line[ℝ, a, b] r
      have hr' : CompassConstructiblePoint initial r' := hr.reflection ha hb hab
      let f := (r -ᵥ r') +ᵥ o.center
      have hfo : o.center ≠ f := by
        contrapose hrl with h
        unfold f at h
        symm at h
        rw [← vsub_eq_zero_iff_eq, vadd_vsub, vsub_eq_zero_iff_eq] at h
        symm at h
        rw [reflection_eq_self_iff] at h
        exact h
      have hf : CompassConstructiblePoint initial f := by
        refine CompassConstructiblePoint.twoCircles ⟨o.center, dist r r'⟩ ⟨r, dist o.center r'⟩
          ?_ ?_ ?_ _ ?_ ?_
        · refine CompassConstructibleCircle.centerRadius' ?_ hr hr' (by simp)
          exact ho.compassConstructiblePoint_center
        · apply CompassConstructibleCircle.centerRadius' hr ho.compassConstructiblePoint_center hr'
          simp
        · simp [hrone]
        · simp [mem_sphere, f, dist_eq_norm_vsub]
        · simp [mem_sphere, f, vsub_vadd_comm r, dist_eq_norm_vsub]
      let f' := reflection line[ℝ, a, b] f
      have hff : f ≠ f' := by
        intro h
        symm at h
        unfold f at h
        rw [reflection_eq_self_iff, AffineSubspace.vadd_mem_iff_mem_direction _ hol] at h
        unfold r' at h
        have h2 := Submodule.mem_inf.mpr ⟨h, vsub_reflection_mem line[ℝ, a, b] r⟩
        rw [(Submodule.isCompl_orthogonal _).inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq]
          at h2
        symm at h2
        rw [reflection_eq_self_iff] at h2
        exact hrl h2
      have hf' : CompassConstructiblePoint initial f' := hf.reflection ha hb hab
      have hmid : midpoint ℝ r r' ∈ line[ℝ, a, b] := midpoint_reflection_mem r line[ℝ, a, b]
      have homid : o.center -ᵥ midpoint ℝ r r' ∈ line[ℝ, a, b].direction := by
        apply AffineSubspace.vsub_mem_direction hol hmid
      have hinner1 : inner ℝ (o.center -ᵥ midpoint ℝ r r') (r -ᵥ midpoint ℝ r r') = 0 := by
        refine (Submodule.mem_orthogonal _ _).mp ?_ _ homid
        rw [left_vsub_midpoint]
        apply Submodule.smul_mem
        apply vsub_reflection_mem
      have hom : dist o.center (midpoint ℝ r r') ^ 2 + dist r (midpoint ℝ r r') ^ 2 =
          o.radius ^ 2 := by
        simp_rw [sq]
        rw [← (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ _ _).mpr ?_,
          mem_sphere'.mp hro]
        rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
        exact hinner1
      have hom' : dist o.center (midpoint ℝ r r') ^ 2 =
          o.radius ^ 2 - dist r (midpoint ℝ r r') ^ 2 := by linear_combination hom
      let m := √(5 - 4 * dist o.center (midpoint ℝ r r') ^ 2 / o.radius ^ 2) • (p -ᵥ o.center) +ᵥ
        o.center
      have hmmem : m ∈ line[ℝ, a, b] := by
        refine AffineSubspace.vadd_mem_of_mem_direction ?_ hol
        apply Submodule.smul_mem
        exact AffineSubspace.vsub_mem_direction hpl hol
      have hinner : inner ℝ (p -ᵥ o.center) (r' -ᵥ r) = 0 := by
        refine (Submodule.mem_orthogonal _ _).mp ?_ _ (AffineSubspace.vsub_mem_direction hpl hol)
        rw [← neg_vsub_eq_vsub_rev]
        apply Submodule.neg_mem
        apply vsub_reflection_mem
      have hfm : dist f m = dist f r' := by
        unfold f m
        conv_lhs =>
          rw [dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right, sub_eq_add_neg,
            norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr (by
              rw [← neg_smul, real_inner_smul_right, real_inner_comm,
                ← neg_vsub_eq_vsub_rev r' r, inner_neg_right, hinner]
              simp
            ), ← sq, ← sq, norm_neg, norm_smul,
            norm_eq_abs, abs_of_nonneg (sqrt_nonneg _),
            ← Real.sqrt_sq (show 0 ≤ ‖p -ᵥ o.center‖ by simp), ← Real.sqrt_mul' _ (by simp),
            ← mem_sphere.mp hpo, dist_eq_norm_vsub _ p, sub_mul,
            div_mul_cancel₀ _ (by simp [hpoeq]), sq_sqrt (by
              rw [hom', ← dist_eq_norm_vsub, mem_sphere.mp hpo, mul_sub, ← sub_add, ← sub_mul,
                show (5 : ℝ) - 4 = 1 by norm_num, one_mul]
              positivity
            ), hom', ← mem_sphere.mp hpo,
            dist_left_midpoint, dist_eq_norm_vsub, dist_eq_norm_vsub, mul_pow, mul_sub, ← mul_assoc,
            show 4 * (‖(2 : ℝ)‖⁻¹) ^ 2 = 1 by norm_num, one_mul, ← sub_add, ← sub_mul,
            show (5 : ℝ) - 4 = 1 by norm_num, one_mul, add_comm _ (‖r -ᵥ r'‖ ^ 2), ← add_assoc,
            ← two_mul]
        conv_rhs =>
          rw [dist_eq_norm_vsub, vadd_vsub_assoc,
            ← vsub_add_vsub_cancel o.center (midpoint ℝ r r') r', midpoint_vsub_right,
            add_comm, add_assoc,
            (show (⅟(2 : ℝ) • (r -ᵥ r') + (r -ᵥ r')) =
              (⅟(2 : ℝ) • (r -ᵥ r') + (1 : ℝ) • (r -ᵥ r')) by simp),
            ← add_smul,
            norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr (by
              rw [left_vsub_midpoint, real_inner_smul_right,
                mul_eq_zero_iff_left (by simp)] at hinner1
              rw [real_inner_smul_right, hinner1]
              simp
            ), ← sq, ← sq, ← dist_eq_norm_vsub,
            hom', ← mem_sphere.mp hpo, dist_eq_norm_vsub, dist_eq_norm_vsub, left_vsub_midpoint,
            norm_smul, norm_smul, mul_pow, mul_pow, sub_add, ← sub_mul,
            show ‖⅟(2 : ℝ)‖ ^ 2 - ‖⅟(2 : ℝ) + 1‖ ^ 2 = -2 by norm_num,
            neg_mul, sub_neg_eq_add, add_comm]
      have hm : CompassConstructiblePoint initial m := by
        refine CompassConstructiblePoint.twoCircles ⟨f, dist f r'⟩ ⟨f', dist f' r⟩ ?_ ?_ ?_ m ?_ ?_
        · exact CompassConstructibleCircle.centerRadius _ r' hf hr' (by simp [mem_sphere'])
        · exact CompassConstructibleCircle.centerRadius _ r hf' hr (by simp [mem_sphere'])
        · simp [hff]
        · simp [mem_sphere', hfm]
        · simp only [mem_sphere]
          rw [dist_reflection_eq_of_mem _ hmmem, dist_comm m f, hfm]
          apply dist_reflection
      have hom : dist o.center m = dist f p := by
        unfold m f
        conv_lhs =>
          rw [dist_eq_norm_vsub', vadd_vsub, norm_smul, hom', norm_eq_abs,
            abs_of_nonneg (sqrt_nonneg _), ← Real.sqrt_sq (show 0 ≤ ‖p -ᵥ o.center‖ by simp),
            ← Real.sqrt_mul' _ (by simp), ← mem_sphere.mp hpo, dist_eq_norm_vsub,
            sub_mul, div_mul_cancel₀ _ (by simp [hpoeq]), mul_sub, ← sub_add, ← sub_mul,
            show (5 : ℝ) - 4 = 1 by norm_num, one_mul, dist_left_midpoint, mul_pow, ← mul_assoc]
        conv_rhs =>
          rw [dist_eq_norm_vsub', vsub_vadd_eq_vsub_sub, sub_eq_add_neg,
            neg_vsub_eq_vsub_rev, norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr hinner,
            ← sq, ← sq, ← dist_eq_norm_vsub' _ r]
        norm_num
      refine CompassConstructiblePoint.twoCircles o ⟨f, dist o.center m⟩ ho ?_ ?_ p hpo ?_
      · apply CompassConstructibleCircle.centerRadius' hf ho.compassConstructiblePoint_center hm
        simp
      · rw [ne_eq, Sphere.ext_iff.not]
        simp [hfo]
      · simp [mem_sphere', hom]
    · let q := reflection line[ℝ, a, b] o.center
      have hoq : o.center ≠ q := by
        contrapose hol
        exact (reflection_eq_self_iff _).mp hol.symm
      have hq : CompassConstructiblePoint initial q :=
        CompassConstructiblePoint.reflection ho.compassConstructiblePoint_center ha hb hab
      refine CompassConstructiblePoint.twoCircles o ⟨q, o.radius⟩ ho ?_ ?_ _ hpo ?_
      · apply CompassConstructibleCircle.centerRadius' hq ho.compassConstructiblePoint_center hr
        rw [mem_sphere'] at hro
        simp [hro]
      · rw [ne_eq, Sphere.ext_iff.not]
        simp [hoq]
      · simp only [mem_sphere, q]
        rw [dist_reflection_eq_of_mem _ hpl]
        rw [mem_sphere] at hpo
        exact hpo
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ ho p hpo₁ hpo₂ =>
    CompassConstructiblePoint.twoCircles o₁ o₂ ho₁.compassConstructibleCircle
      ho₂.compassConstructibleCircle ho p hpo₁ hpo₂

theorem ConstructibleCircle.compassConstructibleCircle {initial : Set P} {o : Sphere P}
    (ho : ConstructibleCircle initial o) :
    CompassConstructibleCircle initial o := match ho with
  | ConstructibleCircle.centerRadius o r hcenter hr ho =>
    CompassConstructibleCircle.centerRadius o r
      hcenter.compassConstructiblePoint hr.compassConstructiblePoint ho

end

mutual

theorem CompassConstructiblePoint.constructiblePoint {initial : Set P} {p : P}
    (hp : CompassConstructiblePoint initial p) :
    ConstructiblePoint initial p := match hp with
  | CompassConstructiblePoint.given p h =>
    ConstructiblePoint.given p h
  | CompassConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ ho p hpo₁ hpo₂ =>
    ConstructiblePoint.twoCircles o₁ o₂ ho₁.constructibleCircle
      ho₂.constructibleCircle ho p hpo₁ hpo₂

theorem CompassConstructibleCircle.constructibleCircle {initial : Set P} {o : Sphere P}
    (ho : CompassConstructibleCircle initial o) :
    ConstructibleCircle initial o := match ho with
  | CompassConstructibleCircle.centerRadius o r hcenter hr ho =>
    ConstructibleCircle.centerRadius o r
      hcenter.constructiblePoint hr.constructiblePoint ho

end

theorem mohr_mascheroni_point :
    CompassConstructiblePoint (V := V) (P := P) = ConstructiblePoint := by
  ext initial p
  exact ⟨fun h ↦ h.constructiblePoint, fun h ↦ h.compassConstructiblePoint⟩

theorem mohr_mascheroni_circle :
    CompassConstructibleCircle (V := V) (P := P) = ConstructibleCircle := by
  ext initial p
  exact ⟨fun h ↦ h.constructibleCircle, fun h ↦ h.compassConstructibleCircle⟩

end EuclideanGeometry
