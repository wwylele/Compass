module

public import Compass.CommonConstruction
public import Mathlib.Geometry.Euclidean.Inversion.Basic

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Similarity

/-!



-/

public section

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
    (ho : CompassConstructibleCircle initial o) (hr : 0 ≤ o.radius)
    (hpo : o.radius < dist o.center p) :
    CompassConstructiblePoint initial (inversion o.center o.radius p) := by
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

/-mutual

theorem ConstructiblePoint.compassConstructiblePoint {initial : Set P} {p : P}
    (hp : ConstructiblePoint initial p) :
    CompassConstructiblePoint initial p := match hp with
  | ConstructiblePoint.given p h =>
    CompassConstructiblePoint.given p h
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ hl p hpl₁ hpl₂ =>
    ...
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo =>
    ...
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ ho p hpo₁ hpo₂ =>
    CompassConstructiblePoint.twoCircles o₁ o₂ ho₁.compassConstructibleCircle
      ho₂.compassConstructibleCircle ho p hpo₁ hpo₂

theorem ConstructibleCircle.compassConstructibleCircle {initial : Set P} {o : Sphere P}
    (ho : ConstructibleCircle initial o) :
    CompassConstructibleCircle initial o := match ho with
  | ConstructibleCircle.centerRadius o r hcenter hr ho =>
    CompassConstructibleCircle.centerRadius o r
      hcenter.compassConstructiblePoint hr.compassConstructiblePoint ho

end-/

end EuclideanGeometry
