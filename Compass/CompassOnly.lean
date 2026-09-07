module

public import Compass.CommonConstruction
public import Mathlib.Geometry.Euclidean.Inversion.Basic

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Similarity
import Mathlib.Geometry.Euclidean.Triangle

/-!



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

theorem CompassConstructibleCircle.radius_nonneg {initial : Set P}
    {o : Sphere P} (ho : CompassConstructibleCircle initial o) :
    0 ≤ o.radius := match ho with
  | CompassConstructibleCircle.centerRadius o r hcenter hr ho => by
    rw [mem_sphere] at ho
    simp [← ho]

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
