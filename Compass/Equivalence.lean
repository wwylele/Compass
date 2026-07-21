module

public import Compass.ConstructibleNumber
public import Compass.CommonConstruction

import Mathlib.LinearAlgebra.Complex.FiniteDimensional


/-!

# Connection between Constructible Points and Numbers

This file connects constructible points and numbers

## Main Declarations

- `EuclideanGeometry.ConstructiblePoint.mem_constructibleClosure`: constructible points on the
  complex plane are in the constructible closure of the conjugate-closed initial points.
- `EuclideanGeometry.constructiblePoint_of_mem_constructibleClosure`: if 0 and 1 are constructible,
  all numbers on the constructible closure are construcible.

-/

public section

open ComplexConjugate
open scoped Real

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

theorem system_two_x {x y a b c d e f : ℝ}
    (h1 : x ^ 2 + a * x + y ^ 2 + b * y = c)
    (h2 : d * x + e * y = f) :
    (2 * (d ^ 2 + e ^ 2) * x + (a * e ^ 2 - b * d * e - 2 * d * f)) ^ 2
      = 4 * (d ^ 2 + e ^ 2) * (e ^ 2 * c - f ^ 2 - b * e * f) +
      (a * e ^ 2 - b * d * e - 2 * d * f) ^ 2 := by
  have h2' : e * y = f - d * x := by linear_combination h2
  have h3 : e ^ 2 * x ^ 2 + e ^ 2 * a * x + (e * y) ^ 2 + e * b * (e * y) = e ^ 2 * c := by
    linear_combination e ^ 2 * h1
  rw [h2'] at h3
  linear_combination 4 * (d ^ 2 + e ^ 2) * h3

theorem system_two_y {x y a b c d e f : ℝ}
    (h1 : x ^ 2 + a * x + y ^ 2 + b * y = c)
    (h2 : d * x + e * y = f) :
    (2 * (d ^ 2 + e ^ 2) * y + (b * d ^ 2 - a * d * e - 2 * e * f)) ^ 2
      = 4 * (d ^ 2 + e ^ 2) * (d ^ 2 * c - f ^ 2 - a * d * f) +
      (b * d ^ 2 - a * d * e - 2 * e * f) ^ 2 := by
  have h1' : y ^ 2 + b * y + x ^ 2 + a * x = c := by linear_combination h1
  have h2' : e * y + d * x = f := by linear_combination h2
  linear_combination system_two_x h1' h2'

local notation "Cℝ(" s ")" =>
  constructibleClosure (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ
local notation "Cℝ*(" s ")" =>
  constructibleClosure (Subfield.closure s) ℝ

theorem system_two_mem {s : Set ℝ} {x y a b c d e f : ℝ}
    (h1 : x ^ 2 + a * x + y ^ 2 + b * y = c)
    (h2 : d * x + e * y = f)
    (hde : d ≠ 0 ∨ e ≠ 0)
    (ha : a ∈ Cℝ*(s))
    (hb : b ∈ Cℝ*(s))
    (hc : c ∈ Cℝ*(s))
    (hd : d ∈ Cℝ*(s))
    (he : e ∈ Cℝ*(s))
    (hf : f ∈ Cℝ*(s)) :
    x ∈ Cℝ*(s) ∧ y ∈ Cℝ*(s) := by
  have hde : 2 * (d ^ 2 + e ^ 2) ≠ 0 := by
    suffices d ^ 2 + e ^ 2 ≠ 0 by simpa
    grind [add_eq_zero_iff_of_nonneg (sq_nonneg d) (sq_nonneg e)]
  have hx := system_two_x h1 h2
  have hy := system_two_y h1 h2
  constructor
  · have h : a * e ^ 2 - b * d * e - 2 * d * f ∈ Cℝ*(s) := by
      apply sub_mem
      · apply sub_mem
        · exact mul_mem ha (pow_mem he _)
        · exact mul_mem (mul_mem hb hd) he
      · exact mul_mem (mul_mem (by simp) hd) hf
    suffices 2 * (d ^ 2 + e ^ 2) * x + (a * e ^ 2 - b * d * e - 2 * d * f) ∈ Cℝ*(s) by
      set g := 2 * (d ^ 2 + e ^ 2) * x + (a * e ^ 2 - b * d * e - 2 * d * f) with hg
      convert_to (2 * (d ^ 2 + e ^ 2)) ⁻¹ * (g - (a * e ^ 2 - b * d * e - 2 * d * f)) ∈ Cℝ*(s)
      · rw [hg, add_sub_cancel_right, inv_mul_cancel_left₀ hde]
      apply mul_mem
      · exact inv_mem (mul_mem (by simp) (add_mem (pow_mem hd _) (pow_mem he _)))
      · exact sub_mem this h
    apply mem_constructibleClosure_of_sq_mem
    rw [hx]
    apply add_mem
    · apply mul_mem
      · apply mul_mem (by simp)
        apply add_mem (pow_mem hd _) (pow_mem he _)
      · apply sub_mem
        · apply sub_mem
          · exact mul_mem (pow_mem he _) hc
          · exact pow_mem hf _
        · exact mul_mem (mul_mem hb he) hf
    · exact pow_mem h _
  · have h : b * d ^ 2 - a * d * e - 2 * e * f ∈ Cℝ*(s) := by
      apply sub_mem
      · apply sub_mem
        · exact mul_mem hb (pow_mem hd _)
        · exact mul_mem (mul_mem ha hd) he
      · exact mul_mem (mul_mem (by simp) he) hf
    suffices 2 * (d ^ 2 + e ^ 2) * y + (b * d ^ 2 - a * d * e - 2 * e * f) ∈ Cℝ*(s) by
      set g := 2 * (d ^ 2 + e ^ 2) * y + (b * d ^ 2 - a * d * e - 2 * e * f) with hg
      convert_to (2 * (d ^ 2 + e ^ 2)) ⁻¹ * (g - (b * d ^ 2 - a * d * e - 2 * e * f)) ∈ Cℝ*(s)
      · rw [hg, add_sub_cancel_right, inv_mul_cancel_left₀ hde]
      apply mul_mem
      · exact inv_mem (mul_mem (by simp) (add_mem (pow_mem hd _) (pow_mem he _)))
      · exact sub_mem this h
    apply mem_constructibleClosure_of_sq_mem
    rw [hy]
    apply add_mem
    · apply mul_mem
      · apply mul_mem (by simp)
        apply add_mem (pow_mem hd _) (pow_mem he _)
      · apply sub_mem
        · apply sub_mem
          · exact mul_mem (pow_mem hd _) hc
          · exact pow_mem hf _
        · exact mul_mem (mul_mem ha hd) hf
    · exact pow_mem h _

theorem collinear_of_mem {a b p : ℂ} {l : AffineSubspace ℝ ℂ}
    (hl : Module.finrank ℝ l.direction = 1) (ha : a ∈ l) (hb : b ∈ l) (hp : p ∈ l) :
    Collinear ℝ {a, b, p} := by
  rw [collinear_iff_finrank_le_one, ← hl, ← direction_affineSpan]
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_le_of_subset_coe
  grind [SetLike.mem_coe]

theorem equation_of_collinear {a b p : ℂ} (habp : Collinear ℝ {a, b, p}) :
    (a.im - b.im) * p.re + (b.re - a.re) * p.im = a.re * (a.im - b.im) - a.im * (a.re - b.re) := by
  rw [collinear_iff_of_mem (show p ∈ {a, b, p} by simp)] at habp
  obtain ⟨v, hv⟩ := habp
  obtain ⟨ra, ha⟩ := hv a (by simp)
  obtain ⟨rb, hb⟩ := hv b (by simp)
  simp only [Complex.real_smul, vadd_eq_add] at ha hb
  simp [congr(Complex.re $ha), congr(Complex.re $hb),
    congr(Complex.im $ha), congr(Complex.im $hb)]
  ring

theorem line_eq_affineSpan {a b : ℂ} {l : AffineSubspace ℝ ℂ}
    (hl : Module.finrank ℝ l.direction = 1) (h : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) :
    l = line[ℝ, a, b] := by
  apply AffineSubspace.ext_of_direction_eq
  · rw [direction_affineSpan, vectorSpan_pair]
    let v : l.direction := ⟨a -ᵥ b, AffineSubspace.vsub_mem_direction ha hb⟩
    have hv : v ≠ 0 := by simpa [v, sub_eq_zero] using h
    rw [finrank_eq_one_iff_of_nonzero v hv] at hl
    have hl := congr(Submodule.map (l.direction.subtype) $hl)
    simpa [v] using hl.symm
  · refine ⟨a, ?_, ?_⟩
    · exact ha
    · apply left_mem_affineSpan_pair

theorem system_one_mem {s : Set ℝ} {x y a b c d e f : ℝ}
    (h1 : a * x + b * y = c)
    (h2 : d * x + e * y = f)
    (hdet : a * e ≠ b * d)
    (ha : a ∈ Cℝ*(s))
    (hb : b ∈ Cℝ*(s))
    (hc : c ∈ Cℝ*(s))
    (hd : d ∈ Cℝ*(s))
    (he : e ∈ Cℝ*(s))
    (hf : f ∈ Cℝ*(s)) :
    x ∈ Cℝ*(s) ∧ y ∈ Cℝ*(s) := by
  have h3 : (a * e - b * d) * x = c * e - f * b := by
    linear_combination e * h1 - b * h2
  have h4 : (a * e - b * d) * y = f * a - c * d := by
    linear_combination a * h2 - d * h1
  constructor
  · suffices (a * e - b * d)⁻¹ * ((a * e - b * d) * x) ∈ Cℝ*(s) by
      rw [inv_mul_cancel_left₀ (by simpa [sub_eq_zero] using hdet)] at this
      exact this
    rw [h3]
    refine mul_mem (inv_mem ?_) ?_
    · apply sub_mem (mul_mem ha he) (mul_mem hb hd)
    · apply sub_mem (mul_mem hc he) (mul_mem hf hb)
  · suffices (a * e - b * d)⁻¹ * ((a * e - b * d) * y) ∈ Cℝ*(s) by
      rw [inv_mul_cancel_left₀ (by simpa [sub_eq_zero] using hdet)] at this
      exact this
    rw [h4]
    refine mul_mem (inv_mem ?_) ?_
    · apply sub_mem (mul_mem ha he) (mul_mem hb hd)
    · apply sub_mem (mul_mem hf ha) (mul_mem hc hd)


theorem ConstructiblePoint.mem_constructibleClosure {initial : Set ℂ}
    (hinit : ∀ x ∈ initial, conj x ∈ initial) {p : ℂ}
    (h : ConstructiblePoint initial p) :
    p ∈ constructibleClosure (Subfield.closure initial) ℂ :=
  match h with
  | ConstructiblePoint.given p h => by
    refine Set.mem_of_mem_of_subset ?_ <| SetLike.coe_subset_coe.mpr bot_le
    rw [SetLike.mem_coe, IntermediateField.mem_bot, Set.mem_range]
    exact ⟨⟨p, Subfield.mem_closure_of_mem h⟩, by simp [Subfield.algebraMap_ofSubfield]⟩
  | ConstructiblePoint.twoLines l₁ l₂ hl₁ hl₂ h p hpl₁ hpl₂ =>
    match hl₁ with
    | ConstructibleLine.twoPoints a b ha hb hab l₁ hal hbl hl₁ =>
    match hl₂ with
    | ConstructibleLine.twoPoints c d hc hd hcd l₂ hcl hdl hl₂ => by
      have ha := ConstructiblePoint.mem_constructibleClosure hinit ha
      have hb := ConstructiblePoint.mem_constructibleClosure hinit hb
      have hc := ConstructiblePoint.mem_constructibleClosure hinit hc
      have hd := ConstructiblePoint.mem_constructibleClosure hinit hd
      have habpcl := collinear_of_mem hl₁ hal hbl hpl₁
      have hcdpcl := collinear_of_mem hl₂ hcl hdl hpl₂
      have habp := equation_of_collinear habpcl
      have hcdp := equation_of_collinear hcdpcl
      rw [mem_constructibleClosure_complex_iff hinit] at ⊢ ha hb hc hd
      apply system_one_mem habp hcdp
      · contrapose h
        rw [collinear_iff_of_mem (show p ∈ {a, b, p} by simp)] at habpcl
        rw [collinear_iff_of_mem (show p ∈ {c, d, p} by simp)] at hcdpcl
        obtain ⟨u, hu⟩ := habpcl
        obtain ⟨ra, ha⟩ := hu a (by simp)
        obtain ⟨rb, hb⟩ := hu b (by simp)
        obtain ⟨v, hv⟩ := hcdpcl
        obtain ⟨rc, hc⟩ := hv c (by simp)
        obtain ⟨rd, hd⟩ := hv d (by simp)
        simp only [Complex.real_smul, vadd_eq_add] at ha hb hc hd
        rw [congr(Complex.re $ha), congr(Complex.re $hb),
          congr(Complex.im $ha), congr(Complex.im $hb),
          congr(Complex.re $hc), congr(Complex.re $hd),
          congr(Complex.im $hc), congr(Complex.im $hd)] at h
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero, add_sub_add_right_eq_sub, Complex.add_re, Complex.mul_re, sub_zero] at h
        have : (u.re * v.im - u.im * v.re) * (ra - rb) * (rc - rd) = 0 := by
          linear_combination h
        have hab0 : ra - rb ≠ 0 := by
          contrapose hab
          rw [sub_eq_zero] at hab
          rw [ha, hb, hab]
        have hab0' : ra - rb ≠ (0 : ℂ) := by
          exact_mod_cast hab0
        have hcd0 : rc - rd ≠ 0 := by
          contrapose hcd
          rw [sub_eq_zero] at hcd
          rw [hc, hd, hcd]
        have : u.re * v.im - u.im * v.re = 0 := by simpa [hab0, hcd0] using this
        have huv : ∃ (w : ℝ), w * u = v := by
          by_cases hu0 : u.re = 0
          · have hu0' : u.im ≠ 0 := by
              intro h
              have hueq0 : u = 0 := Complex.ext hu0 h
              rw [hueq0] at ha hb
              simp [ha, hb] at hab
            have hv0 : v.re = 0 := by simpa [hu0, hu0'] using this
            use v.im / u.im
            apply Complex.ext
            · simp [hu0, hv0]
            · simp [hu0']
          · use v.re / u.re
            apply Complex.ext
            · simp [hu0]
            · simp only [Complex.ofReal_div, Complex.mul_im, Complex.div_ofReal_re,
                Complex.ofReal_re, Complex.div_ofReal_im, Complex.ofReal_im, zero_div, zero_mul,
                add_zero]
              grind
        obtain ⟨w, hw⟩ := huv
        have hw0 : w ≠ 0 := by
          intro h
          have hv0 : v = 0 := by simpa [h] using hw.symm
          rw [hv0] at hc hd
          simp [hc, hd] at hcd
        rw [line_eq_affineSpan hl₁ hab hal hbl]
        apply AffineSubspace.ext_of_direction_eq
        · rw [line_eq_affineSpan hl₂ hcd hcl hdl]
          simp_rw [direction_affineSpan, vectorSpan_pair, ha, hb, hc, hd, ← hw]
          suffices ℝ ∙ ((ra - rb) • u) = ℝ ∙ (((rc - rd) * w) • u) by simpa [sub_mul, ← mul_assoc]
          rw [Submodule.span_singleton_smul_eq (by simp [hab0])]
          rw [Submodule.span_singleton_smul_eq (by simp [hcd0, hw0])]
        · refine ⟨c, ?_, hcl⟩
          change c ∈ line[ℝ, a, b]
          rw [mem_affineSpan_pair_iff_exists_lineMap_eq, ha, hb, hc]
          simp_rw [← vadd_eq_add, ← AffineMap.lineMap_vadd, AffineMap.lineMap_apply_module,
            Complex.real_smul, ← mul_assoc, ← add_mul, vadd_eq_add, add_left_inj, ← hw]
          use (ra - rc * w) / (ra - rb)
          simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_mul]
          grind
      · exact sub_mem ha.2 hb.2
      · exact sub_mem hb.1 ha.1
      · apply sub_mem
        · exact mul_mem ha.1 (sub_mem ha.2 hb.2)
        · exact mul_mem ha.2 (sub_mem ha.1 hb.1)
      · exact sub_mem hc.2 hd.2
      · exact sub_mem hd.1 hc.1
      · apply sub_mem
        · exact mul_mem hc.1 (sub_mem hc.2 hd.2)
        · exact mul_mem hc.2 (sub_mem hc.1 hd.1)
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo =>
    match ho with
    | ConstructibleCircle.centerRadius o r ho hr hro =>
    match hl with
    | ConstructibleLine.twoPoints a b ha hb hab l hal hbl hl => by
      rw [EuclideanGeometry.mem_sphere, Complex.dist_eq] at hpo hro
      have hcircle := congr($(hpo.trans hro.symm) ^ 2)
      simp_rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hcircle
      set d := (-2) * o.center.re
      set e := (-2) * o.center.im
      set f := (r.re - o.center.re) ^ 2 + (r.im - o.center.im) ^ 2
          - (o.center.re ^ 2 + o.center.im ^ 2)
      have hcircle : p.re ^ 2 + d * p.re + p.im ^ 2 + e * p.im = f := by
        linear_combination hcircle
      have hl := equation_of_collinear <| collinear_of_mem hl hal hbl hpl
      have ho := ConstructiblePoint.mem_constructibleClosure hinit ho
      have hr := ConstructiblePoint.mem_constructibleClosure hinit hr
      have ha := ConstructiblePoint.mem_constructibleClosure hinit ha
      have hb := ConstructiblePoint.mem_constructibleClosure hinit hb
      rw [mem_constructibleClosure_complex_iff hinit] at ⊢ ho hr ha hb
      apply system_two_mem hcircle hl
      · contrapose! hab
        rw [Complex.ext_iff]
        constructor
        · symm
          simpa [sub_eq_zero] using hab.2
        · simpa [sub_eq_zero] using hab.1
      · exact mul_mem (by simp) ho.1
      · exact mul_mem (by simp) ho.2
      · apply sub_mem
        · refine add_mem (pow_mem ?_ _) (pow_mem ?_ _)
          · exact sub_mem hr.1 ho.1
          · exact sub_mem hr.2 ho.2
        · exact add_mem (pow_mem ho.1 _) (pow_mem ho.2 _)
      · exact sub_mem ha.2 hb.2
      · exact sub_mem hb.1 ha.1
      · apply sub_mem
        · exact mul_mem ha.1 (sub_mem ha.2 hb.2)
        · exact mul_mem ha.2 (sub_mem ha.1 hb.1)
  | ConstructiblePoint.twoCircles o₁ o₂ ho₁ ho₂ h p hpo₁ hpo₂ =>
    match ho₁ with
    | ConstructibleCircle.centerRadius o₁ r₁ ho₁ hr₁ hro₁ =>
    match ho₂ with
    | ConstructibleCircle.centerRadius o₂ r₂ ho₂ hr₂ hro₂ => by
      rw [EuclideanGeometry.mem_sphere, Complex.dist_eq] at hpo₁ hpo₂ hro₁ hro₂
      have h1 := congr($(hpo₁.trans hro₁.symm) ^ 2)
      have h2 := congr($(hpo₂.trans hro₂.symm) ^ 2)
      simp_rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h1 h2
      set a := 2 * (o₁.center.re - o₂.center.re)
      set b := 2 * (o₁.center.im - o₂.center.im)
      set c := (r₂.re - o₂.center.re) ^ 2 + (r₂.im - o₂.center.im) ^ 2
        + o₁.center.re ^ 2 + o₁.center.im ^ 2 +
        - ((r₁.re - o₁.center.re) ^ 2 + (r₁.im - o₁.center.im) ^ 2
        + o₂.center.re ^ 2 + o₂.center.im ^ 2)
      set d := (-2) * o₁.center.re
      set e := (-2) * o₁.center.im
      set f := (r₁.re - o₁.center.re) ^ 2 + (r₁.im - o₁.center.im) ^ 2
          - (o₁.center.re ^ 2 + o₁.center.im ^ 2)
      have hline : a * p.re + b * p.im = c := by
        linear_combination h2 - h1
      have h1' : p.re ^ 2 + d * p.re + p.im ^ 2 + e * p.im = f := by
        linear_combination h1
      have ho₁ := ConstructiblePoint.mem_constructibleClosure hinit ho₁
      have ho₂ := ConstructiblePoint.mem_constructibleClosure hinit ho₂
      have hr₁ := ConstructiblePoint.mem_constructibleClosure hinit hr₁
      have hr₂ := ConstructiblePoint.mem_constructibleClosure hinit hr₂
      rw [mem_constructibleClosure_complex_iff hinit] at ⊢ ho₁ ho₂ hr₁ hr₂
      apply system_two_mem h1' hline
      · contrapose! h
        have hcenter : o₁.center = o₂.center := by
          rw [Complex.ext_iff]
          constructor
          · simpa [a, sub_eq_zero] using h.1
          · simpa [b, sub_eq_zero] using h.2
        ext
        · exact hcenter
        · rw [← hpo₁, ← hpo₂, hcenter]
      · exact mul_mem (by simp) ho₁.1
      · exact mul_mem (by simp) ho₁.2
      · apply sub_mem
        · refine add_mem (pow_mem ?_ _) (pow_mem ?_ _)
          · exact sub_mem hr₁.1 ho₁.1
          · exact sub_mem hr₁.2 ho₁.2
        · exact add_mem (pow_mem ho₁.1 _) (pow_mem ho₁.2 _)
      · exact mul_mem (by simp) <| sub_mem ho₁.1 ho₂.1
      · exact mul_mem (by simp) <| sub_mem ho₁.2 ho₂.2
      · apply sub_mem
        · refine add_mem ?_ (pow_mem ho₁.2 _)
          refine add_mem ?_ (pow_mem ho₁.1 _)
          exact add_mem (pow_mem (sub_mem hr₂.1 ho₂.1) _) (pow_mem (sub_mem hr₂.2 ho₂.2) _)
        · refine add_mem ?_ (pow_mem ho₂.2 _)
          refine add_mem ?_ (pow_mem ho₂.1 _)
          exact add_mem (pow_mem (sub_mem hr₁.1 ho₁.1) _) (pow_mem (sub_mem hr₁.2 ho₁.2) _)

theorem constructiblePoint_of_mem_constructibleClosure {initial : Set ℂ}
    (h0 : ConstructiblePoint initial 0) (h1 : ConstructiblePoint initial 1) {p : ℂ}
    (h : p ∈ constructibleClosure (Subfield.closure initial) ℂ) :
    ConstructiblePoint initial p := by
  have h01 : ConstructibleCircle initial { center := 0, radius := 1 } :=
    ConstructibleCircle.centerRadius _ 1 h0 h1 (by simp [mem_sphere])
  have hl01 : ConstructibleLine initial line[ℝ, 0, 1] :=
    ConstructibleLine.pair h0 h1 (by simp)
  have hn1 : ConstructiblePoint initial (-1) := by
    apply ConstructiblePoint.lineCircle _ _ hl01 h01
    · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      use -1
      simp [AffineMap.lineMap_apply_module]
    · simp [mem_sphere]
  have hl0i : ConstructibleLine initial line[ℝ, 0, Complex.I] := by
    apply hl01.ortho h0 (left_mem_affineSpan_pair _ _ _)
    suffices ℝ ∙ Complex.I = (ℝ ∙ 1)ᗮ by simpa [direction_affineSpan, vectorSpan_pair_rev]
    ext x
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, Submodule.mem_span_singleton,
      Complex.inner, map_one, mul_one]
    refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ ⟨x.im, ?_⟩⟩
    · simp [← ha]
    · conv_rhs => rw [← Complex.re_add_im x, h]
      simp
  revert h
  apply constructibleClosure_closure_induction
  · simp
  · intro x hx
    exact ConstructiblePoint.given x hx
  · exact h1
  · intro x y hx hy
    by_cases hxy : x = y
    · by_cases! hx0 : x = 0
      · simpa [hx0, ← hxy] using h0
      apply ConstructiblePoint.lineCircle line[ℝ, x, 0] ⟨x, ‖x‖⟩
      · apply ConstructibleLine.pair hx h0 hx0
      · apply ConstructibleCircle.centerRadius _ 0 hx h0
        simp [mem_sphere]
      · rw [← hxy, ← vadd_eq_add]
        apply vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
        · apply left_mem_affineSpan_pair
        · simp [vectorSpan_pair]
      · simp [mem_sphere, hxy]
    apply ConstructiblePoint.twoCircles ⟨x, ‖y‖⟩ ⟨y, ‖x‖⟩
    · apply ConstructibleCircle.centerRadius' hx h0 hy
      simp
    · apply ConstructibleCircle.centerRadius' hy h0 hx
      simp
    · simp [hxy]
    · simp [mem_sphere]
    · simp [mem_sphere]
  · intro x hx
    by_cases! hx0 : x = 0
    · simpa [hx0] using h0
    apply ConstructiblePoint.lineCircle line[ℝ, 0, x] ⟨0, ‖x‖⟩
    · apply ConstructibleLine.twoPoints 0 x h0 hx
      · exact hx0.symm
      · apply left_mem_affineSpan_pair
      · apply right_mem_affineSpan_pair
      · rw [direction_affineSpan, vectorSpan_pair]
        apply finrank_span_singleton
        simpa using hx0
    · apply ConstructibleCircle.centerRadius _ x h0 hx
      simp [mem_sphere]
    · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      use -1
      simp [AffineMap.lineMap_apply_module']
    · simp [mem_sphere]
  · intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using h0
    apply ConstructiblePoint.lineCircle line[ℝ, 0, x⁻¹] ⟨0, ‖x‖⁻¹⟩ ?_ ?_ _
        (right_mem_affineSpan_pair _ _ _) (by simp [mem_sphere])
    · refine ConstructibleLine.twoPoints 0 (conj x) h0 ?_ ?_ _
          (left_mem_affineSpan_pair _ _ _) ?_ ?_
      · apply ConstructiblePoint.twoCircles ⟨0, dist x 0⟩ ⟨1, dist x 1⟩
        · apply ConstructibleCircle.centerRadius _ x h0 hx (by simp [mem_sphere])
        · apply ConstructibleCircle.centerRadius _ x h1 hx (by simp [mem_sphere])
        · simp
        · simp [mem_sphere]
        · simp [mem_sphere, dist_eq_norm_sub, Complex.norm_eq_sqrt_sq_add_sq]
      · contrapose hx0
        simpa using congr(conj $hx0.symm)
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use ‖x‖ ^ 2
        suffices ‖x‖ ^ 2 * x⁻¹ = (starRingEnd ℂ) x by
          simpa [AffineMap.lineMap_apply_module, ]
        rw [Complex.inv_def, ← Complex.ofReal_pow, Complex.ofReal_inv,
          Complex.sq_norm x, mul_comm (conj x), mul_inv_cancel_left₀]
        simpa using hx0
      · rw [direction_affineSpan, vectorSpan_pair_rev]
        apply finrank_span_singleton
        simpa using hx0
    · refine ConstructibleCircle.centerRadius _ (-‖x‖⁻¹ : ℂ) h0 ?_ (by simp [mem_sphere])
      apply ConstructiblePoint.lineCircle _ ⟨(‖x‖ - ‖x‖⁻¹ : ℂ) / 2, (‖x‖ + ‖x‖⁻¹) / 2⟩ hl01
      · apply ConstructibleCircle.threePoints (‖x‖ : ℂ) Complex.I (-Complex.I)
        · apply ConstructiblePoint.lineCircle _ ⟨0, ‖x‖⟩ hl01
          · exact ConstructibleCircle.centerRadius _ x h0 hx (by simp [mem_sphere])
          · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
            use ‖x‖
            simp [AffineMap.lineMap_apply_module]
          · simp [mem_sphere]
        · apply ConstructiblePoint.lineCircle _ _ hl0i h01 _ (right_mem_affineSpan_pair _ _ _)
          simp [mem_sphere]
        · apply ConstructiblePoint.lineCircle _ _ hl0i h01
          · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
            use -1
            simp [AffineMap.lineMap_apply_module]
          · simp [mem_sphere]
        · intro h
          have h := congr(Complex.im $h)
          simp at h
        · intro h
          have h := congr(Complex.im $h)
          simp at h
        · simp [CharZero.eq_neg_self_iff]
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp
          field
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp
          field
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use -‖x‖⁻¹
        simp [AffineMap.lineMap_apply_module]
      · rw [mem_sphere]
        rw [← sq_eq_sq₀ dist_nonneg (by positivity)]
        rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
  · intro x y hx hy
    by_cases! hx0 : x = 0
    · simpa [hx0] using h0
    by_cases! hy0 : y = 0
    · simpa [hy0] using h0
    apply ConstructiblePoint.lineCircle line[ℝ, 0, x * y] ⟨0, ‖x * y‖⟩
    · apply ConstructibleLine.twoPoints 0 (‖x * y‖⁻¹ • (x * y)) h0
      · apply ConstructiblePoint.twoCircles ⟨0, 1⟩ ⟨‖x‖⁻¹ • x, dist (‖y‖⁻¹ • y) 1⟩ h01
        · refine ConstructibleCircle.centerRadius' ?_
            (show ConstructiblePoint initial (‖y‖⁻¹ • y) from ?_) h1  (by simp)
          · refine ConstructiblePoint.lineCircle line[ℝ, 0, x] ⟨0, 1⟩ ?_ h01 ?_ ?_ ?_
            · exact ConstructibleLine.pair h0 hx hx0.symm
            · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
              use ‖x‖⁻¹
              simp [AffineMap.lineMap_apply_module]
            · simp [mem_sphere, hx0]
          · refine ConstructiblePoint.lineCircle line[ℝ, 0, y] ⟨0, 1⟩ ?_ h01 ?_ ?_ ?_
            · exact ConstructibleLine.pair h0 hy hy0.symm
            · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
              use ‖y‖⁻¹
              simp [AffineMap.lineMap_apply_module]
            · simp [mem_sphere, hy0]
        · simp [hx0]
        · suffices ‖y‖⁻¹ * ‖x‖⁻¹ * (‖x‖ * ‖y‖) = 1 by simpa [mem_sphere]
          rw [← mul_assoc, mul_assoc ‖y‖⁻¹, inv_mul_cancel₀ (by simpa using hx0), mul_one,
            inv_mul_cancel₀ (by simpa using hy0)]
        · rw [mem_sphere]
          simp_rw [dist_eq_norm_sub, Complex.real_smul, norm_mul, mul_inv, Complex.ofReal_mul]
          rw [← mul_assoc, mul_right_comm _ _ x, mul_assoc _ _ y, ← mul_sub_one, norm_mul,
            norm_mul, Complex.ofReal_inv, norm_inv, Complex.norm_real, norm_norm,
            inv_mul_cancel₀ (by simpa using hx0), one_mul]
      · simp [hx0, hy0]
      · apply left_mem_affineSpan_pair
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use ‖x * y‖⁻¹
        simp [AffineMap.lineMap_apply_module]
      · rw [direction_affineSpan, vectorSpan_pair]
        apply finrank_span_singleton
        simp [hx0, hy0]
    · refine ConstructibleCircle.centerRadius _ (Complex.I * ‖x * y‖) h0 ?_ (by simp [mem_sphere])
      apply ConstructiblePoint.lineCircle _
        ⟨⟨(‖x‖ - ‖y‖) / 2, (‖x * y‖ - 1) / 2⟩, √((‖x‖ ^ 2 + 1) * (‖y‖ ^ 2 + 1)) / 2⟩ hl0i
      · apply ConstructibleCircle.threePoints (-Complex.I) ‖x‖ (-‖y‖)
        · apply ConstructiblePoint.lineCircle _ _ hl0i h01
          · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
            use -1
            simp [AffineMap.lineMap_apply_module]
          · simp [mem_sphere]
        · apply ConstructiblePoint.lineCircle _ ⟨0, ‖x‖⟩ hl01
          · apply ConstructibleCircle.centerRadius _ x h0 hx
            simp [mem_sphere]
          · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
            use ‖x‖
            simp [AffineMap.lineMap_apply_module]
          · simp [mem_sphere]
        · apply ConstructiblePoint.lineCircle _ ⟨0, ‖y‖⟩ hl01
          · apply ConstructibleCircle.centerRadius _ y h0 hy
            simp [mem_sphere]
          · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
            use -‖y‖
            simp [AffineMap.lineMap_apply_module]
          · simp [mem_sphere]
        · intro h
          apply_fun Complex.im at h
          simp at h
        · intro h
          apply_fun Complex.im at h
          simp at h
        · contrapose hx0 with h
          norm_cast at h
          rw [← norm_eq_zero]
          apply le_antisymm
          · rw [h]
            simp
          · simp
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (div_nonneg (Real.sqrt_nonneg _) (by simp))]
          rw [div_pow, Real.sq_sqrt (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (div_nonneg (Real.sqrt_nonneg _) (by simp))]
          rw [div_pow, Real.sq_sqrt (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (div_nonneg (Real.sqrt_nonneg _) (by simp))]
          rw [div_pow, Real.sq_sqrt (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
      · rw [mul_comm]
        rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use ‖x * y‖
        simp [AffineMap.lineMap_apply_module']
      · rw [mem_sphere]
        rw [← sq_eq_sq₀ dist_nonneg (div_nonneg (Real.sqrt_nonneg _) (by simp))]
        rw [div_pow, Real.sq_sqrt (by positivity)]
        rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
    · apply right_mem_affineSpan_pair
    · simp [mem_sphere]
  · intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using h0
    have hnx2 : ConstructiblePoint initial ‖x ^ 2‖ := by
      apply ConstructiblePoint.lineCircle _ ⟨0, ‖x ^ 2‖⟩ hl01
      · apply ConstructibleCircle.centerRadius _ _ h0 hx
        simp [mem_sphere]
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use ‖x ^ 2‖
        simp [AffineMap.lineMap_apply_module]
      · simp [mem_sphere]
    refine ConstructiblePoint.lineCircle line[ℝ, 0, x] ⟨0, ‖x‖⟩ ?_ ?_ _
        (right_mem_affineSpan_pair _ _ _) (by simp [mem_sphere])
    · by_cases hxi : -‖x‖ ^ 2 = x ^ 2
      · rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply, sq] at hxi
        have hxir := congr(Complex.re $hxi)
        have hxii := congr(Complex.im $hxi)
        rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re] at hxir
        have : 2 * x.re * x.re = 0 := by linear_combination -hxir
        have hxr : x.re = 0 := by simpa using this
        convert hl0i using 1
        rw [AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair _ _ _)
          (left_mem_affineSpan_pair _ _ _), direction_affineSpan, direction_affineSpan,
          vectorSpan_pair_rev, vectorSpan_pair_rev]
        symm
        rw [Submodule.span_singleton_eq_span_singleton]
        have hxi0 : x.im ≠ 0 := by
          contrapose hx0
          simp [Complex.ext_iff, hxr, hx0]
        use Units.mk0 x.im hxi0
        conv_rhs => rw [← Complex.re_add_im x, hxr]
        simp
      refine ConstructibleLine.twoPoints 0 (midpoint ℝ (‖x ^ 2‖ : ℂ) (x ^ 2)) h0 ?_ ?_  _
          (left_mem_affineSpan_pair _ _ _) ?_ ?_
      · exact hnx2.midpoint hx
      · symm
        simpa [midpoint_eq_iff, Equiv.pointReflection_apply] using hxi
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use x.re
        rw [AffineMap.lineMap_apply_module', midpoint_eq_smul_add, invOf_eq_inv,
          norm_pow, Complex.sq_norm, Complex.normSq_apply, sq, Complex.real_smul, Complex.real_smul,
          sub_zero, add_zero]
        apply Complex.ext
        · simp
          ring
        · simp
          ring
      · rw [direction_affineSpan, vectorSpan_pair_rev]
        apply finrank_span_singleton
        simpa using hx0
    · refine ConstructibleCircle.centerRadius _ (‖x‖ * Complex.I) h0 ?_ (by simp [mem_sphere])
      refine ConstructiblePoint.lineCircle _ ⟨(‖x‖ ^ 2 - 1 : ℂ) / 2, (‖x‖ ^ 2 + 1) / 2⟩
          hl0i ?_ _ ?_ ?_
      · refine ConstructibleCircle.centerRadius _ _ ?_ hnx2 ?_
        · convert hn1.midpoint hnx2
          simp [midpoint_eq_smul_add]
          ring
        · rw [mem_sphere]
          rw [← sq_eq_sq₀ dist_nonneg (by positivity)]
          rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
          simp [← Complex.ofReal_pow]
          ring
      · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        use ‖x‖
        simp [AffineMap.lineMap_apply_module]
      · rw [mem_sphere]
        rw [← sq_eq_sq₀ dist_nonneg (by positivity)]
        rw [dist_eq_norm_sub, Complex.sq_norm, Complex.normSq_apply]
        simp [← Complex.ofReal_pow]
        ring

theorem constructiblePoint_iff_mem_constructibleClosure {initial : Set ℂ}
    (hinit : ∀ x ∈ initial, conj x ∈ initial)
    (h0 : ConstructiblePoint initial 0) (h1 : ConstructiblePoint initial 1) {p : ℂ} :
    ConstructiblePoint initial p ↔ p ∈ constructibleClosure (Subfield.closure initial) ℂ where
  mp h := h.mem_constructibleClosure hinit
  mpr h := constructiblePoint_of_mem_constructibleClosure h0 h1 h

end EuclideanGeometry
