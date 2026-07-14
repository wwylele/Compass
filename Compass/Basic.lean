module

public import Compass.ConstructibleClosure
public import Compass.Def

public import Mathlib

/-!
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


theorem AffineIsometryEquiv.trans_apply {𝕜 : Type*} {V : Type*} {V₂ : Type*} {V₃ : Type*}
    {P : Type*} {P₂ : Type*} {P₃ : Type*}
    [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    [PseudoMetricSpace P] [NormedAddTorsor V P] [SeminormedAddCommGroup V₂]
    [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
    [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃]
    [NormedAddTorsor V₃ P₃] (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) (x : P) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

@[simp]
theorem arccos_half : Real.arccos 2⁻¹ = π / 3 := by
  apply Real.arccos_eq_of_eq_cos
  · exact div_nonneg Real.pi_nonneg (by simp)
  · grind [Real.pi_nonneg]
  · simp

theorem irreducible_861 :
    Irreducible (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℚ) := by
  have hdegeee :
      (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℚ).natDegree = 3 := by
    compute_degree!
  have hdegree' :
      (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℤ).natDegree = 3 := by
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdegeee]
  intro x h
  have haeval : (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1 : Polynomial ℤ).aeval x = 0 := by
    simpa [map_ofNat, Polynomial.IsRoot.def] using h
  have hnum : IsFractionRing.num ℤ x ∣ 1 := by simpa using num_dvd_of_is_root haeval
  have hnum : x.num = 1 ∨ x.num = -1 := by
    simpa [← isUnit_iff_dvd_one, Int.isUnit_iff] using x.isFractionRingNum.symm.dvd.trans hnum
  have hden := den_dvd_of_is_root haeval
  rw [Polynomial.leadingCoeff, hdegree', Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
    Polynomial.coeff_one] at hden
  have hden : (IsFractionRing.den ℤ x).val ∣ 8 := by simpa using hden
  have hden : x.den ∣ 8 := by
    simpa using x.isFractionRingDen.symm.dvd.trans (Int.natAbs_dvd_natAbs.mpr hden)
  have hdenle : x.den ≤ 8 := Nat.le_of_dvd (by simp) hden
  interval_cases hdeneq : x.den
  · simp at hden
  · rcases hnum with hnum | hnum
    · have hx : x = 1 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
  · rcases hnum with hnum | hnum
    · have hx : x = 1 / 2 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 / 2 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
  · simp at hden
  · rcases hnum with hnum | hnum
    · have hx : x = 1 / 4 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 / 4 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
  · simp at hden
  · simp at hden
  · simp at hden
  · rcases hnum with hnum | hnum
    · have hx : x = 1 / 8 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 / 8 := by rw [← x.num_div_den, hnum, hdeneq]; simp
      norm_num [hx, map_ofNat] at haeval

theorem irreducible_cube_2 :
    Irreducible (Polynomial.X ^ 3 - 2 : Polynomial ℚ) := by
  have hdegeee : (Polynomial.X ^ 3 - 2 : Polynomial ℚ).natDegree = 3 := by
    compute_degree!
  have hdegree' : (Polynomial.X ^ 3 - 2 : Polynomial ℤ).natDegree = 3 := by
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdegeee]
  intro x h
  have haeval : (Polynomial.X ^ 3 - 2 : Polynomial ℤ).aeval x = 0 := by
    simpa [map_ofNat, Polynomial.IsRoot.def] using h
  have hnum : IsFractionRing.num ℤ x ∣ 2 := by simpa using num_dvd_of_is_root haeval
  have hnum : x.num ∣ 2 := by simpa using x.isFractionRingNum.symm.dvd.trans hnum
  have hnum2 : x.num.natAbs ≤ 2 := by simpa using Int.natAbs_le_of_dvd_ne_zero hnum (by simp)
  have hden := den_dvd_of_is_root haeval
  rw [Polynomial.leadingCoeff, hdegree', Polynomial.coeff_sub] at hden
  have hden : (IsFractionRing.den ℤ x).val ∣ 1 := by simpa using hden
  have hden : x.den = 1 := by
    simpa using x.isFractionRingDen.symm.dvd.trans (Int.natAbs_dvd_natAbs.mpr hden)
  interval_cases hnumabs : x.num.natAbs
  · rcases x.num.natAbs_eq with h | h
    · have hx : x = 0 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = 0 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
  · rcases x.num.natAbs_eq with h | h
    · have hx : x = 1 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -1 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
  · rcases x.num.natAbs_eq with h | h
    · have hx : x = 2 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval
    · have hx : x = -2 := by rw [← x.num_div_den, hden, h, hnumabs]; simp
      norm_num [hx, map_ofNat] at haeval

noncomputable
def ratEquivBot {K : Type*} [Field K] [CharZero K] : ℚ ≃+* (⊥ : Subfield K) :=
    (algebraMap ℚ K).rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr Subfield.bot_eq_of_charZero.symm)

theorem re_im_image_01 : Complex.re '' {0, 1} ∪ Complex.im '' {0, 1} = {0, 1} := by
  ext x
  simp
  grind

theorem Subfield.closrue_01 {K : Type*} [Field K] : Subfield.closure ({0, 1} : Set K) = ⊥ := by
  refine Subfield.closure_eq_of_le ?_ (by simp)
  apply Set.pair_subset (by simp) (by simp)

theorem not_exist_angle_trisection :
    ∃ p₁ p₂ p₃ : P, p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
    ¬ ∃ q₁ q₂ q₃ : P,
    ConstructiblePoint {p₁, p₂, p₃} q₁ ∧
    ConstructiblePoint {p₁, p₂, p₃} q₂ ∧
    ConstructiblePoint {p₁, p₂, p₃} q₃ ∧
    3 * ∠ q₁ q₂ q₃ = ∠ p₁ p₂ p₃ := by
  push Not
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  let o := Nonempty.some (show Nonempty P from inferInstance)
  let basis : OrthonormalBasis (Fin 2) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hrank.out)
  refine ⟨((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o, o, basis 0 +ᵥ o, ?_, ?_, ?_, ?_⟩
  · suffices ((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o ≠ (0 : V) +ᵥ o by simpa
    rw [(vadd_right_cancel_iff _).ne]
    intro h
    have h := congr(basis.repr $h 0)
    simp at h
  · suffices (0 : V) +ᵥ o ≠ basis 0 +ᵥ o by simpa
    rw [(vadd_right_cancel_iff _).ne]
    intro h
    have h := congr(basis.repr $h 0)
    simp at h
  · rw [(vadd_right_cancel_iff _).ne]
    intro h
    have h := congr(basis.repr $h 0)
    simp at h
  intro q₁ q₂ q₃
  let e : P ≃ᵃⁱ[ℝ] ℂ := (AffineIsometryEquiv.vaddConst ℝ o).symm.trans
    (basis.equiv Complex.orthonormalBasisOneI (Equiv.refl _)).toAffineIsometryEquiv
  have hp₁ : e (((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o) =
      2⁻¹ + 2⁻¹ * ↑√3 * Complex.I := by
    simp_rw [e, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
        vadd_vsub]
    simp
  have hp₂ : e o = 0 := by simp [e]
  have hp₃ : e (basis 0 +ᵥ o) = 1 := by
    simp_rw [e, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
        vadd_vsub]
    simp
  have hinit : e '' {((2⁻¹ : ℝ) • basis 0 + (2⁻¹ * √3) • basis 1) +ᵥ o, o, basis 0 +ᵥ o} =
      {2⁻¹ + 2⁻¹ * √3 * Complex.I, 0, 1} := by
    simp_rw [Set.image_insert_eq, Set.image_singleton, hp₁, hp₂, hp₃]
  have hnorm : ‖2⁻¹ + 2⁻¹ * ↑√3 * Complex.I‖ = 1 := by
    rw [← sq_eq_sq₀ (by simp) (by simp), Complex.sq_norm]
    suffices 2⁻¹ * 2⁻¹ + 2⁻¹ * √3 * (2⁻¹ * √3) = 1 by simpa [Complex.normSq]
    grind
  have hcons : ConstructiblePoint {2⁻¹ + 2⁻¹ * √3 * Complex.I, 0, 1}
      = ConstructiblePoint {0, 1} := by
    apply constructiblePoint_insert
    apply ConstructiblePoint.twoCircles ⟨0, 1⟩ ⟨1, 1⟩
    · apply ConstructibleCircle.centerRadius _ 1 (ConstructiblePoint.given 0 (by simp))
        (ConstructiblePoint.given 1 (by simp))
      simp [EuclideanGeometry.mem_sphere]
    · apply ConstructibleCircle.centerRadius _ 0 (ConstructiblePoint.given 1 (by simp))
        (ConstructiblePoint.given 0 (by simp))
      simp [EuclideanGeometry.mem_sphere]
    · simp
    · rw [mem_sphere, dist_zero_right, hnorm]
    · rw [mem_sphere, Complex.dist_eq, ← sq_eq_sq₀ (by simp) (by simp), Complex.sq_norm]
      suffices (2⁻¹ - 1) * (2⁻¹ - 1) + 2⁻¹ * √3 * (2⁻¹ * √3) = 1 by simpa [Complex.normSq]
      grind
  simp_rw [ConstructiblePoint.map_iff e, hinit, hcons,
    ← AffineIsometry.angle_map e.toAffineIsometry,
    AffineIsometryEquiv.coe_toAffineIsometry, hp₁, hp₂, hp₃]
  have hangle : ∠ (2⁻¹ + 2⁻¹ * √3 * Complex.I) 0 1 = π / 3 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle]
    simp [hnorm]
  rw [hangle]
  intro ha hb hc hangle
  rw [mul_comm 3, ← eq_div_iff_mul_eq (by simp), div_div, (show 3 * 3 = (9 : ℝ) by norm_num)]
    at hangle
  set a := e q₁
  set b := e q₂
  set c := e q₃
  have hcbne : c ≠ b := by
    intro h
    rw [h, angle_self_right] at hangle
    rw [div_eq_div_iff (by simp) (by simp)] at hangle
    have hangle : 7 * π = 0 := by linear_combination hangle
    simp at hangle
  have habne : a ≠ b := by
    intro h
    rw [h, angle_self_left] at hangle
    rw [div_eq_div_iff (by simp) (by simp)] at hangle
    have hangle : 7 * π = 0 := by linear_combination hangle
    simp at hangle
  have hcb0 : ‖c - b‖ ≠ 0 := by
    intro h
    have : c = b := by simpa [sub_eq_zero] using h
    exact hcbne this
  have hab0 : ‖a - b‖ ≠ 0 := by
    intro h
    have : a = b := by simpa [sub_eq_zero] using h
    exact habne this
  set d := ‖a - b‖ / ‖c - b‖ * (c - b) + b
  have hdbne : d ≠ b := by simp [d, sub_eq_zero, habne, hcbne]
  have hd : ConstructiblePoint {0, 1} d := by
    apply ConstructiblePoint.lineCircle line[ℝ, c, b] ⟨b, ‖a - b‖⟩
    · apply ConstructibleLine.twoPoints c b hc hb hcbne
      · exact left_mem_affineSpan_pair ℝ c b
      · exact right_mem_affineSpan_pair ℝ c b
      · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton]
        rw [vsub_eq_zero_iff_eq.ne]
        exact hcbne
    · apply ConstructibleCircle.centerRadius _ a hb ha
      simp [mem_sphere, dist_eq_norm]
    · suffices (‖a - b‖ / ‖c - b‖) • (c -ᵥ b) +ᵥ b ∈ line[ℝ, c, b] by
        simpa using this
      apply vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan
      · apply right_mem_affineSpan_pair
      · apply smul_vsub_mem_vectorSpan_pair
    · simp [d, mem_sphere, hcb0]
  have habd : ∠ a b c = ∠ a b d := by
    apply angle_smul_right_of_pos _ (show 0 < (‖c - b‖ / ‖a - b‖) by
      apply div_pos
      · simpa using hcb0
      · simpa using hab0
    )
    suffices ‖c - b‖ / ‖a - b‖ * (‖a - b‖ / ‖c - b‖ * (c - b)) = c - b by simpa [d]
    rw [← mul_assoc, ← mul_div_assoc, div_mul_cancel₀ _ (by simpa using hab0),
      div_self (by simpa using hcb0), one_mul]
  rw [habd, EuclideanGeometry.angle,
    Complex.angle_eq_abs_arg (by simpa [sub_eq_zero] using habne)
    (by simpa [sub_eq_zero] using hdbne), vsub_eq_sub, vsub_eq_sub] at hangle
  set w := (a - b) / (d - b)
  have hwnorm : ‖w‖ = 1 := by simp [w, d, hcb0, hab0]
  have hwre : w.re = Real.cos (π / 9) := by
    rw [← Complex.norm_mul_exp_arg_mul_I w, hwnorm,
      Complex.ofReal_one, one_mul, Complex.exp_ofReal_mul_I_re]
    rcases abs_cases w.arg with ⟨hw, _⟩ | ⟨hw, _⟩
    · rw [← hw, hangle]
    · rw [← hangle, hw, Real.cos_neg]
  have hstar : ∀ x ∈ ({0, 1} : Set ℂ), conj x ∈ ({0, 1} : Set ℂ) := by simp
  have ha := ConstructiblePoint.mem_constructibleClosure hstar ha
  have hb := ConstructiblePoint.mem_constructibleClosure hstar hb
  have hd := ConstructiblePoint.mem_constructibleClosure hstar hd
  have hw : w ∈ constructibleClosure (Subfield.closure ({0, 1} : Set ℂ)) ℂ :=
    div_mem (sub_mem ha hb) (sub_mem hd hb)
  have hwremem : w.re ∈ constructibleClosure (Subfield.closure ({0, 1} : Set ℝ)) ℝ := by
    rw [← re_im_image_01]
    exact re_mem_constructibleClosure hw
  rw [Subfield.closrue_01] at hwremem
  have hquad : (minpoly (⊥ : Subfield ℝ) w.re).natDegree.isPowerOfTwo :=
    isPowerOfTwo_natDegree_minpoly_of_mem_constructibleClosure hwremem
  let p : Polynomial (⊥ : Subfield ℝ) :=
    8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1
  have hp : Irreducible p := by
    suffices Irreducible (Polynomial.mapEquiv ratEquivBot
        (8 * Polynomial.X ^ 3 - 6 * Polynomial.X - 1)) by
      convert this
      simp [p]
    exact Irreducible.map _ irreducible_861
  have hwp : minpoly (⊥ : Subfield ℝ) w.re ∣ p := by
    apply minpoly.dvd
    suffices 8 * Real.cos (π / 9) ^ 3 - 6 * Real.cos (π / 9) - 1 = 0 by simpa [p, hwre, map_ofNat]
    suffices 2 * (4 * Real.cos (π / 9) ^ 3 - 3 * Real.cos (π / 9)) - 1 = 0 by
      linear_combination this
    rw [← Real.cos_three_mul, show 3 * (π / 9) = π / 3 by ring]
    simp
  have hminpoly : (minpoly (⊥ : Subfield ℝ) w.re).natDegree = 3 := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Irreducible.dvd_iff hp] at hwp
    rw [← Polynomial.degree_eq_degree_of_associated <| Or.resolve_left hwp (minpoly.not_isUnit _ _)]
    unfold p
    compute_degree!
  rw [hminpoly] at hquad
  contrapose! hquad
  decide

theorem dist_homothety_homothety {V : Type*} {P : Type*}
    [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V]
    (c : P) (r : 𝕜) (a b : P) :
    dist (AffineMap.homothety c r a) (AffineMap.homothety c r b) = ‖r‖ * dist a b := by
  simp_rw [dist_eq_norm_vsub, AffineMap.homothety_apply, vadd_vsub_vadd_cancel_right,
    ← smul_sub, norm_smul, vsub_sub_vsub_cancel_right]

theorem not_exist_doubling_cube {a b : P} (h : a ≠ b) :
    ¬ ∃ c d : P, ConstructiblePoint {a, b} c ∧ ConstructiblePoint {a, b} d ∧
    dist c d ^ 3 = 2 * dist a b ^ 3 := by
  classical
  push Not
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  have hab : ‖b -ᵥ a‖ ≠ 0 := by simpa using h.symm
  have hab' : ‖b -ᵥ a‖⁻¹ ≠ 0 := by simpa using h.symm
  intro c d hc hd hdist
  have hc := hc.map_homothety a hab'
  have hd := hd.map_homothety a hab'
  have hinit : (AffineMap.homothety a ‖b -ᵥ a‖⁻¹) '' {a, b} =
      {a, ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) +ᵥ a} := by
    rw [Set.image_pair]
    simp [AffineMap.homothety_apply]
  rw [hinit] at hc hd
  let v : Set V := {‖b -ᵥ a‖⁻¹ • (b -ᵥ a)}
  have hv : Orthonormal ℝ ((↑) : v → V) := by
    rw [orthonormal_subsingleton_iff]
    simp [v, norm_smul, hab]
  obtain ⟨u, basis, hvu, hbasis⟩ := Orthonormal.exists_orthonormalBasis_extension hv
  have hfilter : (u.filter (· ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card = 1 := by
    have h1 : ((u.filter (¬ · ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card) = 1 := by
      rw [Finset.card_eq_one]
      use ‖b -ᵥ a‖⁻¹ • (b -ᵥ a)
      grind
    suffices (u.filter (· ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card +
      ((u.filter (¬ · ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a))).card) = 2 by
      rw [h1] at this
      grind
    rw [Finset.card_filter_add_card_filter_not]
    rw [← Module.finrank_eq_card_finset_basis basis.toBasis]
    exact hrank.out
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hfilter
  obtain ⟨hjmem, hjne⟩ : j ∈ u ∧ j ≠ ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) := by simpa using hj.ge
  have hmemu : ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) ∈ u := by
    apply Set.mem_of_subset_of_mem hvu
    simp [v]
  let ie : u ≃ Fin 2 := {
    toFun i := if i = ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) then 0 else 1
    invFun := ![⟨‖b -ᵥ a‖⁻¹ • (b -ᵥ a), hmemu⟩, ⟨j, hjmem⟩]
    left_inv i := by
      by_cases hi : i = ‖b -ᵥ a‖⁻¹ • (b -ᵥ a)
      · ext
        simp [hi]
      · ext
        suffices j = i by simpa [hi]
        symm
        suffices i.val ∈ ({j} : Finset _) by simpa
        rw [← hj]
        simp [hi]
    right_inv i := by
      fin_cases i
      · simp
      · simpa using hjne
  }
  have hbasis0 : basis ⟨‖b -ᵥ a‖⁻¹ • (b -ᵥ a), hmemu⟩ = ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) := by
    simp [hbasis]
  let e : P ≃ᵃⁱ[ℝ] ℂ :=
    (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
    (basis.equiv Complex.orthonormalBasisOneI ie).toAffineIsometryEquiv
  rw [ConstructiblePoint.map_iff e] at hc hd
  have hinit' : e '' {a, ‖b -ᵥ a‖⁻¹ • (b -ᵥ a) +ᵥ a} = {0, 1} := by
    rw [Set.image_pair]
    congrm {?_, ?_}
    · simp [e]
    simp_rw [e, AffineIsometryEquiv.trans_apply, AffineIsometryEquiv.coe_vaddConst_symm,
      vadd_vsub, LinearIsometryEquiv.coe_toAffineIsometryEquiv]
    rw [← hbasis0, OrthonormalBasis.equiv_apply_basis]
    simp [ie]
  rw [hinit'] at hc hd
  set c' := e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ c)
  set d' := e (AffineMap.homothety a ‖b -ᵥ a‖⁻¹ d)
  have hstar : ∀ x ∈ ({0, 1} : Set ℂ), conj x ∈ ({0, 1} : Set ℂ) := by simp
  have hc' := hc.mem_constructibleClosure hstar
  have hd' := hd.mem_constructibleClosure hstar
  have hcd : dist c' d' ∈ constructibleClosure (Subfield.closure ({0, 1} : Set ℝ)) ℝ := by
    rw [dist_eq_norm_sub]
    rw [← re_im_image_01]
    apply norm_mem_constructibleClosure
    exact sub_mem hc' hd'
  rw [Subfield.closrue_01] at hcd
  have hquad : (minpoly (⊥ : Subfield ℝ) (dist c' d')).natDegree.isPowerOfTwo :=
    isPowerOfTwo_natDegree_minpoly_of_mem_constructibleClosure hcd
  have hdist : dist c' d' ^ 3 = 2 := by
    simp_rw [c', d', Isometry.dist_eq (e.isometry), dist_homothety_homothety]
    rw [mul_pow, hdist, dist_eq_norm_vsub', norm_inv, norm_norm, inv_pow]
    rw [mul_comm 2, inv_mul_cancel_left₀ (by simpa using h.symm)]
  let p : Polynomial (⊥ : Subfield ℝ) := Polynomial.X ^ 3 - 2
  have hp : Irreducible p := by
    suffices Irreducible (Polynomial.mapEquiv ratEquivBot
        (Polynomial.X ^ 3 - 2)) by
      convert this
      simp [p]
    exact Irreducible.map _ irreducible_cube_2
  have hwp : minpoly (⊥ : Subfield ℝ) (dist c' d') ∣ p := by
    apply minpoly.dvd
    simp [p, hdist, map_ofNat]
  have hminpoly : (minpoly (⊥ : Subfield ℝ) (dist c' d')).natDegree = 3 := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Irreducible.dvd_iff hp] at hwp
    rw [← Polynomial.degree_eq_degree_of_associated <| Or.resolve_left hwp (minpoly.not_isUnit _ _)]
    unfold p
    compute_degree!
  rw [hminpoly] at hquad
  contrapose! hquad
  decide

end EuclideanGeometry
