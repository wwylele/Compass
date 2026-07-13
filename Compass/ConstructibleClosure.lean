module

public import Mathlib
import all Init.Data.Nat.Power2.Basic

public section

open ComplexConjugate

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace IntermediateField

-- By Aristotle
lemma relrank_le_relrank_of_le_left {A B C : IntermediateField K L} (h : A ≤ B) :
    B.relrank C ≤ A.relrank C := by
  rw [← relrank_inf_mul_relrank_of_le C h]
  refine le_mul_of_one_le_left' ?_
  rw [← inf_relrank_right A (B ⊓ C), relrank_eq_rank_of_le (inf_le_right : A ⊓ (B ⊓ C) ≤ B ⊓ C)]
  exact Cardinal.one_le_iff_ne_zero.mpr (rank_pos (R := ↥(A ⊓ (B ⊓ C)))).ne'

-- By Aristotle
lemma relrank_sup_left_le (M B : IntermediateField K L)
    (h : M.relrank B < Cardinal.aleph0) :
    M.relrank (M ⊔ B) ≤ M.relrank B := by
  have hInfB : (M ⊓ B : IntermediateField K L) ≤ B := inf_le_right
  -- Identify `M.relrank B` with the rank of `B` over `M ⊓ B`.
  have hRB : M.relrank B = Module.rank ↥(M ⊓ B) ↥(extendScalars hInfB) := by
    rw [← inf_relrank_right M B, relrank_eq_rank_of_le hInfB]
  -- Finiteness of the extension gives algebraicity.
  have hfin : Module.rank ↥(M ⊓ B) ↥(extendScalars hInfB) < Cardinal.aleph0 := hRB ▸ h
  have : Module.Free ↥(M ⊓ B) ↥(extendScalars hInfB) := by
    apply Module.Free.of_divisionRing
  haveI : Module.Finite ↥(M ⊓ B) ↥(extendScalars hInfB) := Module.rank_lt_aleph0_iff.mp hfin
  haveI : Algebra.IsAlgebraic ↥(M ⊓ B) ↥(extendScalars hInfB) :=
    Algebra.IsAlgebraic.of_finite _ _
  -- Set up the field tower `(M ⊓ B) → M → L`.
  letI : Algebra ↥(M ⊓ B) ↥M := (inclusion (inf_le_left : M ⊓ B ≤ M)).toAlgebra
  haveI : IsScalarTower ↥(M ⊓ B) ↥M L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- The compositum degree bound for algebraic extensions.
  have key := adjoin_rank_le_of_isAlgebraic_right (F := ↥(M ⊓ B)) (E := ↥M) (K := L)
    (extendScalars hInfB)
  rw [← hRB] at key
  -- Identify `adjoin M ↑B` with `extendScalars (M ≤ M ⊔ B)`.
  have hadj : adjoin ↥M (↑(extendScalars hInfB) : Set L)
      = extendScalars (le_sup_left : M ≤ M ⊔ B) := by
    apply restrictScalars_injective K
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup, coe_extendScalars,
      adjoin_self]
  rw [hadj] at key
  rwa [relrank_eq_rank_of_le (le_sup_left : M ≤ M ⊔ B)]

-- By Aristotle
theorem relrank_sup (e f g : IntermediateField K L)
    (hef : e.relrank f < Cardinal.aleph0) :
    (e ⊔ g).relrank (f ⊔ g) ≤ e.relrank f := by
  set M : IntermediateField K L := (e ⊓ f) ⊔ g with hM
  -- `f ⊔ g` is the compositum of `M` and `f`.
  have hMf : M ⊔ f = f ⊔ g := by
    rw [hM, sup_assoc, sup_comm g f, ← sup_assoc, sup_eq_right.mpr (inf_le_right : e ⊓ f ≤ f)]
  -- `(e ⊓ f).relrank f = e.relrank f`.
  have hinf : (e ⊓ f).relrank f = e.relrank f := inf_relrank_right e f
  -- monotonicity: `M.relrank f ≤ (e ⊓ f).relrank f`.
  have h3 : M.relrank f ≤ (e ⊓ f).relrank f :=
    relrank_le_relrank_of_le_left (by rw [hM]; exact le_sup_left)
  -- hence `M.relrank f` is finite, so the core bound applies.
  have hMfin : M.relrank f < Cardinal.aleph0 := lt_of_le_of_lt (h3.trans_eq hinf) hef
  have h2 : M.relrank (M ⊔ f) ≤ M.relrank f := relrank_sup_left_le M f hMfin
  -- monotonicity: `(e ⊔ g).relrank (f ⊔ g) ≤ M.relrank (f ⊔ g)`.
  have h1 : (e ⊔ g).relrank (f ⊔ g) ≤ M.relrank (f ⊔ g) :=
    relrank_le_relrank_of_le_left (by rw [hM]; exact sup_le_sup_right inf_le_left g)
  calc
    (e ⊔ g).relrank (f ⊔ g) ≤ M.relrank (f ⊔ g) := h1
    _ = M.relrank (M ⊔ f) := by rw [hMf]
    _ ≤ M.relrank f := h2
    _ ≤ (e ⊓ f).relrank f := h3
    _ = e.relrank f := hinf

instance [StarRing K] [StarRing L] [StarModule K L] : Star (IntermediateField K L) where
  star f := {
    __ := star f.toSubalgebra
    inv_mem' x := by simp
  }

@[simp]
theorem coe_star [StarRing K] [StarRing L] [StarModule K L] (f : IntermediateField K L) :
    (star f : Set L) = star (f : Set L) :=
  rfl

@[simp]
theorem mem_star_iff [StarRing K] [StarRing L] [StarModule K L] (f : IntermediateField K L)
    (x : L) :
    x ∈ star f ↔ star x ∈ f := by
  rfl

theorem star_mono [StarRing K] [StarRing L] [StarModule K L] :
    Monotone (star : IntermediateField K L → IntermediateField K L) := by
  intro f g h
  apply Subalgebra.star_mono h

@[simp]
theorem star_bot [StarRing K] [StarRing L] [StarModule K L] :
    star (⊥ : IntermediateField K L) = ⊥ := by
  ext x
  simp only [mem_star_iff, mem_bot, Set.mem_range]
  exact ⟨fun ⟨y, h⟩ ↦ ⟨star y, by simp [h]⟩, fun ⟨y, h⟩ ↦ ⟨star y, by simp [h]⟩⟩

end IntermediateField

inductive IsIteratedQuadraticExtension : IntermediateField K L → Prop
| bot : IsIteratedQuadraticExtension ⊥
| extension (f g : IntermediateField K L) (hf : IsIteratedQuadraticExtension f)
    (hfg : f ≤ g) (hg : IntermediateField.relrank f g = 2) :
    IsIteratedQuadraticExtension g

theorem IsIteratedQuadraticExtension.induction (P : IntermediateField K L → Prop)
    (bot : P ⊥)
    (extension : ∀ f g : IntermediateField K L, IsIteratedQuadraticExtension f → f ≤ g
      → IntermediateField.relrank f g = 2 → P f → P g)
    {f : IntermediateField K L} (hf : IsIteratedQuadraticExtension f) : P f :=
match hf with
| IsIteratedQuadraticExtension.bot => by simpa using bot
| IsIteratedQuadraticExtension.extension e f he hef h => by
  apply extension _ _ he hef h
  apply IsIteratedQuadraticExtension.induction P bot extension he

theorem IsIteratedQuadraticExtension.isPowerOfTwo_finrank {f : IntermediateField K L}
    (hf : IsIteratedQuadraticExtension f) :
    (Module.finrank K f).isPowerOfTwo :=
match hf with
| IsIteratedQuadraticExtension.bot => by
  simpa using Nat.isPowerOfTwo_one
| IsIteratedQuadraticExtension.extension e f he hef h => by
  rw [← IntermediateField.finrank_bot_mul_relfinrank hef,
    IntermediateField.relfinrank_eq_toNat_relrank e f, h, Cardinal.toNat_ofNat]
  exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo he.isPowerOfTwo_finrank

theorem Nat.isPowerOfTwo.dvd {m n : ℕ} (h : n.isPowerOfTwo) (hdvd : m ∣ n) :
    m.isPowerOfTwo := by
  obtain ⟨k, hk⟩ := h
  rw [hk] at hdvd
  rw [Nat.dvd_prime_pow prime_two] at hdvd
  obtain ⟨l, _, hl⟩ := hdvd
  exact ⟨l, hl⟩

theorem IsIteratedQuadraticExtension.isPowerOfTwo_natDegree_minpoly {f : IntermediateField K L}
    (hf : IsIteratedQuadraticExtension f) {x : L} (hx : x ∈ f) :
    (minpoly K x).natDegree.isPowerOfTwo := by
  have h2 := hf.isPowerOfTwo_finrank
  have : Module.Finite K f := by
    apply Module.finite_of_finrank_pos
    obtain ⟨n, hn⟩ := h2
    simp [hn]
  have hdvd : (minpoly K (⟨x, hx⟩ : f)).natDegree ∣ Module.finrank K f :=
    minpoly.degree_dvd (IsAlgebraic.of_finite K (⟨x, hx⟩ : f)).isIntegral
  have hminpoly : minpoly K x = minpoly K (⟨x, hx⟩ : f) := by
    trans minpoly K (algebraMap f L (⟨x, hx⟩ : f))
    · simp
    apply minpoly.algebraMap_eq
    exact FaithfulSMul.algebraMap_injective (↥f) L
  rw [← hminpoly] at hdvd
  exact h2.dvd hdvd

theorem IsIteratedQuadraticExtension.mem_induction (h0 : (2 : L) ≠ 0)
    (P : L → Prop)
    (bot : ∀ x : K, P (algebraMap K L x))
    (add : ∀ x y, P x → P y → P (x + y))
    (inv : ∀ x, P x → P x⁻¹)
    (mul : ∀ x y, P x → P y → P (x * y))
    (sqrt : ∀ x, P (x ^ 2) → P x)
    {f : IntermediateField K L} (hf : IsIteratedQuadraticExtension f) : ∀ x ∈ f, P x := by
  have hbot : ∀ x ∈ (⊥ : IntermediateField K L), P x := by
    intro x hx
    rw [IntermediateField.mem_bot, Set.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    apply bot
  refine IsIteratedQuadraticExtension.induction (fun f ↦ ∀ x ∈ f, P x) hbot ?_ hf
  intro f g hf hfg hg ih
  suffices ∀ x ∈ (⊤ : IntermediateField ↥f ↥(IntermediateField.extendScalars hfg)), P x by
    intro x hx
    apply this ⟨x, by simpa using hx⟩
    simp
  rw [IntermediateField.relrank_eq_rank_of_le hfg] at hg
  have : Module.Finite f (IntermediateField.extendScalars hfg) :=
    Module.finite_of_rank_eq_nat hg
  have : Module.Free f (IntermediateField.extendScalars hfg) := by
    apply Module.Free.of_divisionRing
  have : Algebra.IsSeparable f (IntermediateField.extendScalars hfg) := by
    rw [Algebra.isSeparable_def]
    intro a
    have hint : IsIntegral f a := (IsAlgebraic.of_finite f a).isIntegral
    have : (minpoly f a).natDegree ≤ 2 := by
      apply (minpoly.natDegree_le a).trans_eq
      rw [Module.finrank_eq_of_rank_eq hg]
    have : 0 < (minpoly f a).natDegree := minpoly.natDegree_pos hint
    set d := (minpoly f a).natDegree
    interval_cases hd : d
    · have : (minpoly f a).IsMonicOfDegree 1 := ⟨hd, minpoly.monic hint⟩
      obtain ⟨r, h⟩ := Polynomial.isMonicOfDegree_one_iff.mp this
      rw [IsSeparable, h]
      exact Polynomial.separable_X_add_C r
    · have : (minpoly f a).IsMonicOfDegree 2 := ⟨hd, minpoly.monic hint⟩
      obtain ⟨r, s, h⟩ := Polynomial.isMonicOfDegree_two_iff.mp this
      rw [IsSeparable]
      rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
      suffices (1 + 1) * Polynomial.X + Polynomial.C r ≠ 0 by simpa [h]
      rw [show (1 + 1) = (2 : Polynomial ↥f) by norm_num]
      intro h
      contrapose h0
      obtain h := congr((Polynomial.coeff $h 1))
      have h : (2 : f) = 0 := by simpa using h
      obtain h := congr(($h).val)
      push_cast at h
      exact h
  obtain ⟨a, ha⟩ := Field.exists_primitive_element f (IntermediateField.extendScalars hfg)
  rw [← ha]
  apply IntermediateField.adjoin_induction
  · suffices P a by simpa
    have hint : IsIntegral f a := (IsAlgebraic.of_finite f a).isIntegral
    have : (minpoly f a).natDegree ≤ 2 := by
      apply (minpoly.natDegree_le a).trans_eq
      rw [Module.finrank_eq_of_rank_eq hg]
    have : 0 < (minpoly f a).natDegree := minpoly.natDegree_pos hint
    set d := (minpoly f a).natDegree
    interval_cases hd : d
    · have : (minpoly f a).IsMonicOfDegree 1 := ⟨hd, minpoly.monic hint⟩
      obtain ⟨r, h⟩ := Polynomial.isMonicOfDegree_one_iff.mp this
      have heval := minpoly.aeval f a
      rw [h, Subtype.ext_iff] at heval
      have : a.val + r.val = 0 := by simpa using! heval
      have : a.val = (-1) * r.val := by
        linear_combination this
      rw [this]
      apply mul
      · apply hbot
        simp
      · exact ih r r.prop
    · have : (minpoly f a).IsMonicOfDegree 2 := ⟨hd, minpoly.monic hint⟩
      obtain ⟨r, s, h⟩ := Polynomial.isMonicOfDegree_two_iff.mp this
      have heval := minpoly.aeval f a
      rw [h, Subtype.ext_iff] at heval
      have : (a.val) ^ 2 + r.val * a.val + s.val = 0 := by
        simpa [-Algebra.mul_smul_comm] using! heval
      have : (2 * a.val + r.val) ^ 2 = r.val ^ 2 - 4 * s.val := by
        linear_combination 4 * this
      have : (2 * a.val + r.val) ^ 2 = (r ^ 2 - 4 * s).val := this
      have hP : P (2 * a.val + r.val) := by
        apply sqrt
        rw [this]
        exact ih _ (r ^ 2 - 4 * s).prop
      have : a.val = 2⁻¹ * (2 * a.val + r.val + (-1) * r.val) := by
        rw [neg_one_mul, ← sub_eq_add_neg, add_sub_cancel_right]
        rw [inv_mul_cancel_left₀ h0]
      rw [this]
      apply mul
      · apply inv
        exact ih _ (by simp)
      · apply add
        · exact hP
        · apply mul
          · exact ih _ (by simp)
          · exact ih r r.prop
  · intro x
    simpa using ih x x.prop
  · intro x y hx hy hpx hpy
    exact add x y hpx hpy
  · intro x hx hpx
    exact inv x hpx
  · intro x y hx hy hpx hpy
    exact mul x y hpx hpy

theorem IsIteratedQuadraticExtension.extension'
    {f g : IntermediateField K L} (hf : IsIteratedQuadraticExtension f)
    (hfg : f ≤ g) (hg : IntermediateField.relrank f g ≤ 2) :
    IsIteratedQuadraticExtension g := by
  obtain h := Cardinal.toNat_le_toNat hg (by simp)
  rw [Cardinal.toNat_ofNat] at h
  interval_cases hrank : (f.relrank g).toNat
  · -- to extract: rel rank ne zero
    by_contra
    obtain h := congr(($hrank : Cardinal))
    rw [Cardinal.cast_toNat_of_lt_aleph0 (lt_of_le_of_lt hg (by simp))] at h
    rw [IntermediateField.relrank_eq_rank_of_le hfg] at h
    have hg : Subsingleton g := by simpa [Module.rank_zero_iff_of_free] using h
    apply not_isField_of_subsingleton g (Field.toIsField g)
  · rw [← IntermediateField.relfinrank_eq_toNat_relrank,
      IntermediateField.relfinrank_eq_one_iff] at hrank
    rw [le_antisymm hrank hfg]
    exact hf
  · apply IsIteratedQuadraticExtension.extension f g hf hfg
    obtain h := congr(($hrank : Cardinal))
    rw [Cardinal.cast_toNat_of_lt_aleph0 (lt_of_le_of_lt hg (by simp))] at h
    simpa using h

theorem IsIteratedQuadraticExtension.sup {f g : IntermediateField K L}
    (hf : IsIteratedQuadraticExtension f) (hg : IsIteratedQuadraticExtension g) :
    IsIteratedQuadraticExtension (f ⊔ g) :=
match hf with
| IsIteratedQuadraticExtension.bot => by simpa using hg
| IsIteratedQuadraticExtension.extension e f he hef h => by
  apply IsIteratedQuadraticExtension.extension' (he.sup hg) (sup_le_sup_right hef g)
  rw [← h]
  apply IntermediateField.relrank_sup
  simp [h]

theorem IsIteratedQuadraticExtension.finsetSup {ι : Type*} (s : Finset ι)
    (f : ι → IntermediateField K L) (h : ∀ i ∈ s, IsIteratedQuadraticExtension (f i)) :
    IsIteratedQuadraticExtension (s.sup f) := by
  induction s using Finset.cons_induction with
  | empty =>
    simpa using IsIteratedQuadraticExtension.bot
  | cons a s has ih =>
    rw [Finset.sup_cons]
    apply IsIteratedQuadraticExtension.sup
    · apply h
      simp
    apply ih
    intro i hi
    apply h
    simp [hi]

variable (K L) in
def constructibleClosure : IntermediateField K L :=
    ⨆ (f : IntermediateField K L) (_ : IsIteratedQuadraticExtension f), f

theorem mem_constructibleClosure {x : L} :
    x ∈ constructibleClosure K L ↔
    ∃ f : IntermediateField K L, IsIteratedQuadraticExtension f ∧ x ∈ f where
  mp h := by
    obtain ⟨s, h⟩ := IntermediateField.exists_finset_of_mem_iSup h
    refine ⟨_, ?_, h⟩
    rw [← Finset.sup_eq_iSup]
    apply IsIteratedQuadraticExtension.finsetSup
    intro i _
    by_cases h : IsIteratedQuadraticExtension i
    · simp [h]
    · simpa [h] using IsIteratedQuadraticExtension.bot
  mpr h := by
    obtain ⟨f, hf, hx⟩ := h
    apply SetLike.mem_of_subset ?_ hx
    rw [SetLike.coe_subset_coe]
    apply le_iSup_of_le f
    simp [hf]

theorem isPowerOfTwo_natDegree_minpoly_of_mem_constructibleClosure
    {x : L} (hx : x ∈ constructibleClosure K L) :
    (minpoly K x).natDegree.isPowerOfTwo := by
  obtain ⟨f, hf, hx⟩ := mem_constructibleClosure.mp hx
  exact hf.isPowerOfTwo_natDegree_minpoly hx

theorem mem_constructibleClosure_of_mem_subfield {x : L} {K : Subfield L} (h : x ∈ K) :
    x ∈ constructibleClosure K L := by
  refine Set.mem_of_mem_of_subset ?_ <| SetLike.coe_subset_coe.mpr bot_le
  rw [SetLike.mem_coe, IntermediateField.mem_bot, Set.mem_range]
  exact ⟨⟨x, h⟩, (by simp [Subfield.algebraMap_ofSubfield])⟩

theorem mem_constructibleClosure_of_sq_mem {x : L} (hx : x ^ 2 ∈ constructibleClosure K L) :
    x ∈ constructibleClosure K L := by
  rw [mem_constructibleClosure] at ⊢ hx
  obtain ⟨f, hf, hx⟩ := hx
  have halg : IsAlgebraic f x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨x ^ 2, hx⟩, fun h ↦ ?_, by simp⟩
    obtain h := congr(Polynomial.coeff $h 2)
    simp at h
  have hint := halg.isIntegral
  have hle : f ≤ IntermediateField.adjoin K (f ∪ {x}) := by
    rw [← SetLike.coe_subset_coe]
    exact Set.subset_union_left.trans (IntermediateField.subset_adjoin K (f ∪ {x}))
  refine ⟨IntermediateField.adjoin K (f ∪ {x}), ?_, ?_⟩
  · refine IsIteratedQuadraticExtension.extension' hf hle ?_
    rw [IntermediateField.relrank_eq_rank_of_le hle, IntermediateField.extendScalars_adjoin]
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_eq_bot_iff.mpr (by
      intro x
      simp [IntermediateField.mem_bot]), bot_sup_eq]
    rw [← Cardinal.toNat_le_iff_le_of_lt_aleph0 (by
      rw [Module.rank_lt_aleph0_iff]
      apply IntermediateField.finiteDimensional_adjoin
      simpa using hint
    ) (by simp)]
    rw [← Module.finrank, IntermediateField.adjoin.finrank hint]
    let p : Polynomial f := Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩)
    have hp : p.aeval x = 0 := by simp [p]
    have hp0 : p ≠ 0 := fun h ↦ by
      obtain h := congr(Polynomial.coeff $h 2)
      simp [p, -map_mul] at h
    convert ← Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hp) hp0
    simp_rw [Cardinal.toNat_ofNat, p]
    compute_degree!
  · apply IntermediateField.mem_adjoin_of_mem
    simp

theorem constructibleClosure_induction (h0 : (2 : L) ≠ 0)
    (P : L → Prop)
    (bot : ∀ x : K, P (algebraMap K L x))
    (add : ∀ x y, P x → P y → P (x + y))
    (inv : ∀ x, P x → P x⁻¹)
    (mul : ∀ x y, P x → P y → P (x * y))
    (sqrt : ∀ x, P (x ^ 2) → P x) :
    ∀ x ∈ constructibleClosure K L, P x := by
  intro x hx
  rw [mem_constructibleClosure] at hx
  obtain ⟨f, hf, hx⟩ := hx
  exact hf.mem_induction h0 P bot add inv mul sqrt x hx

theorem constructibleClosure_closure_induction (h0 : (2 : L) ≠ 0) {s : Set L}
    {P : L → Prop}
    (mem : ∀ x ∈ s, P x)
    (one : P 1)
    (add : ∀ x y, P x → P y → P (x + y))
    (neg : ∀ x, P x → P (-x))
    (inv : ∀ x, P x → P x⁻¹)
    (mul : ∀ x y, P x → P y → P (x * y))
    (sqrt : ∀ x, P (x ^ 2) → P x) :
    ∀ x ∈ constructibleClosure (Subfield.closure s) L, P x := by
  refine constructibleClosure_induction h0 P ?_ add inv mul sqrt
  intro x
  obtain ⟨x, hx⟩ := x
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    exact mem x hx
  | one =>
    exact one
  | add x y hx hy hpx hpy =>
    exact add x y hpx hpy
  | neg x hx hpx =>
    exact neg x hpx
  | inv x hx hpx =>
    exact inv x hpx
  | mul x y hx hy hpx hpy =>
    exact mul x y hpx hpy

open Polynomial in
theorem Complex.sq_eq_iff {a b : ℂ} :
    a ^ 2 = b ↔ a = Complex.sqrt b ∨ a = -Complex.sqrt b where
  mp h := by
    let p : Polynomial ℂ := C 1 * X ^ 2 + C 0 * X + C (-b)
    have hp0 : p ≠ 0 := by
      intro h
      obtain h := congr(Polynomial.coeff $h 2)
      simp [p] at h
    have hp : a ∈ p.roots := by
      rw [mem_roots hp0]
      simp [p, h]
    suffices p.roots = {b.sqrt, -b.sqrt} by
      simpa [this] using hp
    rw [Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero' (by simp)]
    suffices b.sqrt * b.sqrt = b by simpa
    rw [← sq, sqrt]
    simp
  mpr h := by
    rcases h with h | h
    · simp [h, Complex.sqrt]
    · simp [h, Complex.sqrt]

theorem Complex.sqrt_eq_real_add_ite' {a : ℂ} :
    a.sqrt = √((‖a‖ + a.re) / 2) +
    ((if 0 ≤ a.im then 1 else -1) * √((‖a‖ - a.re) / 2) : ℝ) * I := by
  convert Complex.sqrt_eq_real_add_ite
  split_ifs
  all_goals
  norm_cast

theorem Complex.re_sq_of_sq_eq {a b : ℂ} (h : a ^ 2 = b) :
    a.re ^ 2 = (‖b‖ + b.re) / 2 := by
  rw [Complex.sq_eq_iff] at h
  have : b.sqrt.re ^ 2 = (‖b‖ + b.re) / 2 := by
    rw [Complex.sqrt_eq_real_add_ite', Complex.add_re]
    rw [Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
    rw [Real.sq_sqrt]
    refine div_nonneg ?_ (by simp)
    simpa [neg_le_iff_add_nonneg] using Complex.re_le_norm (-b)
  rcases h with h | h
  · rw [h]
    exact this
  · rw [h, Complex.neg_re, neg_sq]
    exact this

theorem Complex.im_sq_of_sq_eq {a b : ℂ} (h : a ^ 2 = b) :
    a.im ^ 2 = (‖b‖ - b.re) / 2 := by
  rw [Complex.sq_eq_iff] at h
  have : b.sqrt.im ^ 2 = (‖b‖ - b.re) / 2 := by
    rw [Complex.sqrt_eq_real_add_ite', Complex.add_im]
    rw [Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add,
      mul_pow, ite_pow, Real.sq_sqrt]
    · simp
    refine div_nonneg ?_ (by simp)
    simpa using Complex.re_le_norm b
  rcases h with h | h
  · rw [h]
    exact this
  · rw [h, Complex.neg_im, neg_sq]
    exact this

theorem re_im_subset_constructibleClosure {s : Set ℂ} {x : ℂ}
    (h : x ∈ constructibleClosure (Subfield.closure s) ℂ) :
    x.re ∈ constructibleClosure (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ ∧
    x.im ∈ constructibleClosure (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ := by
  revert h
  apply constructibleClosure_closure_induction
  · simp
  · intro x hx
    constructor
    · apply mem_constructibleClosure_of_mem_subfield
      apply Subfield.mem_closure_of_mem
      grind
    · apply mem_constructibleClosure_of_mem_subfield
      apply Subfield.mem_closure_of_mem
      grind
  · constructor
    · apply mem_constructibleClosure_of_mem_subfield
      simp
    · apply mem_constructibleClosure_of_mem_subfield
      simp
  · intro x y ⟨hxr, hxi⟩ ⟨hyr, hyi⟩
    constructor
    · rw [Complex.add_re]
      exact add_mem hxr hyr
    · rw [Complex.add_im]
      exact add_mem hxi hyi
  · intro x ⟨hxr, hxi⟩
    constructor
    · rw [Complex.neg_re]
      exact neg_mem hxr
    · rw [Complex.neg_im]
      exact neg_mem hxi
  · intro x ⟨hxr, hxi⟩
    have hnorm : Complex.normSq x ∈ (constructibleClosure
        (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ) := by
      rw [Complex.normSq_apply]
      apply add_mem
      · exact mul_mem hxr hxr
      · exact mul_mem hxi hxi
    constructor
    · rw [Complex.inv_re]
      exact div_mem hxr hnorm
    · rw [Complex.inv_im]
      exact div_mem (neg_mem hxi) hnorm
  · intro x y ⟨hxr, hxi⟩ ⟨hyr, hyi⟩
    constructor
    · rw [Complex.mul_re]
      apply sub_mem
      · exact mul_mem hxr hyr
      · exact mul_mem hxi hyi
    · rw [Complex.mul_im]
      apply add_mem
      · exact mul_mem hxr hyi
      · exact mul_mem hxi hyr
  · intro x ⟨hxr, hxi⟩
    have hnorm : ‖x ^ 2‖ ∈ constructibleClosure
        (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ := by
      apply mem_constructibleClosure_of_sq_mem
      rw [Complex.sq_norm, Complex.normSq_apply]
      apply add_mem
      · exact mul_mem hxr hxr
      · exact mul_mem hxi hxi
    constructor
    · apply mem_constructibleClosure_of_sq_mem
      rw [Complex.re_sq_of_sq_eq rfl]
      refine div_mem ?_ (by simp)
      exact add_mem hnorm hxr
    · apply mem_constructibleClosure_of_sq_mem
      rw [Complex.im_sq_of_sq_eq rfl]
      refine div_mem ?_ (by simp)
      exact sub_mem hnorm hxr

theorem mem_constructibleClosure_of_real {s : Set ℂ} (h : ∀ x ∈ s, conj x ∈ s) {x : ℝ}
    (hx : x ∈ constructibleClosure (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ) :
    (x : ℂ) ∈ constructibleClosure (Subfield.closure s) ℂ := by
  revert hx
  apply constructibleClosure_closure_induction
  · simp
  · intro x hx
    simp only [Set.mem_union, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ := hx
    · apply mem_constructibleClosure_of_mem_subfield
      rw [Complex.re_eq_add_conj]
      refine div_mem ?_ (by simp)
      apply add_mem (Subfield.mem_closure_of_mem hy)
      exact Subfield.mem_closure_of_mem (h y hy)
    · rw [Complex.im_eq_sub_conj]
      apply div_mem
      · apply sub_mem
        · apply mem_constructibleClosure_of_mem_subfield
          exact Subfield.mem_closure_of_mem hy
        · apply mem_constructibleClosure_of_mem_subfield
          exact Subfield.mem_closure_of_mem (h y hy)
      · apply mul_mem (by simp)
        apply mem_constructibleClosure_of_sq_mem
        simp
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · intro x hx
    simpa using neg_mem hx
  · intro x hx
    simpa using inv_mem hx
  · intro x y hx hy
    simpa using mul_mem hx hy
  · intro x hx
    apply mem_constructibleClosure_of_sq_mem
    simpa using hx

theorem mem_constructibleClosure_complex_iff {s : Set ℂ} (h : ∀ x ∈ s, conj x ∈ s) {x : ℂ} :
    x ∈ constructibleClosure (Subfield.closure s) ℂ ↔
    x.re ∈ constructibleClosure (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ ∧
    x.im ∈ constructibleClosure (Subfield.closure (Complex.re '' s ∪ Complex.im '' s)) ℝ where
  mp := re_im_subset_constructibleClosure
  mpr hx := by
    rw [← Complex.re_add_im x]
    apply add_mem
    · exact mem_constructibleClosure_of_real h hx.1
    · apply mul_mem
      · exact mem_constructibleClosure_of_real h hx.2
      · apply mem_constructibleClosure_of_sq_mem
        simp
