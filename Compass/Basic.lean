import Mathlib

/-!
-/

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

@[simp]
theorem relrank_star [StarRing K] [StarRing L] [StarModule K L]
    (f g : IntermediateField K L) :
    (star f).relrank (star g) = f.relrank g := by
  rw [← inf_relrank_right _ (star g), ← inf_relrank_right _ g]
  rw [relrank_eq_rank_of_le inf_le_right]
  rw [relrank_eq_rank_of_le inf_le_right]
  let i : ↥(f ⊓ g) ≃ ↥(star f ⊓ star g) := {
    toFun := fun ⟨x, hx⟩ ↦ ⟨star x, by simpa using hx⟩
    invFun := fun ⟨x, hx⟩ ↦ ⟨star x, by simpa using hx⟩
    left_inv := by
      intro x
      simp
    right_inv := by
      intro x
      simp
  }
  let j : ↥(extendScalars (inf_le_right : star f ⊓ star g ≤ star g)) ≃+
      ↥(extendScalars (inf_le_right : f ⊓ g ≤ g)) := {
    toFun := fun ⟨x, hx⟩ ↦ ⟨star x, by simpa using hx⟩
    invFun := fun ⟨x, hx⟩ ↦ ⟨star x, by simpa using hx⟩
    left_inv := by
      intro x
      simp
    right_inv := by
      intro x
      simp
    map_add' := by simp
  }
  apply le_antisymm
  · apply rank_le_of_injective_injectiveₛ i j.toAddMonoidHom i.injective j.injective
    · intro ⟨r, hr⟩ ⟨m, hm⟩
      simp [i, j, IntermediateField.smul_def]
  · apply rank_le_of_injective_injectiveₛ i.symm j.symm.toAddMonoidHom i.symm.injective
      j.symm.injective
    · intro ⟨r, hr⟩ ⟨m, hm⟩
      simp [i, j, IntermediateField.smul_def]

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

protected theorem IsIteratedQuadraticExtension.star [StarRing K] [StarRing L] [StarModule K L]
    {f : IntermediateField K L}
    (hf : IsIteratedQuadraticExtension f) :
    IsIteratedQuadraticExtension (star f) :=
match hf with
| IsIteratedQuadraticExtension.bot => by simpa using IsIteratedQuadraticExtension.bot
| IsIteratedQuadraticExtension.extension e f' he hef h => by
  refine IsIteratedQuadraticExtension.extension (star e) (star f') he.star ?_ ?_
  · exact IntermediateField.star_mono hef
  · simpa using h

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

theorem mem_constructibleClosure_of_mem_subfield {x : L} {K : Subfield L} (h : x ∈ K) :
    x ∈ constructibleClosure K L := by
  refine Set.mem_of_mem_of_subset ?_ <| SetLike.coe_subset_coe.mpr bot_le
  rw [SetLike.mem_coe, IntermediateField.mem_bot, Set.mem_range]
  exact ⟨⟨x, h⟩, (by simp [Subfield.algebraMap_ofSubfield])⟩

theorem star_mem_constructibleClosure [StarRing K] [StarRing L] [StarModule K L]
    {x : L} (hx : x ∈ constructibleClosure K L) :
    star x ∈ constructibleClosure K L := by
  rw [mem_constructibleClosure] at ⊢ hx
  obtain ⟨f, hf, hx⟩ := hx
  exact ⟨star f, hf.star, by simpa using hx⟩

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
| centerRadius (o : Sphere P) (r : P) (hcenter : ConstructiblePoint initial o.center)
    (hradius : ConstructiblePoint initial r) (h : r ∈ o) :
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

theorem Constructible.mem_constructibleClosure {initial : Set ℂ}
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
      have ha := Constructible.mem_constructibleClosure hinit ha
      have hb := Constructible.mem_constructibleClosure hinit hb
      have hc := Constructible.mem_constructibleClosure hinit hc
      have hd := Constructible.mem_constructibleClosure hinit hd
      have habp : Collinear ℝ {a, b, p} := by
        rw [collinear_iff_finrank_le_one, ← hl₁, ← direction_affineSpan]
        apply Submodule.finrank_mono
        apply AffineSubspace.direction_le
        apply affineSpan_le_of_subset_coe
        grind [SetLike.mem_coe]
      have hcdp : Collinear ℝ {c, d, p} := by
        rw [collinear_iff_finrank_le_one, ← hl₂, ← direction_affineSpan]
        apply Submodule.finrank_mono
        apply AffineSubspace.direction_le
        apply affineSpan_le_of_subset_coe
        grind [SetLike.mem_coe]
      rw [mem_constructibleClosure_complex_iff hinit] at ⊢ ha hb hc hd
      constructor
      · apply mem_constructibleClosure_of_mem_subfield
        sorry
      · apply mem_constructibleClosure_of_mem_subfield
        sorry
  | ConstructiblePoint.lineCircle l o hl ho p hpl hpo => by
    sorry
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
      have ho₁ := Constructible.mem_constructibleClosure hinit ho₁
      have ho₂ := Constructible.mem_constructibleClosure hinit ho₂
      have hr₁ := Constructible.mem_constructibleClosure hinit hr₁
      have hr₂ := Constructible.mem_constructibleClosure hinit hr₂
      rw [mem_constructibleClosure_complex_iff hinit] at ⊢ ho₁ ho₂ hr₁ hr₂
      have hx := system_two_x h1' hline
      have hy := system_two_y h1' hline
      have ha : a ∈ Cℝ(initial) := mul_mem (by simp) <| sub_mem ho₁.1 ho₂.1
      have hb : b ∈ Cℝ(initial) := mul_mem (by simp) <| sub_mem ho₁.2 ho₂.2
      have hc : c ∈ Cℝ(initial) := by
        apply sub_mem
        · refine add_mem ?_ (pow_mem ho₁.2 _)
          refine add_mem ?_ (pow_mem ho₁.1 _)
          exact add_mem (pow_mem (sub_mem hr₂.1 ho₂.1) _) (pow_mem (sub_mem hr₂.2 ho₂.2) _)
        · refine add_mem ?_ (pow_mem ho₂.2 _)
          refine add_mem ?_ (pow_mem ho₂.1 _)
          exact add_mem (pow_mem (sub_mem hr₁.1 ho₁.1) _) (pow_mem (sub_mem hr₁.2 ho₁.2) _)
      have hd : d ∈ Cℝ(initial) := mul_mem (by simp) ho₁.1
      have he : e ∈ Cℝ(initial) := mul_mem (by simp) ho₁.2
      have hf : f ∈ Cℝ(initial) := by
        apply sub_mem
        · refine add_mem (pow_mem ?_ _) (pow_mem ?_ _)
          · exact sub_mem hr₁.1 ho₁.1
          · exact sub_mem hr₁.2 ho₁.2
        · exact add_mem (pow_mem ho₁.1 _) (pow_mem ho₁.2 _)
      constructor
      · suffices 2 * (a ^ 2 + b ^ 2) * p.re + (d * b ^ 2 - e * a * b - 2 * a * c) ∈ Cℝ(initial) by
          sorry
        apply mem_constructibleClosure_of_sq_mem
        rw [hx]
        apply add_mem
        · apply mul_mem
          · apply mul_mem (by simp)
            apply add_mem (pow_mem ha _) (pow_mem hb _)
          · apply sub_mem
            · apply sub_mem
              · exact mul_mem (pow_mem hb _) hf
              · exact pow_mem hc _
            · exact mul_mem (mul_mem he hb) hc
        · apply pow_mem
          apply sub_mem
          · sorry
          · sorry
      sorry


theorem not_exist_angle_trisection :
    ∃ p₁ p₂ p₃ : P, ∀ q₁ q₂ q₃ : P,
    ConstructiblePoint {p₁, p₂, p₃} q₁ →
    ConstructiblePoint {p₁, p₂, p₃} q₂ →
    ConstructiblePoint {p₁, p₂, p₃} q₃ →
    3 * ∠ q₁ q₂ q₃ ≠ ∠ p₁ p₂ p₃ := by
  sorry

end EuclideanGeometry
