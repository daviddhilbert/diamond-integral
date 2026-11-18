import «section 2».GammaCodeShift

/-! Stable embeddedness of Γ, the tuple step. If two tuples of nonzero RV
codes have values of the same ℤ-type over the values `Δ` of a small
substructure `K`, then an automorphism fixing `K` carries the values of the
first tuple to those of the second (`exists_automorphism_code_tuple`).

The proof is by induction on the length: move the first value by the one-code
step, enlarge `K` to the code substructure of the target first code (or keep
`K` if that value is dependent), and continue with the remaining values,
whose ℤ-type over the enlarged values is read off from the original one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2.GammaStable
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
set_option linter.unusedSectionVars false

/-! ### Automorphisms acting on RV codes -/

theorem aut_funMap2 (σ : M ≃[LRV] M) (f : Fn 2) (x y : M) :
    σ (Structure.funMap (L := LRV) f ![x,y]) = Structure.funMap (L := LRV) f ![σ x,σ y] := by
  have h := σ.map_fun' (f : LRV.Functions 2) ![x,y]
  change σ.toFun (Structure.funMap (L := LRV) f ![x,y]) = Structure.funMap (L := LRV) f (σ.toFun ∘ ![x,y]) at h
  rw [show (σ.toFun ∘ ![x,y]) = ![σ x,σ y] from by funext i; fin_cases i <;> rfl] at h
  exact h

theorem aut_funMap1 (σ : M ≃[LRV] M) (f : Fn 1) (x : M) :
    σ (Structure.funMap (L := LRV) f ![x]) = Structure.funMap (L := LRV) f ![σ x] := by
  have h := σ.map_fun' (f : LRV.Functions 1) ![x]
  change σ.toFun (Structure.funMap (L := LRV) f ![x]) = Structure.funMap (L := LRV) f (σ.toFun ∘ ![x]) at h
  rw [show (σ.toFun ∘ ![x]) = ![σ x] from by funext i; fin_cases i; rfl] at h
  exact h

theorem aut_funMap0 (σ : M ≃[LRV] M) (f : Fn 0) :
    σ (Structure.funMap (L := LRV) f (fun i => i.elim0)) = Structure.funMap (L := LRV) f (fun i => i.elim0) := by
  have h := σ.map_fun' (f : LRV.Functions 0) (fun i => i.elim0)
  change σ.toFun _ = Structure.funMap (L := LRV) f (σ.toFun ∘ fun i => i.elim0) at h
  rw [show (σ.toFun ∘ fun i : Fin 0 => i.elim0) = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)] at h
  exact h

theorem aut_relMap2 (σ : M ≃[LRV] M) (r : Rel 2) (x y : M) :
    Structure.RelMap (L := LRV) r ![σ x,σ y] ↔ Structure.RelMap (L := LRV) r ![x,y] := by
  have h := σ.map_rel' (r : LRV.Relations 2) ![x,y]
  rw [show (σ.toFun ∘ ![x,y]) = ![σ x,σ y] from by funext i; fin_cases i <;> rfl] at h
  exact h

theorem autRV_val (σ : M ≃[LRV] M) (t : RVS M) : (autRV σ t).val = σ t.val := rfl

theorem autRV_mul (σ : M ≃[LRV] M) (a b : RVS M) : autRV σ (a * b) = autRV σ a * autRV σ b := by
  apply Subtype.ext
  rw [autRV_val,RVOperations.mul_val,RVOperations.mul_val,autRV_val,autRV_val]
  exact aut_funMap2 σ Fn.rvMul a.val b.val

theorem autRV_inv (σ : M ≃[LRV] M) (a : RVS M) : autRV σ a⁻¹ = (autRV σ a)⁻¹ := by
  apply Subtype.ext
  rw [autRV_val,RVOperations.inv_val,RVOperations.inv_val,autRV_val]
  exact aut_funMap1 σ Fn.rvInv a.val

theorem autRV_one (σ : M ≃[LRV] M) : autRV σ (1 : RVS M) = 1 := by
  apply Subtype.ext
  rw [autRV_val,RVOperations.one_val]
  exact aut_funMap0 σ Fn.rvOne

theorem autRV_zero (σ : M ≃[LRV] M) : autRV σ (0 : RVS M) = 0 := by
  apply Subtype.ext
  rw [autRV_val,RVOperations.zero_val]
  exact aut_funMap0 σ Fn.rvZero

/-- The action of an automorphism on RV codes, as a monoid-with-zero map. -/
def autRVHom (σ : M ≃[LRV] M) : RVS M →*₀ RVS M where
  toFun := autRV σ
  map_zero' := autRV_zero σ
  map_one' := autRV_one σ
  map_mul' := autRV_mul σ

theorem autRV_zpow (σ : M ≃[LRV] M) (a : RVS M) (m : ℤ) : autRV σ (a ^ m) = (autRV σ a) ^ m :=
  map_zpow₀ (autRVHom σ) a m

theorem autRV_prod (σ : M ≃[LRV] M) {k : ℕ} (T : Fin k → RVS M) (m : Fin k → ℤ) :
    autRV σ (∏ i, T i ^ m i) = ∏ i, (autRV σ (T i)) ^ m i := by
  change autRVHom σ (∏ i, T i ^ m i) = _
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => autRV_zpow σ (T i) (m i))

theorem autRV_ne_zero (σ : M ≃[LRV] M) {a : RVS M} (ha : a ≠ 0) : autRV σ a ≠ 0 := by
  intro h
  apply ha
  apply Subtype.ext
  have h' : σ a.val = σ (0 : RVS M).val := by
    rw [← autRV_val,h,← autRV_val,autRV_zero]
  exact σ.injective h'

theorem autRV_le_iff (σ : M ≃[LRV] M) (a b : RVS M) :
    Values.vrv (autRV σ a) ≤ Values.vrv (autRV σ b) ↔ Values.vrv a ≤ Values.vrv b := by
  rw [Values.vrv_le_iff,Values.vrv_le_iff,autRV_val,autRV_val]
  exact aut_relMap2 σ Rel.rvLe a.val b.val

theorem autRV_vrv_congr (σ : M ≃[LRV] M) {a b : RVS M} (h : Values.vrv a = Values.vrv b) :
    Values.vrv (autRV σ a) = Values.vrv (autRV σ b) :=
  le_antisymm ((autRV_le_iff σ a b).mpr h.le) ((autRV_le_iff σ b a).mpr h.ge)

theorem autRV_of_mem {σ : M ≃[LRV] M} {K : LRV.Substructure M} (hσ : ∀ x ∈ K, σ x = x)
    {c : RVS M} (hc : c.val ∈ K) : autRV σ c = c :=
  Subtype.ext (hσ c.val hc)

theorem autRV_comp (σ τ : M ≃[LRV] M) (a : RVS M) : autRV (τ.comp σ) a = autRV τ (autRV σ a) := rfl

/-! ### ℤ-types of tuples -/

/-- The values of two code tuples have the same ℤ-type over the values of `K`. -/
def CodeTupleTypeEq (K : LRV.Substructure M) {k : ℕ} (T T' : Fin k → RVS M) : Prop :=
  ∀ (m : Fin k → ℤ) (c : RVS M), c.val ∈ K → c ≠ 0 →
    (Values.vrv (∏ i, T i ^ m i) ≤ Values.vrv c ↔ Values.vrv (∏ i, T' i ^ m i) ≤ Values.vrv c)

theorem prod_single_zero {k : ℕ} (T : Fin (k+1) → RVS M) (m₀ : ℤ) :
    ∏ i, T i ^ (Pi.single (0 : Fin (k+1)) m₀ : Fin (k+1) → ℤ) i = T 0 ^ m₀ := by
  rw [Fin.prod_univ_succ]
  simp only [Pi.single_eq_same]
  rw [Finset.prod_eq_one]
  · rw [mul_one]
  · intro i _
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i),zpow_zero]

theorem CodeTupleTypeEq.head {K : LRV.Substructure M} {k : ℕ} {T T' : Fin (k+1) → RVS M}
    (h : CodeTupleTypeEq K T T') : CodeTypeEq K (T 0) (T' 0) := by
  intro m c hc hc0
  have hh := h (Pi.single 0 m) c hc hc0
  rwa [prod_single_zero,prod_single_zero] at hh

theorem prod_cons {k : ℕ} (T : Fin (k+1) → RVS M) (j : ℤ) (m : Fin k → ℤ) :
    ∏ i, T i ^ (Fin.cons j m : Fin (k+1) → ℤ) i = T 0 ^ j * ∏ i : Fin k, T i.succ ^ m i := by
  rw [Fin.prod_univ_succ]
  rfl

/-- The tail step: after moving the first value, the remaining values have
the same ℤ-type over the values `c·T'₀^j` of the enlarged substructure. -/
theorem tail_type {K : LRV.Substructure M} {k : ℕ} {T T' : Fin (k+1) → RVS M}
    (hT' : T' 0 ≠ 0) (htype : CodeTupleTypeEq K T T')
    (σ : M ≃[LRV] M) (hσ : ∀ x ∈ K, σ x = x) (hσ0 : Values.vrv (autRV σ (T 0)) = Values.vrv (T' 0))
    (hT0 : T 0 ≠ 0) (m : Fin k → ℤ) (c : RVS M) (hc : c.val ∈ K) (hc0 : c ≠ 0) (j : ℤ) :
    Values.vrv (∏ i, (autRV σ (T i.succ)) ^ m i) ≤ Values.vrv (c * T' 0 ^ j) ↔
      Values.vrv (∏ i, T' i.succ ^ m i) ≤ Values.vrv (c * T' 0 ^ j) := by
  have hu : Values.vrv (T' 0 ^ (-j)) ≠ 0 := vrv_ne_zero (zpow_ne_zero _ hT')
  have hrw (P : RVS M) :
      Values.vrv P ≤ Values.vrv (c * T' 0 ^ j) ↔ Values.vrv (T' 0 ^ (-j) * P) ≤ Values.vrv c := by
    rw [← gammaTop_mul_le_mul_iff hu,← RVOperations.vrv_mul,← RVOperations.vrv_mul]
    have he : T' 0 ^ (-j) * (c * T' 0 ^ j) = c := by
      rw [mul_comm c,← mul_assoc,← zpow_add₀ hT',neg_add_cancel,zpow_zero,one_mul]
    rw [he]
  rw [hrw,hrw]
  have hσc : autRV σ c = c := autRV_of_mem hσ hc
  have hleft : Values.vrv (T' 0 ^ (-j) * ∏ i, (autRV σ (T i.succ)) ^ m i) =
      Values.vrv (autRV σ (∏ i, T i ^ (Fin.cons (-j) m : Fin (k+1) → ℤ) i)) := by
    rw [prod_cons,autRV_mul,autRV_zpow,autRV_prod,RVOperations.vrv_mul,RVOperations.vrv_mul,
      vrv_zpow,vrv_zpow,hσ0]
  rw [hleft]
  calc Values.vrv (autRV σ (∏ i, T i ^ (Fin.cons (-j) m : Fin (k+1) → ℤ) i)) ≤ Values.vrv c ↔
        Values.vrv (autRV σ (∏ i, T i ^ (Fin.cons (-j) m : Fin (k+1) → ℤ) i)) ≤ Values.vrv (autRV σ c) := by
          rw [hσc]
    _ ↔ Values.vrv (∏ i, T i ^ (Fin.cons (-j) m : Fin (k+1) → ℤ) i) ≤ Values.vrv c := autRV_le_iff σ _ c
    _ ↔ Values.vrv (∏ i, T' i ^ (Fin.cons (-j) m : Fin (k+1) → ℤ) i) ≤ Values.vrv c := htype _ c hc hc0
    _ ↔ _ := by rw [prod_cons]

/-- The cardinality of a code substructure. -/
theorem codeSubstructure_small (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (K : LRV.Substructure M) (hK : Cardinal.mk (K : Set M) < κ)
    (T : RVS M) (hT : T ≠ 0) (hind : CodeIndependent K T) :
    Cardinal.mk (codeSubstructure hc K T hT hind : Set M) < κ := by
  let f : ↥(K : Set M) × ℤ → M := fun p =>
    if h : iRV p.1.val then ((⟨p.1.val,h⟩ : RVS M) * T ^ p.2).val else p.1.val
  have hsub : (codeSubstructure hc K T hT hind : Set M) ⊆ (K : Set M) ∪ Set.range f := by
    intro x hx
    rcases hx with ⟨_,hxK⟩ | ⟨c,m,hcK,rfl⟩
    · exact Or.inl hxK
    · refine Or.inr ⟨(⟨c.val,hcK⟩,m),?_⟩
      change (if h : iRV c.val then ((⟨c.val,h⟩ : RVS M) * T ^ m).val else c.val) = _
      rw [dif_pos c.property]
  have hrange : Cardinal.mk (Set.range f) < κ := by
    refine (Cardinal.mk_range_le).trans_lt ?_
    rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hκ.le hK (Cardinal.mk_int.trans_lt hκ)
  exact (Cardinal.mk_le_mk_of_subset hsub).trans_lt
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hK hrange))

/-- The tuple step of stable embeddedness. -/
theorem exists_automorphism_code_tuple (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hh : StronglyHomogeneous M κ) :
    ∀ (k : ℕ) (K : LRV.Substructure M), Cardinal.mk (K : Set M) < κ →
      ∀ (T T' : Fin k → RVS M), (∀ i, T i ≠ 0) → (∀ i, T' i ≠ 0) → CodeTupleTypeEq K T T' →
      ∃ σ : M ≃[LRV] M, (∀ x ∈ K, σ x = x) ∧
        ∀ i, ∀ t : RVS M, Values.vrv t = Values.vrv (T i) → Values.vrv (autRV σ t) = Values.vrv (T' i) := by
  intro k
  induction k with
  | zero =>
    intro K _ T T' _ _ _
    exact ⟨FirstOrder.Language.Equiv.refl LRV M,fun _ _ => rfl,fun i => i.elim0⟩
  | succ k ih =>
    intro K hK T T' hT hT' htype
    obtain ⟨σ₁,hσ₁K,hσ₁0⟩ := exists_automorphism_code hc hκ.le hh K hK (T 0) (T' 0) (hT 0) (hT' 0) htype.head
    -- The enlarged substructure and its two properties.
    have hK₁ : ∃ K₁ : LRV.Substructure M, K ≤ K₁ ∧ Cardinal.mk (K₁ : Set M) < κ ∧
        (∀ τ : M ≃[LRV] M, (∀ x ∈ K₁, τ x = x) → ∀ t : RVS M, Values.vrv t = Values.vrv (T' 0) →
          Values.vrv (autRV τ t) = Values.vrv (T' 0)) ∧
        (∀ c₁ : RVS M, c₁.val ∈ K₁ → c₁ ≠ 0 → ∃ c : RVS M, ∃ j : ℤ, c.val ∈ K ∧ c ≠ 0 ∧ c₁ = c * T' 0 ^ j) := by
      by_cases hind : CodeIndependent K (T' 0)
      · refine ⟨codeSubstructure hc K (T' 0) (hT' 0) hind,le_codeSubstructure hc K _ _ hind,
          codeSubstructure_small hc hκ K hK _ _ hind,?_,?_⟩
        · intro τ hτ t ht
          have hfix : autRV τ (T' 0) = T' 0 :=
            Subtype.ext (hτ _ (code_mem_codeSubstructure hc K _ (hT' 0) hind))
          rw [autRV_vrv_congr τ ht,hfix]
        · intro c₁ hc₁ hc₁0
          obtain ⟨c,j,hcK,he⟩ := codeCarrier_rep hc₁ c₁.property
          have he' : c₁ = c * T' 0 ^ j := Subtype.ext he
          refine ⟨c,j,hcK,?_,he'⟩
          rintro rfl
          rw [zero_mul] at he'
          exact hc₁0 he'
      · refine ⟨K,le_refl K,hK,?_,?_⟩
        · intro τ hτ t ht
          simp only [CodeIndependent,not_forall,not_not] at hind
          obtain ⟨m,hm,c,hcK,he⟩ := hind
          have ht0 : t ≠ 0 := by
            intro h0
            rw [h0,(vrv_eq_zero_iff (0 : RVS M)).mpr rfl] at ht
            exact vrv_ne_zero (hT' 0) ht.symm
          have htm : Values.vrv (t ^ m) = Values.vrv c := by rw [vrv_zpow,ht,← vrv_zpow,he]
          have h1 := autRV_vrv_congr τ htm
          rw [autRV_zpow,autRV_of_mem hτ hcK] at h1
          exact gamma_zpow_injective_rv (autRV_ne_zero τ ht0) (hT' 0) hm (h1.trans he.symm)
        · intro c₁ hc₁ hc₁0
          exact ⟨c₁,0,hc₁,hc₁0,by rw [zpow_zero,mul_one]⟩
    obtain ⟨K₁,hKK₁,hK₁small,hK₁fix,hK₁rep⟩ := hK₁
    -- The remaining values have the same type over the enlarged values.
    let U : Fin k → RVS M := fun i => autRV σ₁ (T i.succ)
    let U' : Fin k → RVS M := fun i => T' i.succ
    have htail : CodeTupleTypeEq K₁ U U' := by
      intro m c₁ hc₁ hc₁0
      obtain ⟨c,j,hcK,hc0,rfl⟩ := hK₁rep c₁ hc₁ hc₁0
      exact tail_type (hT' 0) htype σ₁ hσ₁K hσ₁0 (hT 0) m c hcK hc0 j
    obtain ⟨τ,hτK₁,hτ⟩ := ih K₁ hK₁small U U' (fun i => autRV_ne_zero σ₁ (hT i.succ))
      (fun i => hT' i.succ) htail
    refine ⟨τ.comp σ₁,?_,?_⟩
    · intro x hx
      change τ (σ₁ x) = x
      rw [hσ₁K x hx]
      exact hτK₁ x (hKK₁ hx)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro t ht
        rw [autRV_comp]
        apply hK₁fix τ hτK₁
        rw [autRV_vrv_congr σ₁ ht,hσ₁0]
      · intro t ht
        rw [autRV_comp]
        exact hτ j (autRV σ₁ t) (autRV_vrv_congr σ₁ ht)

end DiamondIntegral.Section2.GammaStable
