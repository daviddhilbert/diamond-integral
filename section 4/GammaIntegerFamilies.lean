import «section 4».GammaFamilyIntegration

/-! Finite-range original-base definable integer functions in every finite
Gamma arity. The algebra below is pointwise addition and integer scalar
multiplication, as needed for weighted fibre integration. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaIntegerFamilies
open GammaOrderLogic GammaFamilyIntegration

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem univ_definable_base (B : Base (M := M)) (n : ℕ) :
    GammaDefinable B (Set.univ : Set (Fin n → Values.Gamma (M := M))) := by
  simpa only [GammaDefinable, Set.mem_univ, and_true] using proper_definable_base B n

theorem empty_definable_base (B : Base (M := M)) (n : ℕ) :
    GammaDefinable B (∅ : Set (Fin n → Values.Gamma (M := M))) := by
  simpa only [Set.compl_univ] using
    GammaRelationLogic.complement_definable_base B _ (univ_definable_base B n)

theorem const_definable (B : Base (M := M)) (n : ℕ) (c : ℤ) :
    IntegerFamilyDefinable B (fun _ : Fin n → Values.Gamma (M := M) => c) := by
  refine ⟨Set.finite_range_const, ?_⟩
  intro m
  by_cases h : c = m
  · simpa only [h, Set.ofPred_true] using univ_definable_base B n
  · simpa only [h, Set.ofPred_false] using empty_definable_base B n

theorem map_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (F : ℤ → ℤ) : IntegerFamilyDefinable B (fun y => F (f y)) := by
  refine ⟨(hf.1.image F).subset ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨f y, ⟨y, rfl⟩, rfl⟩
  · intro m
    let s := hf.1.toFinset.filter (fun a => F a = m)
    have h := GammaQuantifierLogic.finite_iUnion_definable_base B
      (fun a : s => {y | f y = a.val}) (fun a => hf.2 a.val)
    convert h using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hy
      exact ⟨⟨f y, Finset.mem_filter.mpr ⟨hf.1.mem_toFinset.mpr ⟨y, rfl⟩, hy⟩⟩, rfl⟩
    · rintro ⟨a, ha⟩
      rw [ha]
      exact (Finset.mem_filter.mp a.property).2

theorem add_definable (B : Base (M := M)) {n : ℕ}
    (f g : (Fin n → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) (hg : IntegerFamilyDefinable B g) :
    IntegerFamilyDefinable B (fun y => f y + g y) := by
  refine ⟨(Set.Finite.image2 (fun a b : ℤ => a + b) hf.1 hg.1).subset ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨f y, ⟨y, rfl⟩, g y, ⟨y, rfl⟩, rfl⟩
  · intro m
    have h := GammaQuantifierLogic.finite_iUnion_definable_base B
      (fun a : hf.1.toFinset => {y | f y = a.val} ∩ {y | g y = m - a.val})
      (fun a => GammaRelationLogic.inter_definable_base B _ _ (hf.2 a.val) (hg.2 (m - a.val)))
    convert h using 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      refine ⟨⟨f y, hf.1.mem_toFinset.mpr ⟨y, rfl⟩⟩, rfl, ?_⟩
      change g y = m - f y
      omega
    · rintro ⟨a, ha, hb⟩
      omega

theorem finsetSum_definable {ι : Type} (B : Base (M := M)) {n : ℕ} (s : Finset ι)
    (f : ι → (Fin n → Values.Gamma (M := M)) → ℤ)
    (hf : ∀ i ∈ s, IntegerFamilyDefinable B (f i)) :
    IntegerFamilyDefinable B (fun y => ∑ i ∈ s, f i y) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const_definable B n 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using add_definable B _ _
      (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem reindex_definable (B : Base (M := M)) {n m : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (π : Fin n → Fin m) : IntegerFamilyDefinable B (fun z => f (z ∘ π)) := by
  refine ⟨hf.1.subset ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨z ∘ π, rfl⟩
  · intro v
    exact GammaRelationLogic.preimage_definable_base B {z | f z = v} (hf.2 v) π

theorem combine_definable (B : Base (M := M)) {n : ℕ}
    (f g : (Fin n → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) (hg : IntegerFamilyDefinable B g)
    (F : ℤ → ℤ → ℤ) : IntegerFamilyDefinable B (fun z => F (f z) (g z)) := by
  refine ⟨(Set.Finite.image2 F hf.1 hg.1).subset ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨f z, ⟨z, rfl⟩, g z, ⟨z, rfl⟩, rfl⟩
  · intro v
    let Samples := {p : (hf.1.toFinset × hg.1.toFinset) // F p.1.val p.2.val = v}
    have h := GammaQuantifierLogic.finite_iUnion_definable_base B
      (fun p : Samples => {z | f z = p.val.1.val} ∩ {z | g z = p.val.2.val})
      (fun p => GammaRelationLogic.inter_definable_base B _ _ (hf.2 p.val.1.val) (hg.2 p.val.2.val))
    convert h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      refine ⟨⟨(⟨f z, hf.1.mem_toFinset.mpr ⟨z, rfl⟩⟩,
        ⟨g z, hg.1.mem_toFinset.mpr ⟨z, rfl⟩⟩), hz⟩, rfl, rfl⟩
    · rintro ⟨p, hfz, hgz⟩
      rw [hfz, hgz]
      exact p.property

def familySubgroup (B : Base (M := M)) (n : ℕ) :
    AddSubgroup (((Fin n → Values.Gamma (M := M))) → ℤ) where
  carrier := {f | IntegerFamilyDefinable B f}
  zero_mem' := const_definable B n 0
  add_mem' := fun hf hg => add_definable B _ _ hf hg
  neg_mem' := fun hf => map_definable B _ hf (fun m => -m)

end DiamondIntegral.Section4.GammaIntegerFamilies
