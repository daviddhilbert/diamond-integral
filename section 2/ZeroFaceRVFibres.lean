import «section 2».ZeroFacesVF
import «section 2».RawRVPolydiscs

/-! RV polydiscs through zero faces. Zero factors remain singletons;
only the nonzero free factors are treated as open discs. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem ZeroFaceChart.insert_rawRVPolydisc {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z)
    (t : Fin n → RVInfinity M) (ht : ∀ i, t (C.zeroIndex i) = rvZero M)
    (u : Fin C.freeArity → M) (hu : u ∈ rawRVPolydisc (t ∘ C.freeIndex)) :
    C.insert (0 : VF M).val u ∈ rawRVPolydisc t := by
  intro j
  rcases C.coordinate_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [C.insert_zero]
    exact ⟨(0 : VF M).property,congrArg Subtype.val (rv_zero.trans (ht i).symm)⟩
  · rw [C.insert_free]
    exact hu i

theorem ZeroFaceChart.rv_rows_constant_lift {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z)
    (F : (Fin n → M) → Set M) (V : Set (Fin C.freeArity → M))
    (hV : ∀ u ∈ V, ∀ i, u i ≠ (0 : VF M).val)
    (hopen : OpenRVRowsConstant (fun u => F (C.insert (0 : VF M).val u)) V) :
    RVPolydiscRowsConstant F (C.lift (0 : VF M).val V) := by
  intro t hsub x hx y hy
  obtain ⟨w,hw⟩ := rawRVPolydisc_nonempty t
  have hwV := hsub hw
  have ht0 : ∀ i, t (C.zeroIndex i) = rvZero M := fun i =>
    (rvRawFibre_mem_zero_iff _ _ (hw (C.zeroIndex i))).mp (hwV.1 i)
  have htn : ∀ i, (t ∘ C.freeIndex) i ≠ rvZero M := by
    intro i he
    have hz : w (C.freeIndex i) = (0 : VF M).val :=
      (rvRawFibre_mem_zero_iff _ _ (hw (C.freeIndex i))).mpr he
    exact hV _ hwV.2 i hz
  have hfreeSub : rawRVPolydisc (t ∘ C.freeIndex) ⊆ V := by
    intro u hu
    have h := (hsub (C.insert_rawRVPolydisc t ht0 u hu)).2
    rwa [C.project_insert] at h
  obtain ⟨a,δ,he⟩ := rawRVPolydisc_eq_named_of_nonzero (t ∘ C.freeIndex) htn
  have hpoly : namedPolydisc (fun _ => false) a δ ⊆ V := by
    rwa [← he]
  have hxFree : C.project x ∈ rawRVPolydisc (t ∘ C.freeIndex) := fun i => hx (C.freeIndex i)
  have hyFree : C.project y ∈ rawRVPolydisc (t ∘ C.freeIndex) := fun i => hy (C.freeIndex i)
  have hxN : C.project x ∈ namedPolydisc (fun _ => false) a δ := by rwa [← he]
  have hyN : C.project y ∈ namedPolydisc (fun _ => false) a δ := by rwa [← he]
  have hconst := hopen a δ hpoly (C.project x) hxN (C.project y) hyN
  change iRv '' F (C.insert (0 : VF M).val (C.project x)) =
    iRv '' F (C.insert (0 : VF M).val (C.project y)) at hconst
  rwa [C.insert_project _ x (hsub hx).1,C.insert_project _ y (hsub hy).1] at hconst

end DiamondIntegral.Section2
