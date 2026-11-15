import ValuedModelMap

/-! A valued-field automorphism of a canonical ACVF model acts on the whole
original language, rather than only its multiplicative RV quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The canonical RV action of a valued-field automorphism is bijective. -/
theorem originalRVMap_surjective (σ : VFType (M := M) ≃+* VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b) :
    Function.Surjective (ValuedModelMap.rvMap σ.toRingHom) := by
  intro r
  obtain ⟨a, rfl⟩ := encodedRv_surjective r
  refine ⟨encodedRv (σ.symm a), ?_⟩
  rw [ValuedModelMap.rvMap_encodedRv σ.toRingHom hσ]
  exact congrArg encodedRv (σ.apply_symm_apply a)

/-- Both sorted components are onto, so the assembled carrier map is onto. -/
theorem originalValuedCarrier_surjective (σ : VFType (M := M) ≃+* VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b) :
    Function.Surjective (ValuedModelMap.components σ.toRingHom hσ).carrierMap := by
  intro x
  rcases TypedModelMap.sort_cover x with hx | hx
  · let a : VFType (M := M) := ⟨x, hx⟩
    refine ⟨(σ.symm a).val, ?_⟩
    rw [TypedModelMap.Components.carrierMap_vf _ (σ.symm a).property]
    exact congrArg Subtype.val (σ.apply_symm_apply a)
  · obtain ⟨a, ha⟩ := originalRVMap_surjective σ hσ (⟨x, hx⟩ : RVSort M)
    refine ⟨a.val, ?_⟩
    rw [TypedModelMap.Components.carrierMap_rv _ a.property]
    exact congrArg Subtype.val ha

/-- Actual automorphism of the full original L_RV structure. -/
def originalValuedModelAut (hc : CanonicalStructure.IsCanonical (M := M))
    (σ : VFType (M := M) ≃+* VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b) : M ≃[LRV] M := by
  let e := (ValuedModelMap.toSortedEmbedding σ.toRingHom hσ).toLRVEmbedding hM hM hc hc
  exact {
    toEquiv := _root_.Equiv.ofBijective e ⟨e.injective, originalValuedCarrier_surjective σ hσ⟩
    map_fun' := e.map_fun
    map_rel' := e.map_rel }

end DiamondIntegral.Section5
