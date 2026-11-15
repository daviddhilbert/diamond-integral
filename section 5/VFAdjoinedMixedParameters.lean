import «section 5».VFAdjoinedParameterTransfer

/-! Finite RV chart tags already named in the original field add no
parameter to F(b). The exact generated-field adapter therefore also
applies to mixed tuples whose RV entries are original-ground names. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open CanonicalRV ValuedModelMap DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (G : GammaGroundContext M)
variable {n : ℕ} (b : Fin n → M)
variable (hb : ∀ i,iRV (b i) → b i ∈ G.base.real)
variable (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1)

include hb in
theorem rawMixedParameters_subset_vfAdjoinedFieldNames :
    G.base.real ∪ Set.range b ⊆ (vfFieldSubstructure hc (vfAdjoinedField G b) : Set M) := by
  rintro x (hx | ⟨i,rfl⟩)
  · exact groundReal_subset_vfAdjoinedFieldNames hc G b hx
  · rcases TypedModelMap.sort_cover (M := M) (b i) with hv | hr
    · exact (vfFieldCarrier_vf (vfAdjoinedField G b) ⟨b i,hv⟩).mpr (Subfield.subset_closure (Or.inr ⟨i,rfl⟩))
    · exact groundReal_subset_vfAdjoinedFieldNames hc G b (hb i hr)

include hb in
theorem raw_to_vfAdjoinedContext_mixed
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    {d : ℕ} (sn : Fin d → SortTag) (D : Set (Fin d → M))
    (hD : DefinableOverBase (vfRawParameterBase G b) sn D) :
    DefinableOverBase (vfAdjoinedContext hc G b hnt).base sn D := by
  apply hD.eliminate_definable_params
  · intro c hc'
    have hm := rawMixedParameters_subset_vfAdjoinedFieldNames hc G b hb hc'
    rcases TypedModelMap.sort_cover (M := M) c with hv | hr
    · exact ⟨.vf,real_definableAtBase _ .vf _ (definableClosureAt_of_mem hm hv)⟩
    · exact ⟨.rv,real_definableAtBase _ .rv _ (definableClosureAt_of_mem hm hr)⟩
  · intro γ hγ'
    exact (hγ γ hγ').mono (groundReal_subset_vfAdjoinedFieldNames hc G b) (Set.empty_subset _)

def vfRawMixedParameterLiftInput
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (I : YinGammaGroundUnmeasuredLiftInput (vfAdjoinedContext hc G b hnt) hc) :
    OriginalBaseUnmeasuredLiftInput hc (vfRawParameterBase G b) :=
  sortedTransferOriginalLiftInput (vfAdjoinedContext_to_raw hc G b hnt)
    (raw_to_vfAdjoinedContext_mixed hc G b hb hnt hγ) (originalBaseLiftInputOfContext I)

end DiamondIntegral.Section5
