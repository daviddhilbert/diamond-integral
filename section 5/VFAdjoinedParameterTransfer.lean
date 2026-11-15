import «section 5».VFAdjoinedFieldNames
import «section 5».VFFieldGammaNames
import «section 5».VFFieldContext
import «section 5».NativeLiftGroundTransfer
import «section 5».RealGammaGroundElimination

/-! The exact F(b) field presentation and the raw original parameters
F together with the displayed VF tuple define the same categories.
This constructs, rather than assumes, the Section 3 presentation adapter. -/
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
variable {n : ℕ} (b : Fin n → M) (hb : ∀ i,iVF (b i))
variable (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1)

def vfAdjoinedContext : GammaGroundContext M :=
  vfFieldContext G hc (vfAdjoinedField G b) (vfAdjoinedField_small G b) (vfAdjoinedField_nontrivial G b hnt)

def vfRawParameterBase : Base (M := M) := ⟨G.base.real ∪ Set.range b,G.base.gamma⟩

theorem vfAdjoinedContext_to_raw {d : ℕ} (sn : Fin d → SortTag) (D : Set (Fin d → M))
    (hD : DefinableOverBase (vfAdjoinedContext hc G b hnt).base sn D) :
    DefinableOverBase (vfRawParameterBase G b) sn D := by
  apply hD.eliminate_definable_params
  · intro c hc'
    obtain ⟨σ,hσ⟩ := vfParameterFieldSubstructure_names hc (G.base.real ∪ Set.range b) c hc'
    exact ⟨σ,real_definableAtBase (vfRawParameterBase G b) σ _ hσ⟩
  · exact vfParameterFieldGamma_names (vfRawParameterBase G b)

include hb in
theorem raw_to_vfAdjoinedContext
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    {d : ℕ} (sn : Fin d → SortTag) (D : Set (Fin d → M))
    (hD : DefinableOverBase (vfRawParameterBase G b) sn D) :
    DefinableOverBase (vfAdjoinedContext hc G b hnt).base sn D := by
  apply hD.eliminate_definable_params
  · intro c hc'
    have hm := rawVFParameters_subset_vfAdjoinedFieldNames hc G b hb hc'
    rcases TypedModelMap.sort_cover (M := M) c with hv | hr
    · exact ⟨.vf,real_definableAtBase _ .vf _ (definableClosureAt_of_mem hm hv)⟩
    · exact ⟨.rv,real_definableAtBase _ .rv _ (definableClosureAt_of_mem hm hr)⟩
  · intro γ hγ'
    exact (hγ γ hγ').mono (groundReal_subset_vfAdjoinedFieldNames hc G b) (Set.empty_subset _)

def vfRawParameterLiftInput
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (I : YinGammaGroundUnmeasuredLiftInput (vfAdjoinedContext hc G b hnt) hc) :
    OriginalBaseUnmeasuredLiftInput hc (vfRawParameterBase G b) :=
  sortedTransferOriginalLiftInput (vfAdjoinedContext_to_raw hc G b hnt)
    (raw_to_vfAdjoinedContext hc G b hb hnt hγ) (originalBaseLiftInputOfContext I)

end DiamondIntegral.Section5
