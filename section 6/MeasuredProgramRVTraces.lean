import «section 6».GammaRVTraceValues
import «section 6».ExactGammaTransport

/-! The complete geometric program trace is extended by its entire
terminal Gamma graph in RV. Each individual admissible row is bounded
using actual source-form bounds, without a uniform VF-parameter bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CentripetalProgramTemplate.gammaRVTrace (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplate (M := M) S p n r) :
    RVSetParameterTemplate (M := M) S p (s+1) := (W.transport (T.transition A)).rvTrace

def CentripetalProgramTemplate.measuredRVTrace (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplate (M := M) S p n r) :
    List (RVDataTemplate (M := M) S p) := T.rvTrace A P ++ [⟨s+1,T.gammaRVTrace A W⟩]

theorem CentripetalProgramTemplate.gammaRVTrace_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplate (M := M) S p n r) :
    (⟨s+1,T.gammaRVTrace A W⟩ : RVDataTemplate (M := M) S p) ∈ T.measuredRVTrace A P W :=
  List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem CentripetalProgramTemplate.gammaRVTrace_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (h : TemplateFibreGeometry A P a)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    RVValueDoublyBounded ((T.gammaRVTrace A W).fibre a).carrier := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha h.proper h.doublyBounded h.subset h.piecesProper
  have hf := F.chain.toChain.toSpecial.bijective h00
  let η := ω.comp (F.map.inverse hf)
  have hGraph := gammaTransitionImage_at a (T.transition A).graph W.graph F.map hf ω F.graph hW
  have hTarget := F.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
  apply (W.transport (T.transition A)).rvTrace_doublyBounded_of_bounds a η hGraph hTarget.rvBounded
  obtain ⟨δ,hδ⟩ := gammaForm_value_bounds h00 hc linear hκ hs hv (small_union_range hκ.le S hsmall a)
    (hΓ.mono Set.subset_union_left (Set.Subset.rfl)) h.proper ω hLevels
  exact ⟨δ,fun q => hδ (F.map.inverse hf q)⟩

theorem CentripetalProgramTemplate.measuredRVTrace_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (h : TemplateFibreGeometry A P a)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    RVTraceRowsBounded a (T.measuredRVTrace A P W) := by
  apply rvTraceRowsBounded_append a (T.rvTrace_bounded h00 hc hκ hs hv A P a ha h)
  intro D hD
  have he : D=(⟨s+1,T.gammaRVTrace A W⟩ : RVDataTemplate (M := M) S p) := List.mem_singleton.mp hD
  subst D
  exact T.gammaRVTrace_bounded h00 hc linear hκ hs hv hsmall hΓ A P W a ha h ω hW hLevels

end DiamondIntegral.Section6
