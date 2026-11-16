import «section 6».UniformMeasuredTerminalValues
import «section 6».SelectedProgramPrefixes
import «section 6».MeasuredFormCompatibleTargets

/-! Terminal identity preparation uses the entire Gamma record to
compare different head parameters. The actual source map, every protected
image and the form-compatible ambient chain are constructed together. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

namespace SelectedProgramContext

def localSourcePoint (X : SelectedProgramContext η A P C π σ) (p : C) :
    A.fibre (unaryFamilyParameter η (X.baseMap p)) :=
  ⟨(Fin.tail p.val.1,p.val.2 ∘ σ),by
    obtain ⟨b,hb,hA⟩ := (mem_unaryIndexedMixedFamily η A _).mp (X.source p.val p.property)
    have hBase : b=X.baseMap p := Subtype.ext
      (hb.symm.trans ((selectedJointPoint_base π σ p.val).trans (X.baseMap_value p).symm))
    rw [hBase] at hA
    rwa [selectedJointPoint_local] at hA⟩

theorem measured_identity_terminal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hBRP : IsRVPullback B.carrier)
    (U : UniformMeasuredProgramFamily (G := G) η (.identity s) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSource : ∀ p : C,gammaFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∃ F : MeasuredCoordinatePreparation (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) C F.target F.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let J := X.terminal (G := G) hBRP U.toUniformProgramFamily
  have hPhi : FormCompatibleSynchronizedChain (G := G) (Fin k) C J.target J.map
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω :=
    .identity C X.proper _ (fun i => rvLabelPullback_subset C _ _) X.piecesProper ω
  apply J.measured_form_compatible_target h00 hc hκ hs hv ω hPhi
  intro p z hTags
  let b := X.baseMap p
  let c := X.baseMap z
  let x := X.localSourcePoint p
  let y := X.localSourcePoint z
  have hOldTags : p.val.2=z.val.2 := hTags
  have hValue := U.values_eq_of_transition_labels b c (X.baseMap_labels p z hOldTags)
    (Map.id (A.fibre (unaryFamilyParameter η b))) Function.bijective_id
    (Map.id (A.fibre (unaryFamilyParameter η c))) Function.bijective_id
    (identityParameterTransition_at A _) (identityParameterTransition_at A _) x y
    (congrArg (fun u => u ∘ σ) hOldTags)
  have hExt := (gammaFormExtension_at (U.forms b) x).trans
    (hValue.trans (gammaFormExtension_at (U.forms c) y).symm)
  exact (hSource p).symm.trans (hExt.trans (hSource z))

end SelectedProgramContext
end DiamondIntegral.Section6
