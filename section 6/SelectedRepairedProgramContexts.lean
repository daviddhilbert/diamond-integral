import «section 6».SelectedProgramBaseMaps
import «section 6».SelectedIndexedFocusSemantics

/-! The actual fusion context at the updated parameter is constructed
from the repaired covered-joint source, keeping every actual source
and protected set exactly unchanged before the new component is applied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

def SelectedProgramContext.afterFocusRepair (X : SelectedProgramContext η A P C π σ)
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    {F : TailContinuousFullFocusGraphData (G := G) (X.jointFrame hTag).coveredBase}
    (R : IndexedFocusRepairCertificate (G := G) η A P (X.jointFrame hTag).coveredBase
      (fun i => (X.jointFrame hTag).coveredPiece (unaryIndexedMixedFamily η (P i))) F) :
    SelectedProgramContext (R.freezing.unaryParameter R.baseProduct η) A P C π σ := by
  refine ⟨X.proper,X.doublyBounded,X.pullback,?_,?_⟩
  · exact R.selected_source (X.jointFrame hTag)
  · intro i
    change ProperInvariant S (rvLabelPullback (X.jointFrame hTag).base (X.jointFrame hTag).labels
      (unaryIndexedMixedFamily (R.freezing.unaryParameter R.baseProduct η) (P i))).carrier
    rw [← R.selected_pieces (X.jointFrame hTag) i]
    exact X.piecesProper i

namespace IndexedFocusRepairCertificate
variable (X : RVRefinementFrame (unaryIndexedMixedFamily η A))
variable {F : TailContinuousFullFocusGraphData (G := G) X.coveredBase}
variable (R : IndexedFocusRepairCertificate (G := G) η A P X.coveredBase
  (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i))) F)

def refinedSelectedComponent (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val})
    (hVal : vfValue R.component.coefficient ≤ vfValue c) : CentripetalData (G := G) X.base :=
  X.coveredFrame.portComponent (R.component.refineCoefficient c hc0 hcDef hVal)

theorem refinedSelectedComponent_focus (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val})
    (hVal : vfValue R.component.coefficient ≤ vfValue c) (p : X.base) :
    (R.refinedSelectedComponent X c hc0 hcDef hVal).extendedFocus p.val=
      R.component.extendedFocus (selectRVPoint X.labels p.val) :=
  X.coveredFrame.portComponent_focus (R.component.refineCoefficient c hc0 hcDef hVal) p.val p.property

theorem refinedSelectedComponent_restrictions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val})
    (hVal : vfValue R.component.coefficient ≤ vfValue c) (i : Fin k) :
    ∃ E : CentripetalData (G := G) (X.selectedPiece (unaryIndexedMixedFamily η (P i))),
      ApertureRestrictionData (R.refinedSelectedComponent X c hc0 hcDef hVal) E := by
  obtain ⟨E,hE⟩ := R.restrictions i
  rw [← X.selected_coveredPiece_eq (unaryIndexedMixedFamily η (P i))]
  have hValE : vfValue E.coefficient ≤ vfValue c := by rw [hE.coefficient]; exact hVal
  exact ⟨_,X.coveredFrame.portComponent_restriction_data h00 hc hκ hs hv
    (R.component.refineCoefficient c hc0 hcDef hVal) (E.refineCoefficient c hc0 hcDef hValE)
    hE.subset (hE.refine c hc0 hcDef hVal)⟩

end IndexedFocusRepairCertificate
end DiamondIntegral.Section6
