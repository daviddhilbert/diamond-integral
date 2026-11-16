import «section 6».MeasuredIndexedFocusRepair
import «section 6».SelectedGammaFormDescent
import «section 6».SelectedIndexedFocusRepair

/-! Actual continuity repair on the covered joint source preserves all
levels of the original source form, even with arbitrary extra retained
RV labels. The full existing geometric repair certificate is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}

theorem exists_measured_selected_indexed_focus_repair
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (X : RVRefinementFrame (unaryIndexedMixedFamily η A))
    (hC : IsRVPullback X.base.carrier) (hB : ProperInvariant S B.carrier)
    (hP : ∀ i,ProperInvariant S (X.selectedPiece (unaryIndexedMixedFamily η (P i))).carrier)
    (F : TailContinuousFullFocusGraphData (G := G) X.coveredBase)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ X.base.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ R : IndexedFocusRepairCertificate (G := G) η A P X.coveredBase
        (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i))) F,
      (∀ γ,∀ E : R.freezing.balls,FMT.CoordinateProductDomain
        {p | p ∈ X.coveredBase.carrier ∧ gammaFormExtension (X.descendedGammaForm ω hSame) p=γ}
        (FMT.vfOpenBall E.val) (R.freezing.centers E) 0) ∧
      ∀ γ,∀ E : R.freezing.balls,FMT.CoordinateProductDomain
        {p | p ∈ X.base.carrier ∧ gammaFormExtension ω p=γ}
        (FMT.vfOpenBall E.val) (R.freezing.centers E) 0 := by
  obtain ⟨R,hProducts⟩ := exists_measured_indexed_focus_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt η hB
    A P X.coveredBase (X.coveredBase_rvPullback hC) X.coveredBase_subset
    (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i)))
    (fun i => X.coveredPiece_properInvariant h00 hc hκ hs hv hC _ (hP i))
    (fun i => Set.inter_comm _ _) F (X.descendedGammaForm ω hSame) (X.descendedGammaForm_levels_open ω hSame hLevels)
  exact ⟨R,hProducts,fun γ E => X.gamma_level_product ω hSame γ _ _ 0 (hProducts γ E)⟩

end DiamondIntegral.Section6
