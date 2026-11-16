import «section 6».IndexedFocusRepair
import «section 6».MeasuredUnaryBaseFocusFreezing

/-! Continuity repair of an actual indexed focus preserves every Gamma
level alongside the actual source, protected pieces and unary parameter
base. The complete existing repair certificate is retained. -/

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

theorem exists_measured_indexed_focus_repair
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hB : ProperInvariant S B.carrier)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hW : IsRVPullback W.carrier) (hSource : W.carrier ⊆ (unaryIndexedMixedFamily η A).carrier)
    (Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hQ : ∀ i,ProperInvariant S (Q i).carrier)
    (hPieces : ∀ i,(Q i).carrier=W.carrier ∩ (unaryIndexedMixedFamily η (P i)).carrier)
    (F : TailContinuousFullFocusGraphData (G := G) W)
    (ω : Map W (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ W.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ R : IndexedFocusRepairCertificate (G := G) η A P W Q F,
      ∀ γ,∀ E : R.freezing.balls,FMT.CoordinateProductDomain
        {p | p ∈ W.carrier ∧ gammaFormExtension ω p=γ} (FMT.vfOpenBall E.val) (R.freezing.centers E) 0 := by
  obtain ⟨D,hCont,hWProd,hQProd,hBProd,hFormProd⟩ := F.exists_measured_frozen_full_graph_with_unary_base
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt Q hQ B hB ω hLevels
  let H := F.frozenFullGraph D hCont
  have hSub (i) : (Q i).carrier ⊆ W.carrier := by
    intro p hp
    rw [hPieces i] at hp
    exact hp.1
  obtain ⟨Z,hCoord,hTags,hFocus,hProtected⟩ := H.exists_protected_component
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hW Q hSub hQ
  have hSourceEq : W.carrier ∩ (unaryIndexedMixedFamily η A).carrier=W.carrier :=
    Set.inter_eq_left.mpr hSource
  have hSourceProduct : ∀ E : D.balls,FMT.CoordinateProductDomain
      (W.carrier ∩ (unaryIndexedMixedFamily η A).carrier) (FMT.vfOpenBall E.val) (D.centers E) 0 := by
    rw [hSourceEq]
    exact hWProd
  have hSourcePreserved := D.unaryIndexed_restricted_family_preserved hBProd η A W hWProd hSourceProduct
  refine ⟨{
    freezing := D
    continuous := hCont
    baseProduct := hBProd
    ambientProduct := hWProd
    pieceProducts := hQProd
    component := Z
    coordinate := hCoord
    activeTags := hTags
    focus := hFocus
    restrictions := hProtected
    source := ?_
    pieces := ?_ },hFormProd⟩
  · intro p hp
    have hPair : p ∈ W.carrier ∩ (unaryIndexedMixedFamily η A).carrier := ⟨hp,hSource hp⟩
    rw [← hSourcePreserved] at hPair
    exact hPair.2
  · intro i
    have hPieceProduct : ∀ E : D.balls,FMT.CoordinateProductDomain
        (W.carrier ∩ (unaryIndexedMixedFamily η (P i)).carrier)
          (FMT.vfOpenBall E.val) (D.centers E) 0 := by
      rw [← hPieces i]
      exact hQProd i
    exact (hPieces i).trans
      (D.unaryIndexed_restricted_family_preserved hBProd η (P i) W hWProd hPieceProduct).symm

end DiamondIntegral.Section6
