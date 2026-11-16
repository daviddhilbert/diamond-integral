import «section 6».FrozenIndexedFocusValues
import «section 6».FullFocusProtectedRealizations
import «section 6».CentripetalProgramTemplates

/-! One actual permitted joint component after continuity repair.
The whole parameter map is frozen, with every current initial source
and protected family preserved before later program data are recomputed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

structure IndexedFocusRepairCertificate
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (F : TailContinuousFullFocusGraphData (G := G) W) where
  freezing : FMT.FocusFreezingData (focusActive W F.activeTags)
  continuous : ∀ u,Continuous (FMT.focusFibre (freezing.frozenMap F.map) u)
  baseProduct : ∀ E : freezing.balls,FMT.CoordinateProductDomain B.carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) 0
  ambientProduct : ∀ E : freezing.balls,FMT.CoordinateProductDomain W.carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) 0
  pieceProducts : ∀ i,∀ E : freezing.balls,FMT.CoordinateProductDomain (Q i).carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) 0
  component : CentripetalData (G := G) W
  coordinate : component.coordinate=F.coordinate
  activeTags : component.activeTags=F.activeTags
  focus : ∀ p : focusActive W F.activeTags,component.extendedFocus p.val=(freezing.frozenMap F.map p).val 0
  restrictions : ∀ i,∃ E : CentripetalData (G := G) (Q i),ApertureRestrictionData component E
  source : W.carrier ⊆ (unaryIndexedMixedFamily (freezing.unaryParameter baseProduct η) A).carrier
  pieces : ∀ i,(Q i).carrier=W.carrier ∩
    (unaryIndexedMixedFamily (freezing.unaryParameter baseProduct η) (P i)).carrier

theorem exists_indexed_focus_repair
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
    (F : TailContinuousFullFocusGraphData (G := G) W) :
    Nonempty (IndexedFocusRepairCertificate (G := G) η A P W Q F) := by
  obtain ⟨D,hCont,hWProd,hQProd,hBProd⟩ := F.exists_frozen_full_graph_with_unary_base
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt Q hQ B hB
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
    pieces := ?_ }⟩
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

theorem IndexedFocusRepairCertificate.prepared_program_good
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S}
    {Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S}
    {F : TailContinuousFullFocusGraphData (G := G) W}
    (R : IndexedFocusRepairCertificate (G := G) η A P W Q F)
    {t : ℕ} (T : CentripetalProgramTemplate (M := M) S 1 n s t)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.preparedGood A P) :
    ∀ b : B,unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b ∈ T.preparedGood A P :=
  R.freezing.unaryParameter_good R.baseProduct η _ hGood

end DiamondIntegral.Section6
