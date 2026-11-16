import «section 6».FormCompatibleRVRefinement
import «section 6».MeasuredPreparationTransport

/-! Actual measured preparation lifts through a refinement of RV labels,
retaining its component form condition, exact Gamma values, target
constancy, tagged geometry and every literal protected image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem MeasuredCoordinatePreparation.refine_rv_labels_form_compatible
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F : MeasuredCoordinatePreparation (G := G) A P hPA ω)
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) A F.target F.map P ω)
    (X : RVRefinementFrame A) :
    ∃ T : MeasuredCoordinatePreparation (G := G) X.base (fun i => X.selectedPiece (P i))
        (fun i => X.selectedPiece_subset (P i)) (ω.comp X.oldMap),
      FormCompatibleSynchronizedChain (G := G) (Fin k) X.base T.target T.map
        (fun i => X.selectedPiece (P i)) (ω.comp X.oldMap) := by
  obtain ⟨K,hK⟩ := hF.rv_refinement_lift_exists h00 hc hκ hs hv X
  have hPrepared (i) : IsRVPullback (K.map.restrict (X.selectedPiece_subset (P i))).image.carrier := by
    rw [K.partition_image h00 (F.special.bijective h00).injective i (hPA i)]
    apply labelRefinement_pullback (F.map.restrict (hPA i)).image
      (K.target.selectedPiece (F.map.restrict (hPA i)).image) K.target.labels
      (K.target.selectedPiece_fibres _ ?_) (F.pieces i).2
    rintro q ⟨p,hp⟩
    exact hp ▸ (F.map.restrict (hPA i) p).property
  refine ⟨{
    arity := K.target.arity
    target := K.target.base
    map := K.map
    special := hK.toSynchronized.toChain.toSpecial
    proper := K.target.proper
    doublyBounded := K.target.doublyBounded
    prepared := K.target.pullback F.prepared
    tagged := labelRefinement_tagged F.target K.target.base K.target.labels K.target.fibres F.tagged
    form := F.form.comp K.target.oldMap
    transport := K.gamma_form_transport ω F.form F.transport
    constant := K.target.gamma_form_constant F.form F.constant
    pieces := fun i => ⟨(hK.toSynchronized.atPiece i).literal_restriction h00 (X.selectedPiece_subset (P i)),hPrepared i⟩ },hK⟩

end DiamondIntegral.Section6
