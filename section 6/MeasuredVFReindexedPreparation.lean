import «section 6».FormCompatibleVFReindexing
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

theorem MeasuredCoordinatePreparation.refine_vf_coordinates_form_compatible
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F : MeasuredCoordinatePreparation (G := G) A P hPA ω)
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) A F.target F.map P ω)
    {e : Fin (n+1) ≃ Fin (n+1)} (X : VFReindexRefinementFrame A e) :
    ∃ T : MeasuredCoordinatePreparation (G := G) X.data.base (fun i => X.selectedPiece (P i))
        (fun i => X.selectedPiece_subset (P i)) (ω.comp X.oldMap),
      FormCompatibleSynchronizedChain (G := G) (Fin k) X.data.base T.target T.map
        (fun i => X.selectedPiece (P i)) (ω.comp X.oldMap) := by
  obtain ⟨K,hK⟩ := hF.vf_reindexed_lift_exists h00 hc hκ hs hv X
  have hPrepared (i) : IsRVPullback (K.map.restrict (X.selectedPiece_subset (P i))).image.carrier := by
    rw [K.partition_image h00 (F.special.bijective h00).injective i (hPA i)]
    apply labelRefinement_pullback (reindexedVFSet (F.map.restrict (hPA i)).image e)
      (K.target.data.selectedPiece (reindexedVFSet (F.map.restrict (hPA i)).image e)) K.target.data.labels
      (K.target.data.selectedPiece_fibres _ ?_) (reindexedVFSet_rvPullback _ e (F.pieces i).2)
    intro q hq
    apply (mem_reindexedVFSet F.target e q).mpr
    obtain ⟨p,hp⟩ := (mem_reindexedVFSet (F.map.restrict (hPA i)).image e q).mp hq
    exact hp ▸ (F.map.restrict (hPA i) p).property
  refine ⟨{
    arity := K.target.data.arity
    target := K.target.data.base
    map := K.map
    special := hK.toSynchronized.toChain.toSpecial
    proper := K.target.data.proper
    doublyBounded := K.target.data.doublyBounded
    prepared := K.target.data.pullback (reindexedVFSet_rvPullback F.target e F.prepared)
    tagged := labelRefinement_tagged (reindexedVFSet F.target e) K.target.data.base K.target.data.labels
      K.target.data.fibres (reindexedVFSet_tagged F.target e F.tagged)
    form := F.form.comp K.target.oldMap
    transport := K.gamma_form_transport ω F.form F.transport
    constant := K.target.gamma_form_constant F.form F.constant
    pieces := fun i => ⟨(hK.toSynchronized.atPiece i).literal_restriction h00 (X.selectedPiece_subset (P i)),hPrepared i⟩ },hK⟩

end DiamondIntegral.Section6
