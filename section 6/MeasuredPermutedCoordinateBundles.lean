import «section 6».MeasuredVFConjugatedPreparation
import «section 6».MeasuredFormCompatibleCarrying
import «section 6».CoordinateGammaConstancy

/-! Actual projected measured preparation carries through a full VF
disc in any coordinate, then conjugates to an actual permitted chain
in the original coordinates with the original form unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_coordinate_bundle_of_projected_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hW : ProperInvariant S W.carrier) (hD : VFDoublyBounded W.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S) (hPW : ∀ i,(P i).carrier ⊆ W.carrier)
    (e : Fin (n+2) ≃ Fin (n+2)) (j : Fin r)
    (hBundle : (reindexedVFSet W e).carrier=(rvCoordinateBundle (coordinateProjection W e) j).carrier)
    (hPieces : ∀ i,(reindexedVFSet (P i) e).carrier=
      (rvCoordinateBundle (coordinateProjection (P i) e) j).carrier)
    (ω : Map W (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map (coordinateProjection W e) (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ q : reindexedVFSet W e,η ((vfDropLast (reindexedVFSet W e)).toImage q)=reindexedGammaForm ω e q)
    (F : MeasuredCoordinatePreparation (G := G) (coordinateProjection W e)
      (fun i => coordinateProjection (P i) e) (fun i => coordinateProjection_subset (hPW i) e) η)
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) (coordinateProjection W e) F.target F.map
      (fun i => coordinateProjection (P i) e) η) :
    ∃ T : MeasuredCoordinatePreparation (G := G) W P hPW ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) W T.target T.map P ω := by
  obtain ⟨T,hT,hFixed⟩ := measured_form_compatible_preparation_carrying_coordinate h00 hc hκ hs hv
    (coordinateProjection_properInvariant W e hW) (coordinateProjection_doublyBounded W e hD) F hF
    j (reindexedVFSet W e) (fun i => reindexedVFSet (P i) e)
    (fun i q hq => (mem_reindexedVFSet W e q).mpr (hPW i ((mem_reindexedVFSet (P i) e q).mp hq)))
    hBundle hPieces (reindexedGammaForm ω e) (by
      intro q
      exact (gammaFormExtension_at η ((vfDropLast (reindexedVFSet W e)).toImage q)).trans
        (congrArg Subtype.val (hη q)))
  exact measured_preparation_conjugate_vf_coordinates h00 hc hκ hs hv hW hD e P hPW ω T hT

end DiamondIntegral.Section6
