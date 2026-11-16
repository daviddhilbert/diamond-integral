import «section 6».MeasuredVFReindexedPreparation
import «section 6».VFConjugatedPreparation

/-! Preparation in permuted VF coordinates returns to literal original
coordinates through actual permitted operations. The original Gamma
map and all protected images are recovered exactly. -/

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

theorem measured_preparation_conjugate_vf_coordinates
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (e : Fin (n+1) ≃ Fin (n+1)) (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (F : MeasuredCoordinatePreparation (G := G) (reindexedVFSet A e)
      (fun i => reindexedVFSet (P i) e) (fun i q hq =>
        (mem_reindexedVFSet A e q).mpr (hPA i ((mem_reindexedVFSet (P i) e q).mp hq))) (reindexedGammaForm ω e))
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) (reindexedVFSet A e) F.target F.map
      (fun i => reindexedVFSet (P i) e) (reindexedGammaForm ω e)) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A P hPA ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) A T.target T.map P ω := by
  let X := VFReindexRefinementFrame.conjugation A e hA hD
  obtain ⟨K,hK⟩ := F.refine_vf_coordinates_form_compatible h00 hc hκ hs hv hF X
  have hForm (p : A) : (((reindexedGammaForm ω e).comp X.oldMap) p).val=(ω p).val := by
    have hPoint : reindexVFInverseMap A e (X.oldMap p)=p := by
      apply Subtype.ext
      change reindexVFPoint e.symm (reindexVFPoint e (p.val.1,p.val.2 ∘ id))=p.val
      rw [Function.comp_id,reindexVFPoint_inverse]
      rfl
    change (ω (reindexVFInverseMap A e (X.oldMap p))).val=(ω p).val
    rw [hPoint]
  let T : MeasuredCoordinatePreparation (G := G) A P hPA ω :=
    (K.changeForm hForm).changePieces (fun i => VFReindexRefinementFrame.conjugation_piece A e hA hD (P i) (hPA i))
  exact ⟨T,(hK.changeForm hForm).changePieces (fun i =>
    VFReindexRefinementFrame.conjugation_piece A e hA hD (P i) (hPA i))⟩

end DiamondIntegral.Section6
