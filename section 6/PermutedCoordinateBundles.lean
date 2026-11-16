import «section 6».VFConjugatedPreparation
import «section 6».PreparedSynchronizedCarrying
import «section 6».CoordinateBundleCriterion

/-! Actual coordinate bundles can be projected and prepared in any
VF coordinate, with conjugation back to a literal original-coordinate
chain and all protected pieces retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def coordinateProjection (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (e : Fin (n+1) ≃ Fin (n+1)) := (vfDropLast (reindexedVFSet W e)).image

theorem coordinateProjection_subset
    {W P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hPW : P.carrier ⊆ W.carrier) (e : Fin (n+1) ≃ Fin (n+1)) :
    (coordinateProjection P e).carrier ⊆ (coordinateProjection W e).carrier := by
  rintro q ⟨p,hp⟩
  refine ⟨⟨p.val,(mem_reindexedVFSet W e p.val).mpr
    (hPW ((mem_reindexedVFSet P e p.val).mp p.property))⟩,hp⟩

theorem coordinateProjection_properInvariant
    (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (e : Fin (n+1) ≃ Fin (n+1)) (hW : ProperInvariant S W.carrier) :
    ProperInvariant S (coordinateProjection W e).carrier :=
  vfDropLast_image_properInvariant (reindexedVFSet_properInvariant W e hW)

theorem coordinateProjection_doublyBounded
    (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (e : Fin (n+1) ≃ Fin (n+1)) (hW : VFDoublyBounded W.carrier) :
    VFDoublyBounded (coordinateProjection W e).carrier :=
  vfDropLast_image_doublyBounded (reindexedVFSet_doublyBounded W e hW)

theorem reindexed_coordinate_bundle_of_replacement
    (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (e : Fin (n+1) ≃ Fin (n+1)) (j : Fin (n+1)) (hj : e (Fin.last n)=j) (k : Fin r)
    (htag : ∀ p ∈ W.carrier,rv M (p.1 j)=p.2 k)
    (hreplace : ∀ p ∈ W.carrier,∀ d : VF M,rv M d=rv M (p.1 j) →
      (Function.update p.1 j d,p.2) ∈ W.carrier) :
    (reindexedVFSet W e).carrier=(rvCoordinateBundle (coordinateProjection W e) k).carrier := by
  apply coordinate_bundle_of_replacement
  · intro p hp
    have h := htag (reindexVFPoint e.symm p) ((mem_reindexedVFSet W e p).mp hp)
    rw [← hj] at h
    simpa only [reindexVFPoint,Function.comp_apply,Equiv.symm_apply_apply] using h
  · intro p hp d hd
    apply (mem_reindexedVFSet W e _).mpr
    have h := hreplace (reindexVFPoint e.symm p) ((mem_reindexedVFSet W e p).mp hp) d (by
      rw [← hj]
      simpa only [reindexVFPoint,Function.comp_apply,Equiv.symm_apply_apply] using hd)
    change (Function.update p.1 (Fin.last n) d ∘ e.symm,p.2) ∈ W.carrier
    rw [update_comp_fin_equiv]
    simpa only [Equiv.symm_symm,hj,reindexVFPoint] using h

theorem synchronized_coordinate_bundle_of_projected_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hW : ProperInvariant S W.carrier) (hD : VFDoublyBounded W.carrier)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hPW : ∀ i,(P i).carrier ⊆ W.carrier)
    (e : Fin (n+1) ≃ Fin (n+1)) (k : Fin r)
    (hBundle : (reindexedVFSet W e).carrier=(rvCoordinateBundle (coordinateProjection W e) k).carrier)
    (hPieces : ∀ i,(reindexedVFSet (P i) e).carrier=
      (rvCoordinateBundle (coordinateProjection (P i) e) k).carrier)
    (F : PreparedSynchronizedFamily (G := G) (coordinateProjection W e)
      (fun i => coordinateProjection (P i) e) (fun i => coordinateProjection_subset (hPW i) e)) :
    Nonempty (PreparedSynchronizedFamily (G := G) W P hPW) := by
  obtain ⟨T,_⟩ := F.carrying_coordinate h00 hc hκ hs hv
    (coordinateProjection_properInvariant W e hW) (coordinateProjection_doublyBounded W e hD)
    k (reindexedVFSet W e) (fun i => reindexedVFSet (P i) e)
    (fun i q hq => (mem_reindexedVFSet W e q).mpr (hPW i ((mem_reindexedVFSet (P i) e q).mp hq)))
    hBundle hPieces
  exact T.conjugate_vf_coordinates h00 hc hκ hs hv hW hD e P hPW

end DiamondIntegral.Section6
