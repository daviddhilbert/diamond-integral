import «section 6».CoreBranchImages

/-! The whole actual retained core image is a coordinate bundle over
its actual projection. This includes every point of its full RV disc
and retains the true core flag and all regularization labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem coreRegularizedImage_bundle
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A)
    (hj : D.coordinate = Fin.last n) :
    D.coreRegularizedImage.carrier =
      (rvCoordinateBundle (vfDropLast D.coreRegularizedImage).image
        (Fin.castAdd (1+r) (Fin.last n))).carrier := by
  apply coordinate_bundle_of_replacement
  · intro q hq
    obtain ⟨a,ha,hCore,he⟩ := (D.mem_coreRegularizedImage h00 q).mp hq
    rw [← he]
    simp only [regularize,Fin.append_left]
    rfl
  · intro q hq d hrv
    obtain ⟨a,ha,hCore,he⟩ := (D.mem_coreRegularizedImage h00 q).mp hq
    have hrv' : rv M d = rv M ((D.point a).1 D.coordinate) := by
      rw [hj]
      exact hrv.trans (congrArg (fun p => rv M (p.1 (Fin.last n))) he.symm)
    have hmem := D.core_image_saturated ha hCore d hrv'
    rw [D.image_carrier] at hmem
    obtain ⟨b,hb,hPoint⟩ := hmem
    have hCoreB : D.core b = true := by
      have hh := congrArg (fun p : Mixed M (n+1) (1+r) => p.2 (Fin.castAdd r (0 : Fin 1))) hPoint
      simp only [point,Fin.append_left,hCore] at hh
      exact branchTag_injective h00 hh
    apply (D.mem_coreRegularizedImage h00 _).mpr
    refine ⟨b,hb,hCoreB,?_⟩
    rw [hPoint,regularize_coordinate_replacement _ _ _ hrv',he,hj]

def coreProjection (D : CentripetalData (G := G) A) := (vfDropLast D.coreRegularizedImage).image

theorem coreProjection_doublyBounded (D : CentripetalData (G := G) A) :
    VFDoublyBounded D.coreProjection.carrier :=
  vfDropLast_image_doublyBounded D.coreRegularizedImage_doublyBounded

theorem coreProjection_tagged (D : CentripetalData (G := G) A) :
    ∀ p ∈ D.coreProjection.carrier, ∀ q ∈ D.coreProjection.carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 :=
  vfDropLast_image_tagged D.coreRegularizedImage_tagged

theorem coreProjection_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A) : ProperInvariant S D.coreProjection.carrier :=
  vfDropLast_image_properInvariant (D.coreRegularizedImage_properInvariant h00 hc hκ hs hv)

end DiamondIntegral.Section6.CentripetalData
