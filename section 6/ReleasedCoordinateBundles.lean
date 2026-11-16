import «section 6».CoordinateBundleCriterion

/-! The entire regularized image of an actual released annulus is
exactly a coordinate bundle over its actual projection. All old and new
RV tags are retained, including the noncore flag. -/

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

theorem releasedRegularizedImage_bundle
    (D : CentripetalData (G := G) A) (hj : D.coordinate = Fin.last n) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    let E := D.refineCoefficient c hc0 hcdef hval
    (D.releasedRegularizedImage E).carrier =
      (rvCoordinateBundle (vfDropLast (D.releasedRegularizedImage E)).image
        (Fin.castAdd (1+r) (Fin.last n))).carrier := by
  let E := D.refineCoefficient c hc0 hcdef hval
  apply coordinate_bundle_of_replacement
  · intro q hq
    obtain ⟨a,ha,hOld,hNew,he⟩ := (D.mem_releasedRegularizedImage E q).mp hq
    rw [← he]
    simp only [regularize,Fin.append_left]
    rfl
  · intro q hq d hrv
    obtain ⟨a,ha,hOld,hNew,he⟩ := (D.mem_releasedRegularizedImage E q).mp hq
    have hrv' : rv M d = rv M ((E.point a).1 D.coordinate) := by
      rw [hj]
      exact hrv.trans (congrArg (fun p => rv M (p.1 (Fin.last n))) he.symm)
    obtain ⟨b,hb,hPoint⟩ := D.released_coordinate_replacement c hc0 hcdef hval a
      ⟨ha,hOld,hNew⟩ d hrv'
    apply (D.mem_releasedRegularizedImage E _).mpr
    refine ⟨b,hb.1,hb.2.1,hb.2.2,?_⟩
    rw [hPoint,regularize_coordinate_replacement _ _ _ hrv',he,hj]

end DiamondIntegral.Section6.CentripetalData
