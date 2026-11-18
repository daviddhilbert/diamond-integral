import «section 3».GammaZeroMeasuredObjects
import «section 3».GammaGroundMeasuredRVFinitePartitions

/-! Literal cuts commute with degree-zero measured descent, before any
group completion or use of a lifting/kernel comparison. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : GammaParameters.Base (M := M)}

theorem gammaZeroLabelBijection_inverse_label (U : GammaGroundZeroMeasuredVF hc B)
    (t : (gammaZeroLabelProjection U).image) :
    ((gammaZeroLabelBijection U).symm.map t).val.2 = t.val := by
  exact congrArg Subtype.val ((gammaZeroLabelBijection U).map.apply_inverse
    (gammaZeroLabelBijection U).bijective t)

def gammaZeroCutImage (U : GammaGroundZeroMeasuredVF hc B)
    (X : GammaGroundDefSet hc B (rawMixedSpace (M := M) 0 U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) :=
  ((gammaZeroLabelProjection U).restrict hX).image

theorem gammaZeroCutImage_subset (U : GammaGroundZeroMeasuredVF hc B)
    (X : GammaGroundDefSet hc B (rawMixedSpace (M := M) 0 U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    (gammaZeroCutImage U X hX).carrier ⊆ (gammaZeroRVOfVF U).underlying.domain.carrier := by
  rintro t ⟨x,hx⟩
  exact ⟨⟨x.val,hX x.property⟩,hx⟩

def gammaZeroRVRestrictionIso (U : GammaGroundZeroMeasuredVF hc B)
    (X : GammaGroundDefSet hc B (rawMixedSpace (M := M) 0 U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    gammaZeroRVOfVF (U.restrict X hX) ≅
      (gammaZeroRVOfVF U).restrict (gammaZeroCutImage U X hX)
        (gammaZeroCutImage_subset U X hX) := by
  let f : gammaZeroRVOfVF (U.restrict X hX) ⟶
      (gammaZeroRVOfVF U).restrict (gammaZeroCutImage U X hX)
        (gammaZeroCutImage_subset U X hX) := {
    bijection := GammaGroundBijection.ofCarrierEq rfl
    preserves := by
      intro t
      rw [GammaGroundMeasuredRVObject.zero_combinedWeight,
        GammaGroundMeasuredRVObject.zero_combinedWeight]
      change gammaGroundFormValue U.form
          ⟨((gammaZeroLabelBijection (U.restrict X hX)).symm.map t).val,
            hX ((gammaZeroLabelBijection (U.restrict X hX)).symm.map t).property⟩ =
        gammaGroundFormValue U.form
          ((gammaZeroLabelBijection U).symm.map
            ⟨t.val,gammaZeroCutImage_subset U X hX t.property⟩)
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · exact funext (fun i => i.elim0)
      · exact (gammaZeroLabelBijection_inverse_label (U.restrict X hX) t).trans
          (gammaZeroLabelBijection_inverse_label U
            ⟨t.val,gammaZeroCutImage_subset U X hX t.property⟩).symm }
  exact asIso f

theorem gammaZeroCutImage_complement (U : GammaGroundZeroMeasuredVF hc B)
    (X : GammaGroundDefSet hc B (rawMixedSpace (M := M) 0 U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    (gammaZeroCutImage U (U.domain.sdiff X) (fun _ h => h.1)).carrier =
      ((gammaZeroRVOfVF U).underlying.domain.sdiff (gammaZeroCutImage U X hX)).carrier := by
  ext t
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨⟨⟨u.val,u.property.1⟩,hu⟩,?_⟩
    rintro ⟨v,hv⟩
    apply u.property.2
    have he : u.val = v.val := Prod.ext (funext (fun i => i.elim0))
      (hu.trans hv.symm)
    exact he.symm ▸ v.property
  · rintro ⟨⟨u,hu⟩,hn⟩
    have hux : u.val ∉ X.carrier := by
      intro hx
      exact hn ⟨⟨u.val,hx⟩,hu⟩
    exact ⟨⟨u.val,u.property,hux⟩,hu⟩

end DiamondIntegral.Section3
