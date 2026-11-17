import «section 3».GammaGroundVolumeForms

/-! A genuine Gamma form extends by one outside its definable domain.
This permits arbitrary old-label forms in the saved coordinate-preserving
geometric constructions without extra label-membership choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q : Space LRV M} {A : GammaGroundDefSet hc B Q}

def GammaGroundVolumeForm.extendByOne (ω : GammaGroundVolumeForm hc B A) :
    GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B Q) where
  toFun a := if h : a.val ∈ A.carrier then ω ⟨a.val,h⟩ else gammaGroundOneForm _ a
  graph_definable := by
    let E := GammaGroundDefSet.univ hc B Q
    let one := gammaGroundOneForm E
    have hA := A.definable.preimage (universalProductFst Q (volumeGammaSpace hc) B.real)
    apply (ω.graph_definable.union (one.graph_definable.inter hA.compl)).congr
    intro z
    constructor
    · rintro (⟨p,hp,hw⟩ | ⟨⟨a,ha,hw⟩,hn⟩)
      · refine ⟨⟨p.val,Set.mem_univ _⟩,hp,?_⟩
        simpa only [dite_eq_left p.property] using hw
      · have hnot : a.val ∉ A.carrier := ha.symm ▸ hn
        refine ⟨a,ha,?_⟩
        simpa only [dite_eq_right hnot] using hw
    · rintro ⟨a,ha,hw⟩
      by_cases hm : a.val ∈ A.carrier
      · left
        exact ⟨⟨a.val,hm⟩,ha,by simpa only [dite_eq_left hm] using hw⟩
      · right
        refine ⟨⟨a,ha,by simpa only [dite_eq_right hm] using hw⟩,?_⟩
        change z.1 ∉ A.carrier
        exact ha ▸ hm

theorem GammaGroundVolumeForm.extendByOne_apply (ω : GammaGroundVolumeForm hc B A) (a : A) :
    ω.extendByOne ⟨a.val,Set.mem_univ _⟩ = ω a := by
  change (if h : a.val ∈ A.carrier then ω ⟨a.val,h⟩ else _) = _
  rw [dite_eq_left a.property]

end DiamondIntegral.Section3
