import «section 3».GammaGroundTopForms
import «section 3».GammaGroundEqualizers

/-! A nowhere-zero top-valued form is a genuine Gamma form over the
same base. The complete graph is pulled through the existing imaginary
inclusion; no RV representative is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q : Space LRV M} {A : GammaGroundDefSet hc B Q}

def GammaGroundTopForm.finite (ω : GammaGroundTopForm hc B A)
    (hω : ∀ a, (ω a).val ≠ Values.infinity (M := M)) : GammaGroundVolumeForm hc B A where
  toFun a := ⟨⟨(ω a).val,hω a⟩,Set.mem_univ _⟩
  graph_definable := by
    let G := GammaGroundDefSet.univ hc B (volumeGammaSpace hc)
    let left := ω.comp (GammaGroundMap.prodFst A G)
    let inclusion : GammaGroundMap G (GammaGroundDefSet.univ hc B gammaTopSpace) :=
      GammaGroundMap.ofGlobal G _ (gammaIncludeTopMap hc B.real) (fun _ => Set.mem_univ _)
    let right := inclusion.comp (GammaGroundMap.prodSnd A G)
    apply (left.equalizer right).definable.congr
    intro z
    constructor
    · rintro ⟨a,ha,he⟩
      let p : A := ⟨a.val.1,a.property.1⟩
      refine ⟨p,congrArg Prod.fst ha,?_⟩
      apply Subtype.ext
      exact he.trans (congrArg (fun x : Q.Carrier × (volumeGammaSpace hc).Carrier => x.2.val) ha)
    · rintro ⟨p,hp,hγ⟩
      let a : A.prod G := ⟨(p.val,z.2),p.property,Set.mem_univ _⟩
      refine ⟨a,Prod.ext hp rfl,?_⟩
      have he := congrArg (fun γ : Values.Gamma (M := M) => γ.val) hγ
      exact he

theorem GammaGroundTopForm.finite_value (ω : GammaGroundTopForm hc B A)
    (hω : ∀ a, (ω a).val ≠ Values.infinity (M := M)) (a : A) :
    (gammaGroundFormValue (ω.finite hω) a).val = (ω a).val := rfl

end DiamondIntegral.Section3
