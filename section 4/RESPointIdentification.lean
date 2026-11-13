import «section 4».RESPointTuples
import «section 4».RESFibreObjects

/-! The explicit degree-one point tuple is the manuscript's actual
proper RV point object, via an original-base underlying bijection. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESPointIdentification
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem point_domain (B : Base (M := M)) :
    (RESPointTuples.chart B 1).domain = (RESFibreObjects.point B).domain := by
  ext z
  change z = RESPointTuples.tuple 1 ↔ z = ![raw (RVRadiusGenerators.oneCode (M := M))]
  have he : RESPointTuples.tuple (M := M) 1 = ![raw (RVRadiusGenerators.oneCode (M := M))] := by
    funext i
    fin_cases i
    rfl
  rw [he]

def pointIso (B : Base (M := M)) : RVForgetScissors.UnderlyingIso
    (RESPointTuples.chart B 1) (RESFibreObjects.point B).toChart :=
  RVUnderlyingIsomorphisms.toFixed (RVUnderlyingIsomorphisms.ofMap
    (RESPointTuples.chart B 1) (RESFibreObjects.point B).toChart id
    (RVSharpCharts.identity_graph_definable B _ (RESPointTuples.tuple_definable B 1))
    ⟨(fun u hu => point_domain B ▸ hu), (fun _ _ _ _ h => h),
      (fun u hu => ⟨u, (point_domain B).symm ▸ hu, rfl⟩)⟩)

theorem ordinary_point (B : Base (M := M)) :
    RESOrdinaryRing.objectClass (RESPointTuples.res B 1) = RESOrdinaryRing.objectClass (RESFibreObjects.point B) :=
  RESOrdinaryRing.objectClass_iso (pointIso B)

end DiamondIntegral.Section4.RESPointIdentification
