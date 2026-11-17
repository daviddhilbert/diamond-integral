import «section 3».GammaGroundMeasuredRVGenerators
import «section 3».GammaGroundPrescribedWeights
import «section 3».GammaGroundRVProductLaws

/-! An empty-tuple presentation of the degree-one unit-form point.
Its label domain is literally the degree-zero unit domain; the degree
and the full measured point class are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : GammaParameters.Base (M := M))

def gammaMeasuredPointZeroArity : GammaGroundMeasuredRVObject hc B 1 := .withZeroForm {
  arity := 0
  domain := (GammaGroundRVObject.unit hc B).domain
  volume := GammaGroundMap.ofReal (rvRightTagMap (RVObject.unit B.real).domain 0)
  finite := fun _ => Set.toFinite _
  nonzero := by
    intro u i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    change iRVOne ≠ iRVZero
    exact RVCalc.rv_one_ne_zero (inferInstance : M ⊨ Axioms.ACVF) }

def gammaMeasuredPointZeroArityHom : GammaGroundMeasuredRVHom
    (gammaMeasuredPointZeroArity hc B) (gammaGroundMeasuredRVOne hc B) where
  bijection := {
    map := GammaGroundMap.ofReal (rvRightTagMap (RVObject.unit B.real).domain 0).toImage
    bijective := by
      constructor
      · intro a b _
        exact Subtype.ext (funext (fun i => i.elim0))
      · rintro ⟨_,u,rfl⟩
        exact ⟨u,rfl⟩ }
  preserves u := by
    change (1 : Values.Gamma (M := M)) * _ = 1 * _
    rfl

@[simp] theorem gammaMeasuredPointZeroArity_weight (u : (gammaMeasuredPointZeroArity hc B).underlying.domain) :
    (gammaMeasuredPointZeroArity hc B).combinedWeight u = 1 := by
  change (1 : Values.Gamma (M := M)) * (∏ i : Fin 1, Section2.rvFiniteValue _) = 1
  simp only [Fin.prod_univ_one]
  change (1 : Values.Gamma (M := M)) * Section2.rvFiniteValue ⟨⟨iRVOne,_⟩,_⟩ = 1
  rw [one_mul]
  apply Subtype.ext
  rw [Section2.rvFiniteValue_val]
  have he : (⟨iRVOne,by exact SpecialTransformations.Milestone0.Transfer.rv_one_mem inferInstance⟩ : CanonicalRV.RVSort M) = 1 :=
    Subtype.ext RVOperations.one_val.symm
  exact (congrArg Values.vrv he).trans
    ((RVOperations.vrv_one (M := M)).trans (map_one (Values.gammaValHom (M := M))).symm)

end DiamondIntegral.Section3
