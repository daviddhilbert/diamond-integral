import «section 3».GammaGroundRVUnitProducts
import «section 3».FullGammaFunctions
import «section 3».GammaGroundBijectionRestrictions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- A product chart retaining the Gamma function that gives its weight.
The source space and ambient factor arities do not encode label degree. -/
structure GammaGroundRVFormProductChart (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (Q : Space LRV M) (w : Q.Carrier → Values.Gamma (M := M)) where
  source : GammaGroundDefSet hc B Q
  residueArity : ℕ
  gammaArity : ℕ
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) residueArity)
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin gammaArity))
  residue_finite : (rvUnitTupleValues '' residue.carrier).Finite
  bijection : GammaGroundBijection source (residue.prod (gammaGroundRVUnitGammaPreimage gamma))
  weight : (Fin gammaArity → Values.Gamma (M := M)) → Values.Gamma (M := M)
  weight_definable : FullGammaFunction (integrationGammaBase B) weight
  preserves : ∀ a, w a.val = weight (rvUnitTupleValues (bijection.map a).val.2)

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {Q P : Space LRV M} {w : Q.Carrier → Values.Gamma (M := M)}

def GammaGroundRVFormProductChart.pullback
    (C : GammaGroundRVFormProductChart hc B Q w)
    {A : GammaGroundDefSet hc B P} {T : GammaGroundDefSet hc B Q}
    (f : GammaGroundBijection A T) (hC : C.source.carrier ⊆ T.carrier)
    (v : P.Carrier → Values.Gamma (M := M)) (hv : ∀ a : A, v a.val = w (f.map a).val) :
    GammaGroundRVFormProductChart hc B P v where
  source := f.inverseImage C.source
  residueArity := C.residueArity
  gammaArity := C.gammaArity
  residue := C.residue
  gamma := C.gamma
  residue_finite := C.residue_finite
  bijection := C.bijection.comp (f.restrictTarget C.source hC)
  weight := C.weight
  weight_definable := C.weight_definable
  preserves a := (hv ⟨a.val,f.inverseImage_subset C.source a.property⟩).trans
    (C.preserves ((f.restrictTarget C.source hC).map a))
end DiamondIntegral.Section3
