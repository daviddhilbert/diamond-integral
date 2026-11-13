import «section 3».RVUnitTupleProducts
import «section 3».GammaGroundGraphSets
import «section 3».GammaGroundRVUnitRES
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}
variable {A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
variable {D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)}

/-- Actual graph tuples retain literal input and output coordinates in
one RV-unit tuple, over the original mixed ground. -/
def GammaGroundMap.unitGraphMap (f : GammaGroundMap A D) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) (n+m))) :=
  (gammaGroundRVUnitTupleProductMap f.graphSet).comp f.graphPair

theorem GammaGroundMap.unitGraphMap_injective (f : GammaGroundMap A D) : Function.Injective f.unitGraphMap :=
  (gammaGroundRVUnitTupleProductMap_injective f.graphSet).comp f.graphPair_bijective.1

def GammaGroundMap.unitGraphBijection (f : GammaGroundMap A D) : GammaGroundBijection A f.unitGraphMap.image :=
  ⟨f.unitGraphMap.toImage,f.unitGraphMap.toImage_bijective f.unitGraphMap_injective⟩

theorem GammaGroundMap.unitGraph_input_injective (f : GammaGroundMap A D) :
    Set.InjOn (fun z => z ∘ Fin.castAdd m) f.unitGraphMap.image.carrier := by
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩ hab
  have he : a = b := by
    apply Subtype.ext
    funext i
    have hi := congrFun hab i
    change Fin.append a.val (f a).val (Fin.castAdd m i) = Fin.append b.val (f b).val (Fin.castAdd m i) at hi
    simpa only [Fin.append_left] using hi
  subst b
  rfl

theorem GammaGroundMap.unitGraph_output_injective (f : GammaGroundMap A D) (hf : Function.Injective f) :
    Set.InjOn (fun z => z ∘ Fin.natAdd n) f.unitGraphMap.image.carrier := by
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩ hab
  have he : f a = f b := by
    apply Subtype.ext
    funext i
    have hi := congrFun hab i
    change Fin.append a.val (f a).val (Fin.natAdd n i) = Fin.append b.val (f b).val (Fin.natAdd n i) at hi
    simpa only [Fin.append_right] using hi
  have hab' := hf he
  subst b
  rfl

def GammaGroundMap.unitGraphLabel (f : GammaGroundMap A D) :
    GammaGroundMap f.unitGraphMap.image (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) n)) :=
  (gammaGroundRVUnitToRVMap A).comp f.unitGraphBijection.symm.map

theorem GammaGroundMap.unitGraphLabel_finite (f : GammaGroundMap A D) : f.unitGraphLabel.FiniteFibres :=
  (GammaGroundMap.finiteFibres_of_injective (gammaGroundRVUnitToRVMap_injective A)).comp
    (GammaGroundMap.finiteFibres_of_injective f.unitGraphBijection.symm.bijective.1)
end DiamondIntegral.Section3
