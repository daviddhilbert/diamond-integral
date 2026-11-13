import «section 4».GammaFiniteRVMaps
import «section 4».GammaFiniteRVGrading
import «section 4».GammaRVMapGradings
import «section 4».GammaBoundedRVProfiles

/-! All actual finite-Gamma coefficient maps preserve the full gradings. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteRVMapGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradedForget (B : Base (M := M)) :
    GradedRingHom (GammaFiniteRVGrading.gradedPiece B) (GammaRVGrading.gradedPiece B) where
  toRingHom := GammaFiniteRVMaps.forget B
  map_mem := GammaFiniteRVGrading.map_mem_of_classes B (GammaRVGrading.gradingCoaction B)
    (GammaFiniteRVMaps.forget B) (by
      intro n a
      rw [GammaFiniteRVMaps.forget_class]
      exact GammaRVGrading.class_mem B a.toChart)

def gradedBounded (B : Base (M := M)) :
    GradedRingHom (GammaFiniteRVGrading.gradedPiece B) (GammaBoundedRVGrading.gradedPiece B) where
  toRingHom := GammaFiniteRVMaps.bounded B
  map_mem := GammaFiniteRVGrading.map_mem_of_classes B (GammaBoundedRVGrading.gradingCoaction B)
    (GammaFiniteRVMaps.bounded B) (by
      intro n a
      rw [GammaFiniteRVMaps.bounded_class]
      exact GammaBoundedRVGrading.class_mem B _)

def gradedSharp (B : Base (M := M)) :
    GradedRingHom (GammaFiniteRVGrading.gradedPiece B) (RESRingCoaction.gradedPiece B) where
  toRingHom := GammaFiniteRVMaps.sharp B
  map_mem := GammaFiniteRVGrading.map_mem_of_classes B (RESGrading.gradingCoaction B)
    (GammaFiniteRVMaps.sharp B) (by
      intro n a
      rw [GammaFiniteRVMaps.sharp_class]
      exact RESRingCoaction.class_mem_gradedPiece B _)

end DiamondIntegral.Section4.GammaFiniteRVMapGradings
