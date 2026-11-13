import «section 4».GammaOrdinaryFiniteMaps
import «section 4».GammaOrdinaryFiniteGrading
import «section 4».GammaOrdinaryGrading
import «section 4».RESOrdinaryGrading
import «section 4».CoactionGradedMaps

/-! Both ordinary finite-Gamma coefficient maps preserve the full
object-degree grading. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteMapGradings
open GammaOrdinaryFiniteMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem full_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (full B)).comp (GammaOrdinaryFiniteGrading.coaction B) = (GammaOrdinaryGrading.coaction B).comp (full B) := by
  apply GammaOrdinaryFiniteRing.hom_ext B
  intro n a
  change (GammaOrdinaryFiniteGrading.coaction B (GammaOrdinaryFiniteRing.objectClass a)).map (full B) =
    GammaOrdinaryGrading.coaction B (full B (GammaOrdinaryFiniteRing.objectClass a))
  rw [GammaOrdinaryFiniteGrading.coaction_class, Polynomial.map_monomial, full_class, GammaOrdinaryGrading.coaction_class]

theorem sharp_coaction (B : Base (M := M)) :
    (Polynomial.mapRingHom (sharp B)).comp (GammaOrdinaryFiniteGrading.coaction B) = (RESOrdinaryGrading.coaction B).comp (sharp B) := by
  apply GammaOrdinaryFiniteRing.hom_ext B
  intro n a
  change (GammaOrdinaryFiniteGrading.coaction B (GammaOrdinaryFiniteRing.objectClass a)).map (sharp B) =
    RESOrdinaryGrading.coaction B (sharp B (GammaOrdinaryFiniteRing.objectClass a))
  rw [GammaOrdinaryFiniteGrading.coaction_class, Polynomial.map_monomial, sharp_class, RESOrdinaryGrading.coaction_class]

theorem full_mem (B : Base (M := M)) {n : ℕ} {x : GammaOrdinaryFiniteRing.Ring B}
    (hx : x ∈ GammaOrdinaryFiniteGrading.gradedPiece B n) : full B x ∈ GammaOrdinaryGrading.gradedPiece B n := by
  change GammaOrdinaryFiniteGrading.coaction B x = Polynomial.monomial n x at hx
  change GammaOrdinaryGrading.coaction B (full B x) = Polynomial.monomial n (full B x)
  have he := RingHom.congr_fun (full_coaction B) x
  change (GammaOrdinaryFiniteGrading.coaction B x).map (full B) = GammaOrdinaryGrading.coaction B (full B x) at he
  rw [← he, hx, Polynomial.map_monomial]

theorem sharp_mem (B : Base (M := M)) {n : ℕ} {x : GammaOrdinaryFiniteRing.Ring B}
    (hx : x ∈ GammaOrdinaryFiniteGrading.gradedPiece B n) : sharp B x ∈ RESOrdinaryGrading.gradedPiece B n := by
  change GammaOrdinaryFiniteGrading.coaction B x = Polynomial.monomial n x at hx
  change RESOrdinaryGrading.coaction B (sharp B x) = Polynomial.monomial n (sharp B x)
  have he := RingHom.congr_fun (sharp_coaction B) x
  change (GammaOrdinaryFiniteGrading.coaction B x).map (sharp B) = RESOrdinaryGrading.coaction B (sharp B x) at he
  rw [← he, hx, Polynomial.map_monomial]

def gradedFull (B : Base (M := M)) : GradedRingHom (GammaOrdinaryFiniteGrading.gradedPiece B) (GammaOrdinaryGrading.gradedPiece B) where
  toRingHom := full B
  map_mem := fun hx => full_mem B hx

def gradedSharp (B : Base (M := M)) : GradedRingHom (GammaOrdinaryFiniteGrading.gradedPiece B) (RESOrdinaryGrading.gradedPiece B) where
  toRingHom := sharp B
  map_mem := fun hx => sharp_mem B hx

end DiamondIntegral.Section4.GammaOrdinaryFiniteMapGradings
