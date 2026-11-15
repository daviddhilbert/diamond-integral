import IntegrationSection5.GammaTraceProjection
import IntegrationSection5.UniformTraceExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {n m l : ℕ}

theorem GammaUniformTrace.castSource {A A' : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) (h : A = A') :
    GammaUniformTrace (G := G) (T.castSource h) := by subst A'; exact hT

theorem GammaUniformTrace.castTarget {A : DefSet (M := M) S n m} {B B' : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) (h : B = B') :
    GammaUniformTrace (G := G) (T.castTarget h) := by subst B'; exact hT

theorem GammaUniformTrace.extendBase {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) (hSR : S ⊆ R) :
    GammaUniformTrace (G := G) (T.extendBase hSR) := by
  induction T with
  | nil A => exact hT
  | @canonical m l A B i tail ih =>
    have he : SpecialTransformations.Section5.extendBase (coordinateCanonicalImage A i) hSR =
        coordinateCanonicalImage (SpecialTransformations.Section5.extendBase A hSR) i := by
      apply PresentedSet.eq_of_carrier_eq
      rfl
    change GammaSetDefinable G (carrier (SpecialTransformations.Section5.extendBase A hSR)) ∧
      GammaUniformTrace (G := G) ((tail.extendBase hSR).castSource he)
    exact ⟨hT.1,GammaUniformTrace.castSource _ (ih hT.2) he⟩
  | @focus m l A B i k D tail ih =>
    have he : SpecialTransformations.Section5.extendBase D.image hSR = (D.extendBase hSR).image := by
      apply PresentedSet.eq_of_carrier_eq
      rfl
    change GammaSetDefinable G (carrier (SpecialTransformations.Section5.extendBase A hSR)) ∧
      GammaFibreFocusDefinable G (D.extendBase hSR) ∧ GammaUniformTrace (G := G) ((tail.extendBase hSR).castSource he)
    exact ⟨hT.1,GammaFibreFocusDefinable.extendBase D hT.2.1 hSR,GammaUniformTrace.castSource _ (ih hT.2.2) he⟩

end IntegrationInACVF.Section5
