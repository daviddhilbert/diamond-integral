import «section 3».GammaGroundVFFilteredComparison
import «section 3».GammaGroundVFGroupColimitCategory
import «section 3».AdditiveSemiringTransport
import «section 3».CompletionEquivalences

/-! The cartesian VF semiring is the actual filtered additive colimit,
relative to the accepted lift comparisons, and retains actual products. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}

@[instance_reducible] def gammaGroundFiniteVFCommSemiring (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    CommSemiring (GammaGroundFiniteVFKPlus hc C.base) :=
  additiveTransportCommSemiring (gammaGroundFiniteVFSemiringAddEquiv H D)

def gammaGroundFiniteVFSemiringEquiv (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    letI := gammaGroundFiniteVFCommSemiring H D
    GammaGroundFiniteVFKPlus hc C.base ≃+* GammaGroundVFPositiveSemiring hc C.base :=
  additiveTransportRingEquiv (gammaGroundFiniteVFSemiringAddEquiv H D)

theorem gammaGroundFiniteVFClass_product (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv)
    (U V : GammaGroundFiniteVFObject hc C.base) :
    letI := gammaGroundFiniteVFCommSemiring H D
    gammaGroundFiniteVFClass (U.product V) = gammaGroundFiniteVFClass U * gammaGroundFiniteVFClass V := by
  letI := gammaGroundFiniteVFCommSemiring H D
  let e := gammaGroundFiniteVFSemiringEquiv H D
  apply e.injective
  have hU : e (gammaGroundFiniteVFClass U) = gammaGroundVFSemiringClass U :=
    gammaGroundFiniteVFKPlusToSemiring_class U
  have hV : e (gammaGroundFiniteVFClass V) = gammaGroundVFSemiringClass V :=
    gammaGroundFiniteVFKPlusToSemiring_class V
  calc
    _ = gammaGroundVFSemiringClass (U.product V) := gammaGroundFiniteVFKPlusToSemiring_class _
    _ = gammaGroundVFSemiringClass U * gammaGroundVFSemiringClass V := gammaGroundVFSemiringClass_product U V
    _ = e (gammaGroundFiniteVFClass U) * e (gammaGroundFiniteVFClass V) := congrArg₂ (· * ·) hU.symm hV.symm
    _ = _ := (e.map_mul _ _).symm

def gammaGroundVFSemiringColimitCocone : Cocone (gammaGroundVFPositiveDiagram hc C.base) where
  pt := AddCommMonCat.of (GammaGroundVFPositiveSemiring hc C.base)
  ι := {
    app := fun _ => AddCommMonCat.ofHom gammaGroundVFKPlusToSemiring
    naturality := by
      intro k l f
      apply AddCommMonCat.hom_ext
      exact gammaGroundVFKPlusToSemiring_raise (leOfHom f) }

def gammaGroundVFSemiringIsColimit (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    IsColimit (gammaGroundVFSemiringColimitCocone (C := C) (hc := hc)) where
  desc s := AddCommMonCat.ofHom ((gammaGroundVFColimitLift (gammaGroundVFCompatibleOfCocone hc C.base s)).comp
    (gammaGroundFiniteVFSemiringAddEquiv H D).symm.toAddMonoidHom)
  fac s k := by
    apply AddCommMonCat.hom_ext
    apply positiveAdditivePresentationHom_ext (gammaGroundVFPresentation hc C.base k)
    intro U
    change gammaGroundVFColimitLift (gammaGroundVFCompatibleOfCocone hc C.base s)
      ((gammaGroundFiniteVFSemiringAddEquiv H D).symm (gammaGroundVFKPlusToSemiring (gammaGroundVFClass U))) = _
    have he : gammaGroundVFKPlusToSemiring (gammaGroundVFClass U) =
        gammaGroundFiniteVFSemiringAddEquiv H D (gammaGroundFiniteVFClass (.ofBound U)) := by
      change gammaGroundFiniteVFKPlusToSemiring (gammaGroundVFToFiniteKPlus (gammaGroundVFClass U)) = _
      rw [gammaGroundVFToFiniteKPlus_class]
      rfl
    rw [he, AddEquiv.symm_apply_apply, gammaGroundVFColimitLift_class]
    rfl
  uniq s m hm := by
    apply AddCommMonCat.hom_ext
    let F := gammaGroundVFCompatibleOfCocone hc C.base s
    let e := gammaGroundFiniteVFSemiringAddEquiv H D
    have he : m.hom.comp e.toAddMonoidHom = gammaGroundVFColimitLift F := by
      apply gammaGroundVFColimitLift_unique F
      intro k
      exact congrArg (fun f : (gammaGroundVFPositiveDiagram hc C.base).obj k ⟶ s.pt => f.hom) (hm k)
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := e.surjective z
    change m.hom (e x) = gammaGroundVFColimitLift F (e.symm (e x))
    rw [e.symm_apply_apply]
    exact DFunLike.congr_fun he x

def gammaGroundVFRingColimitCocone : Cocone (gammaGroundVFGroupDiagram hc C.base) :=
  additiveCompletionFunctor.mapCocone (gammaGroundVFSemiringColimitCocone (C := C) (hc := hc))

def gammaGroundVFRingIsColimit (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (D : YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv) :
    IsColimit (gammaGroundVFRingColimitCocone (C := C) (hc := hc)) :=
  isColimitOfPreserves additiveCompletionFunctor (gammaGroundVFSemiringIsColimit H D)

end DiamondIntegral.Section3
