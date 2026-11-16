import «section 6».RVCoordinateArithmeticBounds
import «section 6».RVGammaVolumeMaps

/-! Changing an actual finite volume on a fixed label domain. The
measured form is constructed as the old total weight divided by the new
volume, so the resulting identity-label isomorphism is measured. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def RVObject.withVolume (U : RVObject (M := M) S n)
    (θ : Map U.domain (DefSet.univ (rawRVSpace (M := M) n) S)) : RVObject (M := M) S n where
  arity := U.arity
  domain := U.domain
  volume := θ

def MeasuredRVObject.withVolume (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (θ : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) n) S))
    (hθF : θ.FiniteFibres) (hθ : ∀ u k, ((θ u).val k).val ≠ iRVZero) : MeasuredRVObject (M := M) S n where
  object := RVObject.withVolume U.object θ
  finiteVolume := hθF
  nonzero := hθ
  form := gammaMapDiv hc (gammaMapMul hc U.form (rvVolumeGammaMap hc U.object))
    (rvVolumeGammaMap hc (RVObject.withVolume U.object θ))

theorem MeasuredRVObject.withVolume_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (θ : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) n) S))
    (hθF : θ.FiniteFibres) (hθ : ∀ u k, ((θ u).val k).val ≠ iRVZero) (u : U.object.domain) :
    (U.withVolume hc θ hθF hθ).totalWeight u = U.totalWeight u := by
  let W := U.withVolume hc θ hθF hθ
  change ((gammaMapValue U.form u * gammaMapValue (rvVolumeGammaMap hc U.object) u) /
    gammaMapValue (rvVolumeGammaMap hc W.object) u) * W.volumeGamma u = U.totalWeight u
  rw [rvVolumeGammaMap_value hc U.object U.nonzero,rvVolumeGammaMap_value hc W.object W.nonzero]
  exact div_mul_cancel _ _

def measuredVolumeChangeIso (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n)
    (θ : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) n) S))
    (hθF : θ.FiniteFibres) (hθ : ∀ u k, ((θ u).val k).val ≠ iRVZero) :
    MeasuredRVIso U (U.withVolume hc θ hθF hθ) where
  iso := rvIsoOfFiniteVolumeNonzero (Map.id U.object.domain) Function.bijective_id
    U.finiteVolume hθF U.nonzero hθ
  balance u := (U.withVolume_totalWeight hc θ hθF hθ u).symm

def measuredCoordinateArithmeticObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :=
  U.withVolume hc (rvCoordinateArithmeticObject U.object op i j).volume
    (rvCoordinateArithmeticObject_finiteVolume U.object op i j hij U.finiteVolume U.nonzero)
    (rvCoordinateArithmeticObject_nonzero U.object op i j U.nonzero)

def measuredCoordinateArithmeticIso (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    MeasuredRVIso U (measuredCoordinateArithmeticObject hc U op i j hij) :=
  measuredVolumeChangeIso hc U _
    (rvCoordinateArithmeticObject_finiteVolume U.object op i j hij U.finiteVolume U.nonzero)
    (rvCoordinateArithmeticObject_nonzero U.object op i j U.nonzero)

theorem measuredCoordinateArithmeticIso_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    RVUnaryRelativeAt (measuredCoordinateArithmeticIso hc U op i j hij).iso.hom.map i := by
  intro u k hk
  change (rvCoordinateArithmeticObject U.object op i j).value u k = U.object.value u k
  rw [rvCoordinateArithmeticObject_value,Function.update_of_ne hk]

theorem measuredCoordinateArithmeticObject_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j)
    (hB : U.doublyBounded) : (measuredCoordinateArithmeticObject hc U op i j hij).doublyBounded :=
  rvCoordinateArithmeticObject_doublyBounded U.object op i j U.nonzero hB

end DiamondIntegral.Section6
