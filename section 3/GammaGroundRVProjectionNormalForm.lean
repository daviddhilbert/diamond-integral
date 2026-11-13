import «section 3».GammaGroundRVProducts
import «section 3».GammaGroundRVScissors

/-! Every actual RV object is isomorphic to its graph, with the original
finite-to-one label map realized as the first coordinate projection. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundRVObject.graphMap (U : GammaGroundRVObject hc ground k) :
    GammaGroundMap U.domain (GammaGroundDefSet.univ hc ground (rawRVSpace (k + U.arity))) :=
  (gammaGroundRVPack (GammaGroundDefSet.univ hc ground (rawRVSpace k)) U.domain).comp (U.volume.pair (GammaGroundMap.id U.domain))

theorem GammaGroundRVObject.graphMap_injective (U : GammaGroundRVObject hc ground k) : Function.Injective U.graphMap := by
  intro a b he
  have hp := rvAppend_injective (congrArg Subtype.val he)
  exact Subtype.ext (congrArg Prod.snd hp)

def GammaGroundRVObject.graphBijection (U : GammaGroundRVObject hc ground k) : GammaGroundBijection U.domain U.graphMap.image where
  map := U.graphMap.toImage
  bijective := by
    constructor
    · intro a b he
      apply U.graphMap_injective
      exact Subtype.ext (congrArg (fun x : U.graphMap.image => x.val) he)
    · rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩

def GammaGroundRVObject.projectionObject (U : GammaGroundRVObject hc ground k) : GammaGroundRVObject hc ground k where
  arity := k + U.arity
  domain := U.graphMap.image
  volume := U.volume.comp U.graphBijection.symm.map
  finite := U.finite.comp (GammaGroundMap.finiteFibres_of_injective U.graphBijection.symm.bijective.injective)
  nonzero a := U.nonzero (U.graphBijection.symm.map a)

def GammaGroundRVObject.projectionIso (U : GammaGroundRVObject hc ground k) : U ≅ U.projectionObject :=
  asIso (show U ⟶ U.projectionObject from U.graphBijection)

theorem GammaGroundRVObject.projectionObject_volume (U : GammaGroundRVObject hc ground k)
    (a : U.projectionObject.domain) (i : Fin k) :
    (U.projectionObject.volume a).val i = a.val (Fin.castAdd U.arity i) := by
  obtain ⟨u, rfl⟩ := U.graphBijection.bijective.surjective a
  change (U.volume (U.graphBijection.symm.map (U.graphBijection.map u))).val i = _
  rw [GammaGroundBijection.symm, GammaGroundMap.inverse_apply]
  change (U.volume u).val i = rvAppend (U.volume u).val u.val (Fin.castAdd U.arity i)
  rw [rvAppend, Fin.append_left]

theorem gammaGroundRVClass_projectionObject (U : GammaGroundRVObject hc ground k) : gammaGroundRVClass U.projectionObject = gammaGroundRVClass U :=
  (gammaGroundRVClass_iso U.projectionIso).symm

end DiamondIntegral.Section3
