import «section 3».RVProducts
import «section 3».RVScissors

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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVObject.graphMap (U : RVObject (M := M) S k) :
    Map U.domain (DefSet.univ (rawRVSpace (k + U.arity)) S) :=
  (rvPack (DefSet.univ (rawRVSpace k) S) U.domain).comp (U.volume.pair (Map.id U.domain))

theorem RVObject.graphMap_injective (U : RVObject (M := M) S k) : Function.Injective U.graphMap := by
  intro a b he
  have hp := rvAppend_injective (congrArg Subtype.val he)
  exact Subtype.ext (congrArg Prod.snd hp)

def RVObject.graphBijection (U : RVObject (M := M) S k) : DefinableBijection U.domain U.graphMap.image where
  map := U.graphMap.toImage
  bijective := by
    constructor
    · intro a b he
      apply U.graphMap_injective
      exact Subtype.ext (congrArg (fun x : U.graphMap.image => x.val) he)
    · rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩

def RVObject.projectionObject (U : RVObject (M := M) S k) : RVObject S k where
  arity := k + U.arity
  domain := U.graphMap.image
  volume := U.volume.comp U.graphBijection.symm.map
  finite := U.finite.comp (Map.finiteFibres_of_injective U.graphBijection.symm.bijective.injective)
  nonzero a := U.nonzero (U.graphBijection.symm.map a)

def RVObject.projectionIso (U : RVObject (M := M) S k) : U ≅ U.projectionObject :=
  asIso (show U ⟶ U.projectionObject from U.graphBijection)

theorem RVObject.projectionObject_volume (U : RVObject (M := M) S k)
    (a : U.projectionObject.domain) (i : Fin k) :
    (U.projectionObject.volume a).val i = a.val (Fin.castAdd U.arity i) := by
  obtain ⟨u, rfl⟩ := U.graphBijection.bijective.surjective a
  change (U.volume (U.graphBijection.symm.map (U.graphBijection.map u))).val i = _
  rw [U.graphBijection.symm_apply_apply]
  change (U.volume u).val i = rvAppend (U.volume u).val u.val (Fin.castAdd U.arity i)
  rw [rvAppend, Fin.append_left]

theorem rvClass_projectionObject (U : RVObject (M := M) S k) : rvClass U.projectionObject = rvClass U :=
  (rvClass_iso U.projectionIso).symm

end DiamondIntegral.Section3
