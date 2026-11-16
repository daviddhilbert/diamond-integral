import «section 6».DefinableParameterDescent

/-! Actual RV objects, finite volume, Gamma forms and measured
isomorphisms under a temporary extension of the real parameter base.
All point functions and full retained label tuples are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {k : ℕ}

def extendRVObjectBase (hST : S ⊆ T) (U : RVObject (M := M) S k) : RVObject (M := M) T k where
  arity := U.arity
  domain := extendDefSetBase hST U.domain
  volume := extendMapBase hST U.volume

def extendRVHomBase (hST : S ⊆ T) {U V : RVObject (M := M) S k} (f : RVHom U V) :
    RVHom (extendRVObjectBase hST U) (extendRVObjectBase hST V) where
  map := extendMapBase hST f.map
  volumetric := f.volumetric
  finite_volume_images := f.finite_volume_images

def extendRVIsoBase (hST : S ⊆ T) {U V : RVObject (M := M) S k} (e : U ≅ V) :
    extendRVObjectBase hST U ≅ extendRVObjectBase hST V where
  hom := extendRVHomBase hST e.hom
  inv := extendRVHomBase hST e.inv
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    exact SpecialTransformations.Section7.rvIso_inv_apply e u
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    exact SpecialTransformations.Section7.rvIso_apply_inv e u

def MeasuredRVObject.extend (U : MeasuredRVObject (M := M) S k) (hST : S ⊆ T) :
    MeasuredRVObject (M := M) T k where
  object := extendRVObjectBase hST U.object
  finiteVolume := U.finiteVolume
  nonzero := U.nonzero
  form := extendMapBase hST U.form

def MeasuredRVIso.extend {U V : MeasuredRVObject (M := M) S k}
    (e : MeasuredRVIso U V) (hST : S ⊆ T) : MeasuredRVIso (U.extend hST) (V.extend hST) where
  iso := extendRVIsoBase hST e.iso
  balance := e.balance

theorem rvLift_extend_base_carrier (hST : S ⊆ T) (U : RVObject (M := M) S k) :
    (rvLift (extendRVObjectBase hST U)).carrier = (rvLift U).carrier := rfl

def MeasuredRVLiftData.measuredObject {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    {r : ℕ} {A : DefSet (rawMixedSpace (M := M) k r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (L : MeasuredRVLiftData (G := G) A ω) : MeasuredRVObject (M := M) S k where
  object := L.object
  finiteVolume := L.finiteVolume
  nonzero := fun u i he => L.valueBounded.nonzero (L.object.value u) ⟨u,rfl⟩ i (Subtype.ext he)
  form := L.rvForm

theorem MeasuredRVLiftData.measuredObject_doublyBounded {G : Type}
    [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
    {r : ℕ} {A : DefSet (rawMixedSpace (M := M) k r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (L : MeasuredRVLiftData (G := G) A ω) : L.measuredObject.doublyBounded :=
  ⟨L.domainBounded,L.valueBounded⟩

end DiamondIntegral.Section6
