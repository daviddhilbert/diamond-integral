import IntegrationSection5.FiniteMixedRVFibres
import IntegrationSection5.NaturalContractionGamma

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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}

theorem rv_volume_finite_of_lift_finite
    (U : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S n)
    (hU : @FiniteMixedRVFibres M sM n (rvObjectArity U) (carrier (rawLift U))) :
    Map.FiniteFibres (rvObjectVolume U) := by
  intro t
  choose x hx using fun i => @CanonicalRV.encodedRv_surjective M sM _ (t.val i)
  have hfin := (hU x).preimage (f := fun u : rvObjectDomain U => u.val) Subtype.val_injective.injOn
  apply hfin.subset
  intro u hu
  change (x,u.val) ∈ carrier (rawLift U)
  refine ⟨u,rfl,?_⟩
  funext i
  change (rvObjectVolume U u).val i =
    @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
      (CanonicalStructure.normalized_model hM) n x i
  rw [normalized_tupleRV,hu]
  exact (hx i).symm

namespace StandardContraction
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

def gammaNaturalLiftIso (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program) :
    GammaIso G (carrier A) (carrier (rawLift C.contractionObject)) where
  equiv := Equiv.ofBijective C.naturalLiftMap C.naturalLiftMap_bijective
  graph := gamma_standard_natural_graph hGS C hA hC

theorem finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ) (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (hFinite : FiniteMixedRVFibres (carrier A)) :
    Map.FiniteFibres (rvObjectVolume C.contractionObject) :=
  rv_volume_finite_of_lift_finite C.contractionObject
    (GammaIso.finite_mixed_rv_fibres hκ hs hsmall (C.gammaNaturalLiftIso hGS hA hC) hFinite)

def finiteObject {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk G.real < κ) (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (hFinite : FiniteMixedRVFibres (carrier A)) :
    @SpecialTransformations.Section4.RVFiniteObject M (@CanonicalStructure.normalize M sM) S n :=
  ⟨C.contractionObject,C.finite_volume hκ hs hsmall hGS hA hC hFinite⟩

end StandardContraction
end IntegrationInACVF.Section5
