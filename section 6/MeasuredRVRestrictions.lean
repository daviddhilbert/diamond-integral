import «section 6».FiniteUnaryMeasuredRVLifts
import Section9.GlueLabelLifts
import Section9.RestrictActualLift

/-! Restriction and gluing retain the full total derivative on a fixed
old-label fibre. Measured restrictions use the literal restricted form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def MeasuredRVObject.restrict (U : MeasuredRVObject (M := M) S n)
    (A : DefSet (rawRVSpace (M := M) U.object.arity) S) (hA : A.carrier ⊆ U.object.domain.carrier) :
    MeasuredRVObject (M := M) S n where
  object := U.object.restrict A hA
  finiteVolume := U.finiteVolume.restrict hA
  nonzero u := U.nonzero ⟨u.val,hA u.property⟩
  form := U.form.restrict hA

def MeasuredRVIso.restrict {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (A : DefSet (rawRVSpace (M := M) U.object.arity) S) (hA : A.carrier ⊆ U.object.domain.carrier) :
    MeasuredRVIso (U.restrict A hA)
      (V.restrict (e.iso.hom.map.restrict hA).image (rvLabelImage_subset e.iso A hA)) where
  iso := rvIsoRestrict e.iso A hA
  balance u := e.balance ⟨u.val,hA u.property⟩

theorem mixedDerivative_of_label_restriction
    {U V : RVObject (M := M) S n}
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    {B : DefSet (rawMixedSpace (M := M) n V.arity) S}
    (f : Map (rvLift (U.restrict A hA)) B) (g : Map (rvLift U) (rvLift V))
    (p : rvLift (U.restrict A hA)) (q : rvLift U) (hpq : p.val = q.val)
    (hagree : ∀ (p' : rvLift (U.restrict A hA)) (q' : rvLift U), p'.val = q'.val →
      (f p').val = (g q').val)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hL : HasMixedVFDerivativeAt f p L) : HasMixedVFDerivativeAt g q L := by
  obtain ⟨F,⟨ρ,hρ⟩,hD⟩ := hL
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  refine ⟨F,⟨ρ,fun x hx => ?_⟩,h₁ ▸ hD⟩
  obtain ⟨hxA,hxF⟩ := hρ x (h₁.symm ▸ hx)
  let a : rvLift (U.restrict A hA) := ⟨(x,p.val.2),hxA⟩
  have hxU : (x,q.val.2) ∈ (rvLift U).carrier :=
    h₂ ▸ ((rvLift_restrict_mem_iff U A hA _).mp hxA).1
  let b : rvLift U := ⟨(x,q.val.2),hxU⟩
  have hab := hagree a b (Prod.ext rfl h₂)
  have he := hagree p q hpq
  refine ⟨hxU,?_⟩
  change (g b).val = _
  rw [← hab,hxF,congrArg Prod.snd he]

end DiamondIntegral.Section6
