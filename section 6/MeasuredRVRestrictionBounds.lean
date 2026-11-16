import «section 6».MeasuredRVRestrictions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem MeasuredRVObject.restrict_doublyBounded (U : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hU : U.doublyBounded) : (U.restrict D hD).doublyBounded := by
  constructor
  · obtain ⟨γ,hγ⟩ := hU.1
    exact ⟨γ,fun u hu k => hγ u (hD hu) k⟩
  · obtain ⟨γ,hγ⟩ := hU.2
    refine ⟨γ,?_⟩
    rintro t ⟨u,rfl⟩ k
    exact hγ (U.object.value ⟨u.val,hD u.property⟩) ⟨⟨u.val,hD u.property⟩,rfl⟩ k

theorem rvIso_map_bijective {U V : RVObject (M := M) S n} (e : U ≅ V) : Function.Bijective e.hom.map := by
  constructor
  · intro u v he
    have h := congrArg e.inv.map he
    rwa [SpecialTransformations.Section7.rvIso_inv_apply,SpecialTransformations.Section7.rvIso_inv_apply] at h
  · intro v
    exact ⟨e.inv.map v,SpecialTransformations.Section7.rvIso_apply_inv e v⟩

end DiamondIntegral.Section6
