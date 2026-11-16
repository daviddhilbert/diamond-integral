import «section 6».CentripetalHomeomorphism

/-! The zero-length special covariant bijection, including actual local
VF charts on every proper invariant source and the empty determinant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem identity_source_iff (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u v : Fin r → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (Map.id A) u v ↔ (a,u) ∈ A.carrier ∧ u = v := by
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    exact ⟨hp ▸ p.property,(congrArg Prod.snd hp).symm.trans (congrArg Prod.snd hfp)⟩
  · rintro ⟨ha,rfl⟩
    exact ⟨a,⟨(a,u),ha⟩,rfl,rfl⟩

theorem identity_range_eq_source (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u v : Fin r → RVInfinity M) :
    graphFibreRange (Map.id A) u v = graphFibreSource (Map.id A) u v := by
  ext a
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    have he : b = a := (congrArg Prod.fst hp).symm.trans (congrArg Prod.fst hfp)
    subst b
    exact ⟨a,p,hp,hfp⟩
  · rintro ⟨b,p,hp,hfp⟩
    have he : b = a := (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)
    subst b
    exact ⟨a,p,hp,hfp⟩

theorem identity_vfChart (hA : ProperInvariant S A.carrier) (p : A) : IsVFChartAt (Map.id A) p id := by
  obtain ⟨α,_,hα⟩ := hA.radii p.val.2
  obtain ⟨δ,hδ⟩ := (Set.finite_range α).bddAbove
  refine ⟨δ,fun x hx => ?_⟩
  have hclose : Congruent α p.val.1 x := fun i => by
    change (α i).val < Values.vfValueHom (p.val.1 i - x i)
    rw [vfValue_sub_comm]
    exact (show (α i).val ≤ δ.val from hδ (Set.mem_range_self i)).trans_lt (hx i)
  exact ⟨(hα _ _ hclose).mp p.property,rfl⟩

theorem identity_unit_derivative (hA : ProperInvariant S A.carrier) (p : A) :
    HasMixedUnitDerivativeAt (Map.id A) p := by
  obtain ⟨L,hL,hdet⟩ := hasUnitJacobianAt_id p.val.1
  exact ⟨L,⟨id,identity_vfChart hA p,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hdet⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem identity_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier) : ProperCovariantHomeomorphism (Map.id A) := by
  have hD (u v : Fin r → RVInfinity M) : IsClopen (graphFibreSource (Map.id A) u v) := by
    classical
    by_cases he : u = v
    · have heq : graphFibreSource (Map.id A) u v = vfFibre A.carrier u := by
        ext a
        exact (identity_source_iff A u v a).trans (and_iff_left he)
      rw [heq]
      exact hA.clopen_fibres hv u
    · have heq : graphFibreSource (Map.id A) u v = ∅ := by
        ext a
        exact ⟨fun ha => False.elim (he ((identity_source_iff A u v a).mp ha).2),False.elim⟩
      rw [heq]
      exact isClopen_empty
  have hcont : ContinuousOnGraphFibres (Map.id A) := by
    intro u v
    apply continuous_id.continuousOn.congr
    intro a ha
    obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph (Map.id A) u v ha
    exact (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)
  have hcov := properCovariant_of_clopen_ranges h00 hc hκ hs hv (Map.id A) hA hA hcont
    (fun u v => (hD u v).isOpen) (fun u v => identity_range_eq_source A u v ▸ hD u v)
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (Map.id A) hcov Function.bijective_id hcont

end DiamondIntegral.Section6
