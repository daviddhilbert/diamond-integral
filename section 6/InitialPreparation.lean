import «section 6».ZeroCenteredInvariance
import «section 2».Bases

/-! Existence of the original-base preliminary preparation. The uniform
invariant radius is chosen first, then raised to the value of a named
nonzero VF center. Actual VF generation, saturation, and smallness remain
explicit; no algebraic point is silently treated as individually definable. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_zeroCentered_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) :
    Nonempty (ZeroCenteredData A) := by
  obtain ⟨δ,hδ,hδ0,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA
  obtain ⟨c,hc0,hcdef,hcδ⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ0 hδ
  refine ⟨⟨hA,c,hc0,hcdef,fun u => (hInv u).larger_radius (fun _ => ?_)⟩⟩
  exact hcδ.le

theorem vfGenerated_base_support
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ a : B.field, a ≠ 0 ∧ Valued.v a.val ≠ 1) :
    (∀ a ∈ vfFieldNames B.field, iVF a) ∧ vfFieldNames B.field ⊆ (S : Set M) ∧
      (S : Set M) ⊆ algebraicClosureSet (vfFieldNames B.field) ∧
      ∃ x : vfAlgebraicClosureField (vfFieldNames B.field), x ≠ 0 ∧ Valued.v x.val ≠ 1 := by
  refine ⟨?_,B.fieldNames_subset,?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact a.property
  · intro a ha
    obtain ⟨σ,hσ⟩ := B.definable_over_fieldNames a ha
    exact ⟨σ,hσ.algebraic⟩
  · obtain ⟨a,ha0,hav⟩ := hnt
    have ha : a.val ∈ vfAlgebraicClosureField (vfFieldNames B.field) :=
      (mem_vfAlgebraicClosureField _ _).mpr
        (show DefinableClosureAt (vfFieldNames B.field) .vf a.val.val from
          definableClosureAt_of_mem (show a.val.val ∈ vfFieldNames B.field from
            ⟨a.val,a.property,rfl⟩) a.val.property).algebraic
    exact ⟨⟨a.val,ha⟩,fun he => ha0 (Subtype.ext
      (congrArg (fun x : vfAlgebraicClosureField (vfFieldNames B.field) => x.val) he)),hav⟩

/-- The preliminary preparation from Remark 6.13, over an actual
VF-generated field base. All choices stay over that original base. -/
theorem exists_initial_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ a : B.field, a ≠ 0 ∧ Valued.v a.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) n r) (S : Set M)) (hA : ProperInvariant (S : Set M) A.carrier) :
    ∃ D : ZeroCenteredData A,
      SpecialCovariantChain (G := G) A D.map.image D.bijection ∧
      ProperCovariantHomeomorphism D.bijection ∧ ProperInvariant (S : Set M) D.map.image.carrier ∧
      VFDoublyBounded D.map.image.carrier ∧
      (∀ u, AlphaInvariant (fun _ => finiteValue D.center D.center_nonzero) (vfFibre D.map.image.carrier u)) ∧
      ∀ p : A, HasMixedUnitDerivativeAt D.bijection p := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support S B hnt
  obtain ⟨D⟩ := exists_zeroCentered_data h00 hc linear hκ hs hv (vfFieldNames B.field) (S : Set M)
    hsmall hΓ hV hVS hSV hnt' A hA
  exact ⟨D,.zeroCentered A D,D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ,
    D.image_properInvariant h00 hc hκ hs hv,D.image_vfDoublyBounded,D.image_fibres_invariant h00,
    D.unit_derivative hv⟩

end DiamondIntegral.Section6
