import «section 6».ProtectedMeasuredOrderedPrograms
import «section 6».BinaryMeasuredOrderedPrograms
import «section 6».BinaryOrderedContractions

/-! Actual simultaneous binary ordered preparation, including arbitrary
Gamma forms with open fixed-RV levels, is obtained from single-source
existence by the checked membership graft and first-stage absorption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_protected_ordered_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hC : ∀ i,ProperInvariant S (C i).carrier) :
    Nonempty (ProtectedOrderedProgram (G := G) A C) := by
  let τ := properMembershipLabels A C
  let B := (graftMap hc τ).image
  have hτ := properMembershipLabels_properCovariant h00 hc hκ hs hv A hA C hC
  have hB := graft_properInvariant h00 hc hκ hs hv τ hA hτ
  have hBD : VFDoublyBounded B.carrier := by
    obtain ⟨α,hα⟩ := hAD
    exact ⟨α,by rintro q ⟨p,rfl⟩ i; exact hα p.val p.property i⟩
  obtain ⟨q,U,⟨T⟩⟩ := ordered_standard_program_binary_doublyBounded h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt B hB hBD
  exact ⟨protectedOrderedProgram_of_grafted_program h00 hc linear hκ hs hv hsmall hΓ A hA C hC T⟩

theorem binary_protected_measured_ordered_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (ProtectedMeasuredOrderedProgram (G := G) A C ω) := by
  let τ := properMembershipLabels A C
  let B := (graftMap hc τ).image
  have hτ := properMembershipLabels_properCovariant h00 hc hκ hs hv A hA C hC
  have hB := graft_properInvariant h00 hc hκ hs hv τ hA hτ
  have hBD : VFDoublyBounded B.carrier := by
    obtain ⟨α,hα⟩ := hAD
    exact ⟨α,by rintro q ⟨p,rfl⟩ i; exact hα p.val p.property i⟩
  obtain ⟨T⟩ := binary_measured_ordered_program h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    B hB hBD (membershipGraftForm hc A C ω)
    (membershipGraftForm_levels_open h00 hc linear hκ hs hv hsmall hΓ A hA C hC ω hLevels)
  exact ⟨protectedMeasuredOrderedProgram_of_grafted_program h00 hc linear hκ hs hv hsmall hΓ A hA C hC ω T⟩

end DiamondIntegral.Section6
