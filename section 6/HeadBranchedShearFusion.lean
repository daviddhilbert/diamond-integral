import «section 6».FrozenBranchedShearValues

/-! Complete original-base head fusion of actual local branch witnesses.
Finite formula selection, common output coding and simultaneous
continuity repair are all constructed, with the original source fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem branched_shear_data_of_head_witnesses
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hA : ProperInvariant S A.carrier)
    (hLocal : ∀ a : VF M,Nonempty (BranchedShearData (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val)))) : Nonempty (BranchedShearData (G := G) A) := by
  let U := (rawVFSpace (M := M) 1).domain
  have hLocalU : ∀ z ∈ U,Nonempty (BranchedShearData (G := G) ((headFibreTemplate A).fibre z)) := by
    rintro z ⟨a,rfl⟩
    have he : vfValues a=(fun _ : Fin 1 => (a 0).val) := by funext i; fin_cases i; rfl
    rw [he]
    exact hLocal (a 0)
  obtain ⟨s,T,hF,hGood⟩ := exists_uniform_branched_shear_template hv hs hsmall (headFibreTemplate A)
    U ((rawVFSpace (M := M) 1).definable_domain S) hLocalU
  have hGoodVF (a : VF M) : (fun _ : Fin 1 => a.val) ∈ T.good (headFibreTemplate A) :=
    hGood _ ⟨fun _ => a,rfl⟩
  obtain ⟨D,hI,hO,hProd⟩ := exists_branched_shear_common_freezing h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A hA T hF
  exact ⟨branchedShearDataOfCommonFreezing hv A T hF hGoodVF D hI hO hProd⟩

end DiamondIntegral.Section6
