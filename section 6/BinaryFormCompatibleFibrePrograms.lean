import «section 6».FiniteHeadFormCompatiblePrograms
import «section 6».BinaryMeasuredFibrePrograms
import «section 6».UnaryMeasuredFormCompatibleExistence

/-! In two VF dimensions the measured head-fibre programs are
constructed from the actual unary theorem, including the component form condition and
common chain. The original Gamma image may be infinite. This supplies
finite program selection, not an assertion of general measured fusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_binary_form_compatible_fibre_programs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin 2 → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S 1 1 r s,
      ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ (T i).2.measuredFormGood
        (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω) := by
  apply exists_finite_head_form_compatible_programs h00 hc linear hκ hs hv hsmall hΓ A hARV P hPA ω
  intro a
  let z : Fin 1 → M := fun _ => a.val
  obtain ⟨hV',hVS',hSV',hnt',hsmall',hΓ'⟩ := vf_preparation_support_adjoin_tuple
    hV hVS hSV hnt hκ.le hsmall hΓ z (fun _ => a.property)
  obtain ⟨T,hT⟩ := unary_measured_form_compatible_preparation_of_doublyBounded_tagged
    h00 hc linear hκ hs hv (V ∪ Set.range z) hsmall' hΓ' hV' hVS' hSV' hnt'
    ((headFibreTemplate A).fibre z) (headFibreTemplate_properInvariant A hA a)
    (headFibreTemplate_doublyBounded A hAD a) (headFibreTemplate_rvPullback A hARV a)
    (headFibreTemplate_tagged A hTag a) (fun i => (headFibreTemplate (P i)).fibre z)
    (fun i => headFibreTemplate_subset (hPA i) a)
    (fun i => headFibreTemplate_properInvariant (P i) (hP i) a)
    (headGammaFormMap ω a) (headGammaFormMap_levels_open ω a hLevels)
  exact ⟨T.coordinate,hT⟩

end DiamondIntegral.Section6
