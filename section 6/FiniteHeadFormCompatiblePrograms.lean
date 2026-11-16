import «section 6».FiniteFormCompatiblePrograms
import «section 6».FiniteHeadMeasuredPrograms

/-! Measured head-fibre preparation with the component form invariant
supplies finitely many original-base programs retaining that invariant
at every stage, as well as all terminal measured conclusions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_head_form_compatible_programs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparation (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a) (headGammaFormMap ω a),
        FormCompatibleSynchronizedChain (G := G) (Fin k)
          ((headFibreTemplate A).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMap ω a)) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S 1 (n+1) r s,
      ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ (T i).2.measuredFormGood
        (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω) := by
  obtain ⟨l,T,hCover⟩ := exists_finite_form_compatible_programs h00 hc linear hκ hs hv hsmall hΓ
    (rawVFSpace (M := M) 1).domain ((rawVFSpace (M := M) 1).definable_domain S)
    (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω) (by
      intro z hz
      obtain ⟨a,rfl⟩ := (raw_unary_vf_parameter_iff z).mp hz
      obtain ⟨F,hF⟩ := hLocal a
      refine ⟨F.arity,F.target,F.map,headGammaFormMap ω a,hF,headFibreTemplate_rvPullback A hARV a,
        (fun i => (F.pieces i).2),headGammaFormTemplate_section ω a,?_⟩
      intro t u he
      have h := F.constant (F.map t).val (F.map t).property (F.map u).val (F.map u).property he
      rw [gammaFormExtension_at F.form (F.map t),gammaFormExtension_at F.form (F.map u)] at h
      exact (F.transport t).symm.trans (h.trans (F.transport u)))
  exact ⟨l,T,fun a => hCover (fun _ => a.val) ⟨(fun _ => a),rfl⟩⟩

end DiamondIntegral.Section6
