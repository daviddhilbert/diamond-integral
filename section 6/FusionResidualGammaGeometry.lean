import «section 6».MeasuredFusionResidualForms

/-! Actual inverse transport on a residual branch has exact values at
every global preimage and open levels inherited from the whole step. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalFusionRepair
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 (n+1) s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 (n+1) s}
variable {A : MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 (n+1) s}
variable {C : DefSet (rawMixedSpace (M := M) (n+2) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

theorem fusionResidualGammaMap_at_preimage (h00 : M ⊨ Axioms.ACVF00)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (z : R.residualTarget hCoeffMem) (p : C) (hp : (R.stageMap p).val=z.val) :
    (R.fusionResidualGammaMap h00 hCoeffMem ω z).val=(ω p).val := by
  change (R.fusionGammaMap h00 ω ⟨z.val,z.property.1⟩).val=(ω p).val
  have he : (⟨z.val,z.property.1⟩ : R.stageTarget)=R.stageMap p := Subtype.ext hp.symm
  rw [he]
  exact R.fusionGammaMap_transport h00 ω p

theorem fusionResidualGammaMap_levels_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ C.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ (R.residualTarget hCoeffMem).carrier ∧
      gammaFormExtension (R.fusionResidualGammaMap h00 hCoeffMem ω) (x,u)=γ} := by
  have hGeometry := (R.stage_chain h00 hc hκ hs hv).toChain.toSpecial.gamma_levels_proper_geometry
    h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  intro u γ
  have hRes := gammaFormRestriction_level_geometry (A := R.stageTarget) (C := R.residualTarget hCoeffMem)
    (fun _ hp => hp.1) (R.residualContext h00 hc hκ hs hv hCoeffMem).proper.geometry
    (R.fusionGammaMap h00 ω) γ (hGeometry γ)
  exact (hRes.clopen_fibres hv u).isOpen

end DiamondIntegral.Section6.CentripetalFusionRepair
