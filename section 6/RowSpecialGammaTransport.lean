import «section 6».RowForms
import «section 6».RowGammaFormBounds
import «section 6».RowTransportedGammaLevels
import «section 6».RowGammaFormUniformFibres

/-! (Row-form version for Remark 6.20, translated from `SpecialGammaTransport`.)
 All Gamma levels of a proper form survive transportRow by an actual
special covariant chain. Its inverse, full Gamma graph, open levels and
one original-base named invariance radius are constructed from the chain.
This is transportRow support for measured preparation, not its existence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}

theorem SpecialCovariantChain.gamma_levels_uniform_invariant_row
    (H : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ 1 ≤ δ ∧
      (∀ v, AlphaInvariant (fun _ => δ) (vfFibre B.carrier v)) ∧
      ∀ γ v, AlphaInvariant (fun _ => δ) (vfFibre {p | p ∈ B.carrier ∧
        rowFormExtension (ω.comp (f.inverse (H.bijective h00))) p = γ} v) := by
  have hHomeo := H.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hB := hHomeo.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHomeo.bijective.surjective
  obtain ⟨h,hRetain⟩ := H.retainsRV
  exact gamma_form_all_levels_uniform_invariant_row h00 hc linear hκ hs hv hsmall hΓ hB
    (rowFormExtension (ω.comp (f.inverse (H.bijective h00)))) (rowFormExtension_graph_definable _)
    (transported_gamma_levels_open_row f (H.bijective h00) h hRetain hHomeo.inverseContinuous
      (fun v => (hB.clopen_fibres hv v).isOpen) ω hLevels)

theorem SpecialCovariantChain.gamma_levels_proper_geometry_row
    (H : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ}) :
    ∀ γ, ProperInvariantGeometry {p | p ∈ B.carrier ∧
      rowFormExtension (ω.comp (f.inverse (H.bijective h00))) p = γ} := by
  have hHomeo := H.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hB := hHomeo.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHomeo.bijective.surjective
  obtain ⟨δ,hδ,hδ1,hInv,hLevelsInv⟩ := H.gamma_levels_uniform_invariant_row h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  intro γ
  exact ⟨hB.vfBounded.mono (fun _ hp => hp.1),hB.rvBounded.mono (fun _ hp => hp.1),
    fun v => ⟨fun _ => δ,hLevelsInv γ v⟩⟩

end DiamondIntegral.Section6
