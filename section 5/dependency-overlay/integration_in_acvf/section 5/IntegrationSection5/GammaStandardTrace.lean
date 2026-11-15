import IntegrationSection5.GammaProgramTrace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

structure StandardNaturalTrace (C : StandardContraction A σ) where
  arity : ℕ
  target : DefSet (M := M) S n arity
  trace : UniformRelativeTrace S n A target
  projection : Fin C.arity → Fin arity
  square : ∀ a : A, fullRVProjection projection (trace.toMap a).val = (C.naturalMap a).val

theorem standard_natural_gamma_trace (C : StandardContraction A σ) (hA : GammaSetDefinable G (carrier A))
    (hC : GammaProgramHasUniformTraces (G := G) C.program) :
    ∃ R : StandardNaturalTrace C, GammaUniformTrace (G := G) R.trace := by
  obtain ⟨R,hRG⟩ := program_natural_gamma_trace C.program hC
  have hSub : ∀ p ∈ carrier A, vfRVProjection σ id p ∈ carrier (vfPermutationImage A σ) := by
    intro p hp
    exact ⟨⟨p,hp⟩,rfl⟩
  obtain ⟨b,K,ρ,W,hWG,hW,hOther⟩ := R.trace.gamma_lift_projection hRG A σ σ.injective id hSub hA
  refine ⟨⟨b,K,W,ρ ∘ R.projection,?_⟩,hWG⟩
  intro a
  have he : (⟨vfRVProjection σ id a.val,hSub _ a.property⟩ : vfPermutationImage A σ) =
      vfPermutationBijection A σ a := rfl
  have h := congrArg (fullRVProjection R.projection) (hW a)
  rw [he] at h
  have hEq : vfPermutation σ (fullRVProjection (ρ ∘ R.projection) (W.toMap a).val) =
      (C.program.naturalMap (vfPermutationBijection A σ a)).val :=
    h.trans (R.square (vfPermutationBijection A σ a))
  apply vfPermutation_injective σ
  exact hEq.trans (vfPermutation_inverse σ.symm (C.program.naturalMap (vfPermutationBijection A σ a)).val).symm

theorem standard_contraction_exists_gamma_traced {κ : Cardinal}
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real) (hGS : G.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable G (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, GammaProgramDefinable G C.program ∧
      ∃ R : StandardNaturalTrace C, GammaUniformTrace (G := G) R.trace := by
  obtain ⟨l,U,T,hTG,hTrace⟩ := gamma_ordered_contraction_program_gamma_traced hs h00 G hsmall F hGS n
    (vfPermutationImage A σ) (gamma_vfPermutationImage A hA σ)
  let C : StandardContraction A σ := ⟨l,U,T⟩
  obtain ⟨R,hR⟩ := standard_natural_gamma_trace C hA hTrace
  exact ⟨C,hTG,R,hR⟩

end IntegrationInACVF.Section5
