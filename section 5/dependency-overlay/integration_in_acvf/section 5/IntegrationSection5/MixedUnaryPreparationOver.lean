import IntegrationSection5.MixedUnaryPreparations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}
theorem mixed_unary_preparations_over {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (K : Set M) (A : Set (Point (M := M) 2 m)) (hR : GammaSetDefinable G (A)) :
    ∃ P : MixedUnaryPreparations (G := G) A, K ⊆ P.codes := by
  obtain ⟨d,t,ht,H,hH⟩ := gammaPresentationInput G (A) hR
  let S0 := G.real ∪ Set.range (GammaParameters.rawTuple t)
  obtain ⟨r,D,TD,hSD,hD⟩ := gamma_pullback_preparation_over hs h00 hsmall F (S0 ∪ K)
    (mixedUnaryProjectionSet A 0) (mixedUnaryProjection_gamma A hR 0)
  obtain ⟨s,E,TE,hDE,hE⟩ := gamma_pullback_preparation_over hs h00 hsmall F TD.codes
    (mixedUnaryProjectionSet A 1) (mixedUnaryProjection_gamma A hR 1)
  let hHE : S0 ⊆ TE.codes := fun _ hx => hDE (hSD (Or.inl hx))
  let U := TD.special.extendBase hDE
  refine ⟨{
    codes := TE.codes
    real_contains := TE.real_contains
    source := extendBase H hHE
    source_eq := hH
    sourceD := extendBase TD.source hDE
    sourceE := TE.source
    sourceD_eq := TD.source_eq
    sourceE_eq := TE.source_eq
    arityD := r
    arityE := s
    targetD := extendBase TD.target hDE
    targetE := TE.target
    specialD := U
    specialE := TE.special
    gammaD := GammaChainDefinable.extendBase G TD.special.chain hDE TD.invariant_graphs
    gammaE := TE.invariant_graphs
    pullbackD := TD.target_eq.symm ▸ hD
    pullbackE := TE.target_eq.symm ▸ hE },?_⟩
  exact fun x hx => hDE (hSD (Or.inr hx))
end IntegrationInACVF.Section5
