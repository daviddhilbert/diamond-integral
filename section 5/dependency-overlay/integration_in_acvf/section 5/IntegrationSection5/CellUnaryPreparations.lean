import IntegrationSection5.CellUnaryProjections
import IntegrationSection5.GammaPullbackPreparationOver

/-! Both actual unary cell projections are prepared over one internally
constructed real base, retaining their original-Gamma special chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}

structure CellUnaryPreparations (R : Set (VF (M := M) × VF (M := M))) where
  codes : Set M
  real_contains : G.real ⊆ codes
  source : DefSet (M := M) codes 2 0
  source_eq : carrier source = cellPointSet R
  sourceD : DefSet (M := M) codes 1 0
  sourceE : DefSet (M := M) codes 1 0
  sourceD_eq : carrier sourceD = vfUnarySet (first R)
  sourceE_eq : carrier sourceE = vfUnarySet (second R)
  arityD : ℕ
  arityE : ℕ
  targetD : DefSet (M := M) codes 1 arityD
  targetE : DefSet (M := M) codes 1 arityE
  specialD : SpecialBijection sourceD targetD
  specialE : SpecialBijection sourceE targetE
  gammaD : GammaChainDefinable G specialD.chain
  gammaE : GammaChainDefinable G specialE.chain
  pullbackD : IsRVPullback (carrier targetD)
  pullbackE : IsRVPullback (carrier targetE)

theorem cell_unary_preparations {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (R : Set (VF (M := M) × VF (M := M))) (hR : GammaSetDefinable G (cellPointSet R)) :
    Nonempty (CellUnaryPreparations (G := G) R) := by
  obtain ⟨d,t,ht,H,hH⟩ := gammaPresentationInput G (cellPointSet R) hR
  let S0 := G.real ∪ Set.range (GammaParameters.rawTuple t)
  obtain ⟨r,D,TD,hSD,hD⟩ := gamma_pullback_preparation_over hs h00 hsmall F S0
    (vfUnarySet (first R)) (cell_first_unary_gamma R hR)
  obtain ⟨s,E,TE,hDE,hE⟩ := gamma_pullback_preparation_over hs h00 hsmall F TD.codes
    (vfUnarySet (second R)) (cell_second_unary_gamma R hR)
  let hHE : S0 ⊆ TE.codes := fun _ hx => hDE (hSD hx)
  let U := TD.special.extendBase hDE
  exact ⟨{
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
    pullbackE := TE.target_eq.symm ▸ hE }⟩

end IntegrationInACVF.Section5
