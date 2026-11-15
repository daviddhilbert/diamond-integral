import IntegrationSection5.ActiveUnaryProjection
import IntegrationSection5.CellUnaryPreparations

/-! Prepare both mixed unary projections over one internally constructed real presentation, retaining full original-Gamma special chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}

def mixedUnaryProjectionSet (A : Set (Point (M := M) 2 m)) (i : Fin 2) :
    Set (Point (M := M) 1 m) := activeUnaryProjection i id '' A

theorem mixedUnaryProjection_gamma (A : Set (Point (M := M) 2 m))
    (hA : GammaSetDefinable G A) (i : Fin 2) : GammaSetDefinable G (mixedUnaryProjectionSet A i) := by
  let X := PresentedSet.univ (pointSpace (M := M) 2 m) G.real
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).restrict_graph hA
    ((gammaLogicInput G).real_map_graph (activeUnaryProjectionMap i id X)))
  convert h using 1
  ext q
  constructor
  · rintro ⟨p,hp,hq⟩
    exact ⟨p,hp,⟨p,Set.mem_univ _⟩,rfl,hq⟩
  · rintro ⟨p,hp,a,ha,hq⟩
    exact ⟨p,hp,(congrArg (activeUnaryProjection i id) ha).symm.trans hq⟩

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}
structure MixedUnaryPreparations (A : Set (Point (M := M) 2 m)) where
  codes : Set M
  real_contains : G.real ⊆ codes
  source : DefSet (M := M) codes 2 m
  source_eq : carrier source = A
  sourceD : DefSet (M := M) codes 1 m
  sourceE : DefSet (M := M) codes 1 m
  sourceD_eq : carrier sourceD = mixedUnaryProjectionSet A 0
  sourceE_eq : carrier sourceE = mixedUnaryProjectionSet A 1
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

theorem mixed_unary_preparations {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (A : Set (Point (M := M) 2 m)) (hR : GammaSetDefinable G (A)) :
    Nonempty (MixedUnaryPreparations (G := G) A) := by
  obtain ⟨d,t,ht,H,hH⟩ := gammaPresentationInput G (A) hR
  let S0 := G.real ∪ Set.range (GammaParameters.rawTuple t)
  obtain ⟨r,D,TD,hSD,hD⟩ := gamma_pullback_preparation_over hs h00 hsmall F S0
    (mixedUnaryProjectionSet A 0) (mixedUnaryProjection_gamma A hR 0)
  obtain ⟨s,E,TE,hDE,hE⟩ := gamma_pullback_preparation_over hs h00 hsmall F TD.codes
    (mixedUnaryProjectionSet A 1) (mixedUnaryProjection_gamma A hR 1)
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
