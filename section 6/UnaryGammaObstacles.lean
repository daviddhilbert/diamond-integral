import «section 6».GammaCodeLocus

/-! One actual finite original-base obstacle set controls all Gamma
levels simultaneously. The additional RV coordinate ranges over every
proper code of a Gamma value; no individual level is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r : ℕ} {S : Set M}

theorem exists_unary_gamma_obstacles
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (ω : Mixed M 1 r → Gamma M)
    (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω)) :
    ∃ Q : Finset (VF M), S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))) ∧
      ∀ γ : Gamma M, UnaryObstacleControl (G := G) Q {p | p ∈ A.carrier ∧ ω p = γ} := by
  obtain ⟨Q,hQ,hControl⟩ := exists_unary_obstacles hc hv (gammaCodeLocus A ω hGraph)
  refine ⟨Q,hQ,fun γ a ρ hAvoid x hx y hy u => ?_⟩
  obtain ⟨t,ht,htγ⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
  let τ : RVInfinity M := ⟨t,ht.1⟩
  have hAt (z : VF M) :
      ((fun _ : Fin 1 => z),Fin.cons τ u) ∈ (gammaCodeLocus A ω hGraph).carrier ↔
        ((fun _ : Fin 1 => z),u) ∈ A.carrier ∧ ω ((fun _ : Fin 1 => z),u) = γ := by
    rw [gammaCodeLocus_at]
    constructor
    · rintro ⟨hz,_,hVal⟩
      exact ⟨hz,hVal.symm.trans htγ⟩
    · rintro ⟨hz,hγ⟩
      exact ⟨hz,ht,htγ.trans hγ.symm⟩
  exact (hAt x).symm.trans ((hControl a ρ hAvoid x hx y hy (Fin.cons τ u)).trans (hAt y))

theorem exists_unary_gamma_controlling_roots
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (ω : Mixed M 1 r → Gamma M)
    (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω)) :
    ∃ R : UnaryRootFamily A, ∃ N : ℕ, (∀ u, (R.fibre u).card ≤ N) ∧
      ∀ γ : Gamma M, UnaryRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  obtain ⟨Q,hQ,hControl⟩ := exists_unary_gamma_obstacles hc hv A ω hGraph
  let R := UnaryRootFamily.fromObstacles A Q hQ
  refine ⟨R,Q.card,fun u => ?_,fun γ => UnaryRootFamily.fromObstacles_control Q hQ _ (hControl γ)⟩
  apply Finset.card_le_card
  intro x hx
  have hMem := (R.mem_fibre u x).mp hx
  exact hMem.2

end DiamondIntegral.Section6
