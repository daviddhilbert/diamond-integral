import «section 6».RowForms
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowGammaCodeLocus

/-! (Row-form version for Remark 6.20, translated from `UnaryGammaObstacles`.)
 One actual finite original-base obstacle set controls all Gamma
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
variable {qR : ℕ}

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r : ℕ} {S : Set M}

theorem exists_unary_gamma_obstacles_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier)
    (hGraph : MixedRowGraphDefinable S A.carrier ω) :
    ∃ Q : Finset (VF M), S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))) ∧
      ∀ γ : Set (rawRVSpace (M := M) qR).Carrier, UnaryObstacleControl (G := G) Q {p | p ∈ A.carrier ∧ ω p = γ} := by
  obtain ⟨Q₁,hQ₁,hControl₁⟩ := exists_unary_obstacles hc hv (gammaCodeLocusRow A ω hGraph)
  obtain ⟨Q₂,hQ₂,hControl₂⟩ := exists_unary_obstacles hc hv A
  have hQ : S.Definable₁ LRV (Subtype.val '' ((Q₁ ∪ Q₂ : Finset (VF M)) : Set (VF M))) := by
    rw [Finset.coe_union,Set.image_union]
    exact hQ₁.union hQ₂
  refine ⟨Q₁ ∪ Q₂,hQ,fun γ a ρ hAvoid x hx y hy u => ?_⟩
  have hAt (z : VF M) (v : Fin qR → RVInfinity M) :
      ((fun _ : Fin 1 => z),Fin.append u v) ∈ (gammaCodeLocusRow A ω hGraph).carrier ↔
        ((fun _ : Fin 1 => z),u) ∈ A.carrier ∧ v ∈ ω ((fun _ : Fin 1 => z),u) := by
    rw [gammaCodeLocus_at_row]
  have hA := hControl₂ a ρ (fun z hz => hAvoid z (Finset.mem_union_right Q₁ hz)) x hx y hy u
  have hL (v : Fin qR → RVInfinity M) :=
    hControl₁ a ρ (fun z hz => hAvoid z (Finset.mem_union_left Q₂ hz)) x hx y hy (Fin.append u v)
  have hEq (hxA : ((fun _ : Fin 1 => x),u) ∈ A.carrier) :
      ω ((fun _ : Fin 1 => x),u) = ω ((fun _ : Fin 1 => y),u) := by
    have hyA := hA.mp hxA
    ext v
    constructor
    · intro hv
      exact ((hAt y v).mp ((hL v).mp ((hAt x v).mpr ⟨hxA,hv⟩))).2
    · intro hv
      exact ((hAt x v).mp ((hL v).mpr ((hAt y v).mpr ⟨hyA,hv⟩))).2
  constructor
  · rintro ⟨hxA,hγ⟩
    exact ⟨hA.mp hxA,(hEq hxA).symm.trans hγ⟩
  · rintro ⟨hyA,hγ⟩
    have hxA := hA.mpr hyA
    exact ⟨hxA,(hEq hxA).trans hγ⟩

theorem exists_unary_gamma_controlling_roots_row
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (ω : Mixed M 1 r → Set (rawRVSpace (M := M) qR).Carrier)
    (hGraph : MixedRowGraphDefinable S A.carrier ω) :
    ∃ R : UnaryRootFamily A, ∃ N : ℕ, (∀ u, (R.fibre u).card ≤ N) ∧
      ∀ γ : Set (rawRVSpace (M := M) qR).Carrier, UnaryRootControl (G := G) R {p | p ∈ A.carrier ∧ ω p = γ} := by
  obtain ⟨Q,hQ,hControl⟩ := exists_unary_gamma_obstacles_row hc hv A ω hGraph
  let R := UnaryRootFamily.fromObstacles A Q hQ
  refine ⟨R,Q.card,fun u => ?_,fun γ => UnaryRootFamily.fromObstacles_control Q hQ _ (hControl γ)⟩
  apply Finset.card_le_card
  intro x hx
  have hMem := (R.mem_fibre u x).mp hx
  exact hMem.2

end DiamondIntegral.Section6
