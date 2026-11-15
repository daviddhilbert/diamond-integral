import IntegrationSection5.SharedRVUnaryHeadPreparation
import IntegrationSection5.ProductContractionSource

/-! The exact first contracted source of a product family with shared RV parameters. -/
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
variable {S : Set M} {m b r : ℕ}

theorem sharedRV_product_head_contracted_shape
    (E : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 b)
    (K : DefSet (M := M) S 2 r) (σ : Fin b → Fin r) (ρ : Fin m → Fin r)
    (hK : carrier K = {q | activeUnaryProjection 0 σ q ∈ carrier B ∧
      activeUnaryProjection 1 ρ q ∈ carrier E}) :
    carrier (headImage K) = {p | activeUnaryProjection 0 (Fin.natAdd 1 ∘ ρ) p ∈ carrier E ∧
      productHeadRVCondition B σ p.2} := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩
    have ha := (Set.ext_iff.mp hK a.val).mp a.property
    change activeUnaryProjection 0 (Fin.natAdd 1 ∘ ρ) (headKeyMap K a).val ∈ carrier E ∧
      productHeadRVCondition B σ (headKeyMap K a).val.2
    rw [headKeyMap_apply]
    refine ⟨?_,vfAt a.val 0,?_,rfl⟩
    · convert ha.2 using 1
      apply Prod.ext
      · funext j; fin_cases j; rfl
      · funext j
        simp only [activeUnaryProjection,Function.comp_apply,headKey,Fin.append_right]
    · have he : activeUnaryProjection 0 σ
          (![vfAt a.val 0,0],fun j => (headKey a.val).2 (Fin.natAdd 1 j)) =
            activeUnaryProjection 0 σ a.val := by
        refine Prod.ext rfl ?_
        funext j
        simp only [activeUnaryProjection,Function.comp_apply,headKey,Fin.append_right]
      exact he.symm ▸ ha.1
  · rintro ⟨hE,x,hB,hx⟩
    let q : Point (M := M) 2 r := (![x,vfAt p 0],fun j => p.2 (Fin.natAdd 1 j))
    have hq : q ∈ carrier K := (Set.ext_iff.mp hK q).mpr ⟨hB,hE⟩
    refine ⟨⟨q,hq⟩,?_⟩
    change (headKeyMap K ⟨q,hq⟩).val = p
    rw [headKeyMap_apply]
    refine Prod.ext ?_ ?_
    · funext j
      fin_cases j
      rfl
    · funext j
      cases j using Fin.addCases with
      | left j => fin_cases j; exact hx
      | right j => simp only [headKey,Fin.append_right,q]

end IntegrationInACVF.Section5
