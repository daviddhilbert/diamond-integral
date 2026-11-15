import IntegrationSection5.UnaryProductHeadPreparation
import IntegrationSection5.CellUnaryProjections

/-! An actual unary special preparation of one factor gives the first
stage of the product contraction, with an exact product target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {b : ℕ}

theorem product_head_stage (D E : Set (VF (M := M)))
    {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
    (hA : carrier A = vfUnarySet D)
    (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B))
    (H : DefSet (M := M) S 2 0) (hH : carrier H = cellPointSet (D ×ˢ E))
    (hHG : GammaSetDefinable G (carrier H)) :
    ∃ T : HeadPreparation H, ∃ σ : Fin b → Fin T.arity,
      Function.Bijective σ ∧ GammaSetDefinable G (carrier T.target) ∧
      GammaGraphDefinable G (pointMapGraph T.map) ∧
      carrier T.target = {q | activeUnaryProjection 0 σ q ∈ carrier B ∧ vfAt q 1 ∈ E} ∧
      ∀ p : H, ∃ a : A, vfAt a.val 0 = vfAt p.val 0 ∧
        activeUnaryProjection 0 σ (T.map p).val = (u.toMap a).val := by
  let Q : Point (M := M) 2 0 → Prop := fun p => vfAt p 1 ∈ E
  have hQ : ∀ p x, Q (replace 0 p x) ↔ Q p := by
    intro p x
    change vfAt (replace 0 p x) 1 ∈ E ↔ vfAt p 1 ∈ E
    simp [replace,vfAt]
  have hSource : carrier H = {p | activeUnaryProjection 0 Fin.elim0 p ∈ carrier A ∧ Q p} := by
    rw [hH,hA]
    rfl
  obtain ⟨T,σ,hle,hTG,hfG,hσ,hcover,hImage,hcomm⟩ :=
    unary_product_head_preparation u hu hB H hHG Q hQ hSource
  refine ⟨T,σ,hσ rfl,hTG,hfG,hImage,?_⟩
  intro p
  exact ⟨⟨activeUnaryProjection 0 Fin.elim0 p.val,
    ((Set.ext_iff.mp hSource p.val).mp p.property).1⟩,rfl,hcomm p⟩

end IntegrationInACVF.Section5
