import «section 5».Completed18CoherentCells
import «section 5».Completed18CellRestrictions
import «section 5».Completed18CellBaseTransfer
import «section 5».Completed18RVParameterFamilies
import «section 5».Completed18RVParameterInsertion

/-! The completed generated-base cell preparation applies after naming
arbitrary RV parameters: promote them first, then restrict whole cells. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section5
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem positioned_cells_with_rv_parameters {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : Base (M := M))
    (hr : Cardinal.mk G.real < κ) (hG : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    {m r : ℕ} (z : Fin r → RV (M := M)) (U : Set (Point (M := M) 2 m))
    (hU : GammaSetDefinable (RVLabelSlices.labelBase G z) U) :
    Nonempty (PositionedCellLabelInjection (RVLabelSlices.labelBase G z) U) := by
  let E := RVLabelSlices.labelBase G z
  obtain ⟨A,hA,hrow⟩ := rv_parameter_family z U hU
  obtain ⟨T,hcoh⟩ := exists_coherent_positioned_cell_label_injection hκ hs h00 G hr hG δ hδ hδ1 A hA
  have hGE : BaseDefinableIn G E :=
    ⟨Set.subset_union_left.trans (subset_closureBase E).1,(subset_closureBase E).2⟩
  let TE := positionedCells_base_transfer hGE T
  let e := rvParameterAttachIso E U hU z (fun i => Or.inr ⟨i,rfl⟩)
  have hsub : rvParameterAttachedSet U z ⊆ A := by
    rintro q ⟨p,rfl⟩
    exact (hrow p.val).mpr p.property
  have hsat : ∀ a b : A,a.val.2=b.val.2 → a.val∈rvParameterAttachedSet U z →
      b.val∈rvParameterAttachedSet U z := by
    intro a b hab ha
    obtain ⟨p,hp⟩ := ha
    have hl : Fin.append z p.val.2 = b.val.2 := (congrArg Prod.snd hp).trans hab
    have htuple : Fin.append z (b.val.2 ∘ Fin.natAdd r) = b.val.2 := by
      have hz : b.val.2 ∘ Fin.castAdd m = z := by
        funext i
        have hh := congrFun hl (Fin.castAdd m i)
        simpa only [Function.comp_apply,Fin.append_left] using hh.symm
      rw [← hz]
      exact Fin.append_castAdd_natAdd
    let q : Point (M := M) 2 m := (b.val.1,b.val.2 ∘ Fin.natAdd r)
    have hq : (q.1,Fin.append z q.2) = b.val := Prod.ext rfl htuple
    have hqU : q ∈ U := (hrow q).mp (hq.symm ▸ b.property)
    exact ⟨⟨q,hqU⟩,hq⟩
  let R := restrictPositionedCells TE hsub (e.target_definable (gammaLogicInput E)) hcoh hsat
  refine ⟨{
    arity := R.arity
    target := R.target
    iso := e.trans (gammaLogicInput E) R.iso
    fixes_vf := ?_
    positionDomain := R.positionDomain
    position := R.position
    position_graph := R.position_graph
    cells := R.cells }⟩
  intro a
  exact R.fixes_vf (e.equiv a)

end DiamondIntegral.Section5
