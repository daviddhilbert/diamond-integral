import IntegrationSection5.FiniteRVComparison
import Section3.GammaClosureLaws

/-! Prepared cells and their complete positioning graphs descend along
definable parameter inclusions, including all RV-label coefficient bases. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section5
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def BaseDefinableIn (G H : Base (M := M)) : Prop :=
  G.real ⊆ (closureBase H).real ∧ G.gamma ⊆ (closureBase H).gamma

theorem BaseDefinableIn.transfer {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {n : ℕ} {sn : Fin n → SortTag} {D : Set (Fin n → M)} (hD : DefinableOverBase G sn D) :
    DefinableOverBase H sn D :=
  hD.eliminate_definable_params h.1 h.2

theorem BaseDefinableIn.labelBase {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {d : ℕ} (s : Fin d → RV (M := M)) :
    BaseDefinableIn (RVLabelSlices.labelBase G s) (RVLabelSlices.labelBase H s) := by
  have hm := closureBase_mono (B := H) (C := RVLabelSlices.labelBase H s)
    Set.subset_union_left (Set.Subset.refl _)
  refine ⟨?_,h.2.trans hm.2⟩
  rintro x (hx | hx)
  · exact hm.1 (h.1 hx)
  · exact (subset_closureBase (RVLabelSlices.labelBase H s)).1 (Or.inr hx)

theorem cellData_base_transfer {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {D : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (hD : Cells.DefinableCellData G D f t) : Cells.DefinableCellData H D f t :=
  ⟨hD.1,h.transfer hD.2.1,h.transfer hD.2.2.1,h.transfer hD.2.2.2.1,
    fun u hu => h.transfer (hD.2.2.2.2 u hu)⟩

def positionedCells_base_transfer {G H : Base (M := M)} (h : BaseDefinableIn G H)
    {m : ℕ} {A : Set (Point (M := M) 2 m)} (T : PositionedCellLabelInjection G A) :
    PositionedCellLabelInjection H A where
  arity := T.arity
  target := T.target
  iso := ⟨T.iso.equiv,h.transfer T.iso.graph⟩
  fixes_vf := T.fixes_vf
  positionDomain := T.positionDomain
  position := T.position
  position_graph := h.transfer T.position_graph
  cells := by
    intro s hs
    obtain ⟨f,t,hD,hpos⟩ := T.cells s hs
    exact ⟨f,t,cellData_base_transfer (h.labelBase s) hD,hpos⟩

end DiamondIntegral.Section5
