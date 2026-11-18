import «section 6».RowGammaFormRVTraceBounds
import «section 6».GammaRVTraceValues

/-! (Row-form version for Remark 6.20, replacing `GammaRVTraceValues`.)
Equal RV traces identify rows on equal old labels, when both row forms are
constant on their label fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r qR : ℕ} [NeZero qR]

theorem GammaFormParameterTemplateRow.values_eq_of_rvTrace_eq_row
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a b : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range b)}
    (ω : RowFormOn A qR) (η : RowFormOn B qR)
    (hWa : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hWb : {z | Sum.elim b z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) η.graph)
    (hTrace : (W.rvTrace.fibre a).carrier=(W.rvTrace.fibre b).carrier)
    (hConstA : ∀ t u : A, t.val.2 = u.val.2 → (ω t).val = (ω u).val)
    (hConst : ∀ t u : B, t.val.2 = u.val.2 → (η t).val = (η u).val)
    (x : A) (y : B) (hTags : x.val.2 = y.val.2) : (ω x).val = (η y).val := by
  have hPrefix (w : Fin r → RVInfinity M) (v : Fin qR → RVInfinity M) :
      (fun j => Fin.append w v (Fin.castAdd qR j)) = w := funext (fun j => Fin.append_left _ _ j)
  have hSuffix (w : Fin r → RVInfinity M) (v : Fin qR → RVInfinity M) :
      (fun j => Fin.append w v (Fin.natAdd r j)) = v := funext (fun j => Fin.append_right _ _ j)
  ext v
  constructor
  · intro hv
    have hV : Fin.append x.val.2 v ∈ (W.rvTrace.fibre a).carrier :=
      (W.rvTrace_entries_row a ω hWa _).mpr ⟨x, (hPrefix _ _).symm, (hSuffix x.val.2 v).symm ▸ hv⟩
    obtain ⟨t, hTV, hRow⟩ := (W.rvTrace_entries_row b η hWb _).mp (hTrace ▸ hV)
    rw [hSuffix] at hRow
    rw [hPrefix] at hTV
    rw [← hConst t y (hTV.trans hTags)]
    exact hRow
  · intro hv
    have hV : Fin.append y.val.2 v ∈ (W.rvTrace.fibre b).carrier :=
      (W.rvTrace_entries_row b η hWb _).mpr ⟨y, (hPrefix _ _).symm, (hSuffix y.val.2 v).symm ▸ hv⟩
    obtain ⟨t, hTV, hRow⟩ := (W.rvTrace_entries_row a ω hWa _).mp (hTrace.symm ▸ hV)
    rw [hSuffix] at hRow
    rw [hPrefix] at hTV
    rw [← hConstA t x (hTV.trans hTags.symm)]
    exact hRow

end DiamondIntegral.Section6
