import «section 6».RowHeadGammaFormMaps
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».HeadGammaFormTemplates

/-! (Row-form version for Remark 6.20, replacing `HeadGammaFormTemplates`.)
One original-base row template specializes to the actual row form on every
head fibre. The template is the membership graph of the row form, read with
the head coordinate as parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r qR : ℕ} [NeZero qR]

/-- Raw membership in the mixed/RV relation, by actual points. -/
theorem mixed_rv_relation_iff {n r q : ℕ}
    (R : (rawMixedSpace (M := M) n r).Carrier → (rawRVSpace (M := M) q).Carrier → Prop)
    (z : (Fin n ⊕ Fin r) ⊕ Fin q → M) :
    z ∈ (rawMixedSpace (M := M) n r).relation (rawRVSpace (M := M) q) R ↔
      ∃ x v, Sum.elim (mixedValues x) (rvValues v) = z ∧ R x v := by
  constructor
  · rintro ⟨hx, hy, h⟩
    refine ⟨_, _, ?_, h⟩
    funext i
    cases i with
    | inl i => exact congrFun (mixedValues_decode ⟨_, hx⟩) i
    | inr i => exact congrFun (rvValues_decode (M := M) ⟨_, hy⟩) i
  · rintro ⟨x, v, rfl, h⟩
    refine ⟨mixedValues_mem_domain x, ⟨v, rfl⟩, ?_⟩
    have e1 : (rawMixedSpace (M := M) n r).decode ⟨Sum.elim (mixedValues x) (rvValues v) ∘ Sum.inl,
        mixedValues_mem_domain x⟩ = x := decode_mixedValues x
    have e2 : (rawRVSpace (M := M) q).decode ⟨Sum.elim (mixedValues x) (rvValues v) ∘ Sum.inr, ⟨v, rfl⟩⟩ = v :=
      decode_rvValues v
    rw [e1, e2]
    exact h

def headGammaFormCodeIndexRow : ((Fin (n+1) ⊕ Fin r) ⊕ Fin qR) → Fin 1 ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) :=
  Sum.elim (fun i => Sum.elim Sum.inl (Sum.inr ∘ Sum.inl) (headFibreCodeIndex i)) (Sum.inr ∘ Sum.inr)

def headGammaFormTemplateRow {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : RowFormOn A qR) : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n r :=
  ⟨{z | z ∘ headGammaFormCodeIndexRow ∈ (rawMixedSpace (M := M) (n+1) r).relation (rawRVSpace (M := M) qR) ω.graph},
    Set.Definable.preimage_comp headGammaFormCodeIndexRow ω.graph_definable⟩

theorem headGammaFormExtension_at_row {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : RowFormOn A qR) (a : VF M)
    (x : (headFibreTemplate A).fibre (fun _ => a.val)) :
    rowFormExtension (headGammaFormMapRow ω a) x.val = rowFormExtension ω (Fin.cons a x.val.1,x.val.2) := by
  rw [rowFormExtension_at,headGammaFormMap_value_row,
    rowFormExtension_at ω ⟨_,(mem_headFibreTemplate_iff A a x.val).mp x.property⟩]

theorem headGammaFormTemplate_section_row {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (ω : RowFormOn A qR) (a : VF M) :
    {z | Sum.elim (fun _ : Fin 1 => a.val) z ∈ (headGammaFormTemplateRow ω).graph} =
      (rawMixedSpace n r).relation (rawRVSpace (M := M) qR) (headGammaFormMapRow ω a).graph := by
  ext z
  change Sum.elim (fun _ : Fin 1 => a.val) z ∘ headGammaFormCodeIndexRow ∈
    (rawMixedSpace (M := M) (n+1) r).relation (rawRVSpace (M := M) qR) ω.graph ↔ _
  rw [mixed_rv_relation_iff, mixed_rv_relation_iff]
  constructor
  · rintro ⟨X, v, hXv, p, hpX, hv⟩
    have hHead : X.1 0 = a := by
      apply Subtype.ext
      exact congrFun hXv (.inl (.inl 0))
    let x : Mixed M n r := (Fin.tail X.1, X.2)
    have hxFull : (Fin.cons a x.1, x.2) = X := by
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        exact hHead.symm
      · rfl
    have hx : x ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier := by
      apply (mem_headFibreTemplate_iff A a x).mpr
      rw [hxFull, ← hpX]
      exact p.property
    refine ⟨x, v, ?_, ⟨x, hx⟩, rfl, ?_⟩
    · funext i
      rcases i with (i | i) | i
      · exact congrFun hXv (.inl (.inl i.succ))
      · exact congrFun hXv (.inl (.inr i))
      · exact congrFun hXv (.inr i)
    · rcases hv with hv | hv
      · left
        rw [← rowFormExtension_at, headGammaFormExtension_at_row, hxFull, ← hpX, rowFormExtension_at]
        exact hv
      · exact Or.inr hv
  · rintro ⟨x, v, hxv, p, hpx, hv⟩
    have hpA : (Fin.cons a p.val.1, p.val.2) ∈ A.carrier :=
      (mem_headFibreTemplate_iff A a p.val).mp p.property
    refine ⟨(Fin.cons a x.1, x.2), v, ?_, ⟨(Fin.cons a x.1, x.2), hpx ▸ hpA⟩, rfl, ?_⟩
    · funext i
      rcases i with (i | i) | i
      · refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun hxv (.inl (.inl j))
      · exact congrFun hxv (.inl (.inr i))
      · exact congrFun hxv (.inr i)
    · rw [headGammaFormMap_value_row] at hv
      have he : (⟨(Fin.cons a x.1, x.2), hpx ▸ hpA⟩ : A) = ⟨(Fin.cons a p.val.1, p.val.2), hpA⟩ :=
        Subtype.ext (by subst hpx; rfl)
      rw [he]
      exact hv

end DiamondIntegral.Section6
