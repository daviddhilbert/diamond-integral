import «section 4».RVResidueCodeRelations
import «section 4».RVForgetScissors

/-! The residue-field class of an actual RES domain is independent of
its code and invariant under actual original-base underlying RV isomorphisms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueIsomorphisms
open RVResidueChartCodes RVResidueCodeRelations RVMeasuredCharts
open FiniteTupleBlocks DefinableBiUniqueRelation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem joined_graph_biunique {n m : ℕ} (A : Set (Fin n → M)) (B : Set (Fin m → M))
    (e : A ≃ B) : BiUnique A B
      {z | join m n (z ∘ Sum.inl) (z ∘ Sum.inr) ∈
        {w | ∃ u : A, w = join m n u.val (e u).val}} := by
  constructor
  · intro x hx
    let u : A := ⟨x, hx⟩
    refine ⟨(e u).val, ⟨(e u).property, u, rfl⟩, ?_⟩
    rintro y ⟨_, v, hv⟩
    have hh : x = v.val := by
      have he := congrArg (fun w : Fin (m + n) → M => w ∘ headIndex m n) hv
      simpa only [Function.comp_def, join_head, Sum.elim_inl] using he
    have ht : y = (e v).val := by
      have he := congrArg (fun w : Fin (m + n) → M => w ∘ tailIndex m n) hv
      simpa only [Function.comp_def, join_tail, Sum.elim_inr] using he
    have hvu : v = u := Subtype.ext hh.symm
    exact ht.trans (congrArg (fun v : A => (e v).val) hvu)
  · intro y hy
    let u := e.symm ⟨y, hy⟩
    have heu : (e u).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    refine ⟨u.val, ⟨u.property, u, ?_⟩, ?_⟩
    · change join m n u.val y = join m n u.val (e u).val
      rw [heu]
    · rintro x ⟨_, v, hv⟩
      have hh : x = v.val := by
        have he := congrArg (fun w : Fin (m + n) → M => w ∘ headIndex m n) hv
        simpa only [Function.comp_def, join_head, Sum.elim_inl] using he
      have ht : y = (e v).val := by
        have he := congrArg (fun w : Fin (m + n) → M => w ∘ tailIndex m n) hv
        simpa only [Function.comp_def, join_tail, Sum.elim_inr] using he
      have hvu : v = u := e.injective (Subtype.ext (ht.symm.trans heu.symm))
      exact hh.trans (congrArg Subtype.val hvu)

def value (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : FieldDefinableRing.Ring (ModelResidue M) :=
  FieldDefinableRing.objectClass (ModelResidue M) (code hc a).chart

theorem value_iso (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    {B : Base (M := M)} {k : ℕ} (a b : RESChart B k)
    (F : RVForgetScissors.UnderlyingIso a.toChart b.toChart) : value hc a = value hc b :=
  objectClass_eq hc (code hc a) (code hc b)
    {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F.equiv u).val}
    F.graph_definable (joined_graph_biunique a.domain b.domain F.equiv)

theorem value_measured_iso (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {k : ℕ} (a b : RESChart B k)
    (F : Iso a.toChart b.toChart) : value hc a = value hc b :=
  value_iso hc a b (RVForgetScissors.ofMeasured F)

end DiamondIntegral.Section4.RVResidueIsomorphisms
