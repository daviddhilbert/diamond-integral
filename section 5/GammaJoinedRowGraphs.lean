import «section 5».OriginalPredicateSyntax
import «section 4».FiniteTupleBlocks
import Section3.GammaRealMap

/-! A full original-Gamma graph specializes directly to the joined raw
RV graph convention. Every coordinate and the original base are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4.FiniteTupleBlocks

theorem forall_join_property {α : Type*} (P : α → Prop) (n : ℕ) :
    ∀ (m : ℕ) (x : Fin m → α) (y : Fin n → α),
      (∀ i, P (x i)) → (∀ j, P (y j)) → ∀ k, P (join n m x y k) := by
  intro m
  induction m with
  | zero => intro x y hx hy; exact hy
  | succ m ih =>
    intro x y hx hy k
    exact Fin.cases (hx 0) (fun j => ih (Fin.tail x) y (fun l => hx l.succ) hy j) k

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "NStr" => (@CanonicalStructure.normalize M sM)

def joinedRelationRow {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}
    (H : GammaRelationFormula B p a b sp) (z : Fin p → M) : Set (Fin (b + a) → M) :=
  {w | Fin.append (Fin.append z (w ∘ headIndex b a)) (w ∘ tailIndex b a) ∈ H.val}

theorem joinedRelationRow_definable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}
    (H : GammaRelationFormula B p a b sp) (z : Fin p → M) :
    DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩ (fun _ => .rv) (joinedRelationRow H z) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range z, B.gamma⟩
  let R := B.real ∪ Set.range z
  let f (w : Fin (b + a) → M) := Fin.append (Fin.append z (w ∘ headIndex b a)) (w ∘ tailIndex b a)
  have hH := H.property.mono (show B.real ⊆ C.real from Set.subset_union_left) (Set.Subset.refl B.gamma)
  have hf : @Set.DefinableMap M LRV NStr (Fin (b + a)) (Fin ((p + a) + b)) R f := by
    letI := NStr
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · simp only [f, Fin.append_left]
        exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self k))
      · simp only [f, Fin.append_left, Fin.append_right, Function.comp_apply]
        exact Set.DefinableFun.proj LRV
    · simp only [f, Fin.append_right, Function.comp_apply]
      exact Set.DefinableFun.proj LRV
  have h := hH.preimage_real_map (fun _ : Fin (b + a) => .rv) f hf
  convert h using 1
  ext w
  constructor
  · intro hw
    have hhead (i : Fin a) : iRV (w (headIndex b a i)) := by
      have hh := H.property.proper (f w) hw (Fin.castAdd b (Fin.natAdd p i))
      simpa only [f, Fin.append_left, Fin.append_right, Function.comp_apply, sortEval, iRV] using hh
    have htail (i : Fin b) : iRV (w (tailIndex b a i)) := by
      have hh := H.property.proper (f w) hw (Fin.natAdd (p + a) i)
      simpa only [f, Fin.append_right, Function.comp_apply, sortEval, iRV] using hh
    have hs := forall_join_property iRV b a (w ∘ headIndex b a) (w ∘ tailIndex b a) hhead htail
    rw [join_reconstruct] at hs
    exact ⟨hw, hs⟩
  · exact And.left

end DiamondIntegral.Section5
