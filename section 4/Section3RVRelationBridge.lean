import «section 4».Section3RVCodeBridge
import «section 4».Section3GammaRelationBridge
import «section 3».RVZeroStrata

/-! Full binary RV relations in the native and raw chart encodings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVRelationBridge
open Section3RVCodeBridge FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def splitMap (S : Set M) (n m : ℕ) : Map (DefSet.univ (rawRVSpace (M := M) (m + n)) S)
    (DefSet.univ ((rawRVSpace n).prod (rawRVSpace m)) S) :=
  ((rvSelectCoordinates (headIndex m n) (DefSet.univ (rawRVSpace (m + n)) S)).pair
    (rvSelectCoordinates (tailIndex m n) (DefSet.univ (rawRVSpace (m + n)) S))).corestrict (fun _ => Set.mem_univ _)

def mergeMap (S : Set M) (n m : ℕ) : Map (DefSet.univ ((rawRVSpace (M := M) n).prod (rawRVSpace m)) S)
    (DefSet.univ (rawRVSpace (m + n)) S) :=
  (rvSelectCoordinates (Section3GammaRelationBridge.mergeIndices n m)
    (DefSet.univ (rawRVSpace (n + m)) S)).comp (rvAppendMap S n m)

theorem mergeMap_value (S : Set M) (n m : ℕ)
    (a : DefSet.univ ((rawRVSpace (M := M) n).prod (rawRVSpace m)) S) :
    (mergeMap S n m a).val = join m n a.val.1 a.val.2 :=
  Section3GammaRelationBridge.append_mergeIndices n m a.val.1 a.val.2

def realization {n m : ℕ} (R : (Fin n → CanonicalRV.RVSort M) → (Fin m → CanonicalRV.RVSort M) → Prop) :
    Set (Fin (m + n) → M) := {w | ∃ x y, R x y ∧ rvValues (join m n x y) = w}

theorem relation_iff {n m : ℕ} (R : (Fin n → CanonicalRV.RVSort M) → (Fin m → CanonicalRV.RVSort M) → Prop) :
    GammaGroundRelationDefinable hc B (rawRVSpace n) (rawRVSpace m) R ↔
      DefinableOverBase B (fun _ : Fin (m + n) => .rv) (realization R) := by
  constructor
  · intro h
    let D : GammaGroundDefSet hc B (rawRVSpace (M := M) (m + n)) :=
      ⟨{v | R (v ∘ headIndex m n) (v ∘ tailIndex m n)}, h.preimage (splitMap B.real n m)⟩
    have he : rawDomain D = realization R := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v ∘ headIndex m n, v ∘ tailIndex m n, hv, congrArg rvValues (join_reconstruct m n v)⟩
      · rintro ⟨x, y, hxy, rfl⟩
        refine ⟨join m n x y, ?_, rfl⟩
        change R (join m n x y ∘ headIndex m n) (join m n x y ∘ tailIndex m n)
        simpa only [Function.comp_def, join_head, join_tail] using hxy
    exact (congrArg (fun A : Set (Fin (m + n) → M) => DefinableOverBase B (fun _ => .rv) A) he).mp
      (rawDomain_definable D)
  · intro h
    have hh := (ofRaw (hc := hc) (realization R) h).definable.preimage (mergeMap B.real n m)
    apply hh.congr
    intro z
    change rvValues ((mergeMap B.real n m ⟨z, Set.mem_univ _⟩).val) ∈ realization R ↔ R z.1 z.2
    rw [mergeMap_value]
    constructor
    · rintro ⟨x, y, hxy, he⟩
      have hj := rvValues_injective he
      have hx := congrArg (fun v => v ∘ headIndex m n) hj
      have hy := congrArg (fun v => v ∘ tailIndex m n) hj
      simp only [Function.comp_def, join_head, join_tail] at hx hy
      exact (congrArg₂ R hx hy).mp hxy
    · intro hz
      exact ⟨z.1, z.2, hz, rfl⟩

end DiamondIntegral.Section4.Section3RVRelationBridge
