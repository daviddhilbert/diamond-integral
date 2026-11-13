import «section 3».FiniteFamilies
import «section 3».RVZeroStrata
import Section4.RVTagging

/-! Finite RV families have a genuine definable realization using finite
zero/one tags. The encoding is bijective and retains all original points. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvFamilyTag {N : ℕ} (i : Fin N) : Fin N → CanonicalRV.RVSort M :=
  fun j => if j = i then ⟨iRVOne, rv_one_mem hM⟩ else ⟨iRVZero, rv_zero_mem hM⟩

theorem rvFamilyTag_injective {N : ℕ} : Function.Injective (rvFamilyTag (M := M) (N := N)) := by
  classical
  intro i j he
  by_contra hij
  have h := congrArg (fun t : Fin N → CanonicalRV.RVSort M => (t i).val) he
  have heq : iRVOne (M := M) = iRVZero := by simpa [rvFamilyTag, hij] using h
  exact RVCalc.rv_one_ne_zero hM heq

def rvFamilyTagMap {N : ℕ} (i : Fin N) (A : DefSet (rawRVSpace (M := M) n) S) :
    Map A (DefSet.univ (rawRVSpace (N + n)) S) := by
  classical
  let F (z : Fin n → M) := Fin.append (fun j : Fin N => if j = i then iRVOne else iRVZero) z
  refine rvMapOfCode A (fun t => rvAppend (rvFamilyTag i) t) F ?_ ?_
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · by_cases hj : j = i
      · simpa only [F, Fin.append_left, hj, ↓reduceIte, Bool.true_eq] using
          rvConstantCode_definable (M := M) S (ι := Fin n) true
      · simpa only [F, Fin.append_left, hj, ↓reduceIte, Bool.false_eq_true] using
          rvConstantCode_definable (M := M) S (ι := Fin n) false
    · simpa only [F, Fin.append_right] using
        (Set.DefinableFun.proj (M := M) LRV (A := S) (i := j))
  · intro c
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [rvValues, rvAppend, rvFamilyTag, F, Fin.append_left]
      split <;> rfl
    · simpa only [rvValues, rvAppend, F, Fin.append_right] using congrFun (rvValues_decode c) j

def FiniteFamily.rvRealization (A : FiniteFamily (rawRVSpace (M := M) n) S) :
    DefSet (rawRVSpace (A.tags + n)) S where
  carrier := {t | ∃ i, t ∈ (rvFamilyTagMap i (A.piece i)).image.carrier}
  definable := by
    have hd := Set.definable_iUnion_of_finite (fun i => (rvFamilyTagMap i (A.piece i)).image.definable)
    change S.Definable LRV _
    convert hd using 1
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨hz, i, hi⟩
      exact ⟨i, hz, hi⟩
    · rintro ⟨i, hz, hi⟩
      exact ⟨hz, i, hi⟩

def FiniteFamily.rvEncode (A : FiniteFamily (rawRVSpace (M := M) n) S) (a : A.Carrier) : A.rvRealization :=
  ⟨(rvFamilyTagMap a.1 (A.piece a.1) a.2).val, a.1, a.2, rfl⟩

theorem FiniteFamily.rvEncode_bijective (A : FiniteFamily (rawRVSpace (M := M) n) S) :
    Function.Bijective (FiniteFamily.rvEncode A) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have ht : rvFamilyTag (M := M) i = rvFamilyTag j := by
      funext q
      simpa only [FiniteFamily.rvEncode, rvFamilyTagMap, rvMapOfCode, Map.ofCodes,
        rvAppend, Fin.append_left] using
        congrArg (fun t : A.rvRealization => t.val (Fin.castAdd n q)) he
    have hij := rvFamilyTag_injective ht
    subst j
    have hab : a = b := by
      apply Subtype.ext
      funext q
      simpa only [FiniteFamily.rvEncode, rvFamilyTagMap, rvMapOfCode, Map.ofCodes,
        rvAppend, Fin.append_right] using
        congrArg (fun t : A.rvRealization => t.val (Fin.natAdd A.tags q)) he
    subst b
    rfl
  · intro b
    obtain ⟨i, a, ha⟩ := b.property
    exact ⟨⟨i, a⟩, Subtype.ext ha⟩

def FiniteFamily.rvEquiv (A : FiniteFamily (rawRVSpace (M := M) n) S) : A.Carrier ≃ A.rvRealization :=
  Equiv.ofBijective (FiniteFamily.rvEncode A) (FiniteFamily.rvEncode_bijective A)

end DiamondIntegral.Section3
