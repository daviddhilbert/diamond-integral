import «section 5».OriginalSortedPredicates
import «section 5».RESSetSchemata
import «section 4».RVNamedTuples

/-! Literal zero/one tagged coproduct domains are original-base families.
The source coordinates, tag and zero padding remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Milestone0.Transfer
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

def rawRVLeftTag (b : ℕ) (x : Fin a → M) : Fin (1+(a+b)) → M :=
  Fin.append (fun _ : Fin 1 => iRVZero) (Fin.append x (fun _ : Fin b => iRVZero))
def rawRVRightTag (a : ℕ) (y : Fin b → M) : Fin (1+(a+b)) → M :=
  Fin.append (fun _ : Fin 1 => iRVOne) (Fin.append (fun _ : Fin a => iRVZero) y)

def rvTagLeftIndex (a b : ℕ) (i : Fin a) : Fin (1+(a+b)) := Fin.natAdd 1 (Fin.castAdd b i)
def rvTagRightIndex (a b : ℕ) (i : Fin b) : Fin (1+(a+b)) := Fin.natAdd 1 (Fin.natAdd a i)

theorem rawRVLeftTag_eq (w : Fin (1+(a+b)) → M) :
    w = rawRVLeftTag b (w ∘ rvTagLeftIndex a b) ↔
      w (Fin.castAdd (a+b) 0) = iRVZero ∧ ∀ j, w (rvTagRightIndex a b j) = iRVZero := by
  constructor
  · intro h
    rw [h]
    simp only [rawRVLeftTag, rvTagRightIndex, Fin.append_left, Fin.append_right, and_self,
      implies_true]
  · rintro ⟨ht, hz⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ht
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [rawRVLeftTag, rvTagLeftIndex, Function.comp_apply, Fin.append_left, Fin.append_right]
      · simpa only [rawRVLeftTag, rvTagRightIndex, Fin.append_right] using hz j

theorem rawRVRightTag_eq (w : Fin (1+(a+b)) → M) :
    w = rawRVRightTag a (w ∘ rvTagRightIndex a b) ↔
      w (Fin.castAdd (a+b) 0) = iRVOne ∧ ∀ j, w (rvTagLeftIndex a b j) = iRVZero := by
  constructor
  · intro h
    rw [h]
    simp only [rawRVRightTag, rvTagLeftIndex, Fin.append_left, Fin.append_right, and_self,
      implies_true]
  · rintro ⟨ht, hz⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ht
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [rawRVRightTag, rvTagLeftIndex, Fin.append_left, Fin.append_right] using hz j
      · simp only [rawRVRightTag, rvTagRightIndex, Function.comp_apply, Fin.append_right]

theorem OriginalSortedPredicate.equal_named_coordinate {n : ℕ} {s : Fin n → SortTag}
    (i : Fin n) (c : M) (hc : DefinableClosureAtBase B .rv c) :
    OriginalSortedPredicate B s (fun w => w i = c) := by
  have h := hc.preimage_real s (fun _ : Fin 1 => i)
  unfold OriginalSortedPredicate
  convert h using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Function.comp_apply]
  tauto

def taggedParameterLeftIndex (p a b : ℕ) : Fin (p+a) → Fin (p+(1+(a+b))) :=
  Fin.append (Fin.castAdd (1+(a+b))) (fun i => Fin.natAdd p (rvTagLeftIndex a b i))
def taggedParameterRightIndex (p a b : ℕ) : Fin (p+b) → Fin (p+(1+(a+b))) :=
  Fin.append (Fin.castAdd (1+(a+b))) (fun i => Fin.natAdd p (rvTagRightIndex a b i))

def nativeRVTaggedDomain (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp) :
    GammaDomainFormula B p (1+(a+b)) sp := by
  let st := Fin.append sp (fun _ : Fin (1+(a+b)) => .rv)
  let L := taggedParameterLeftIndex p a b
  let R := taggedParameterRightIndex p a b
  have hL : ∀ i, Fin.append sp (fun _ : Fin a => .rv) i = st (L i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st, L, taggedParameterLeftIndex, Fin.append_left, Fin.append_right]
  have hR : ∀ i, Fin.append sp (fun _ : Fin b => .rv) i = st (R i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st, R, taggedParameterRightIndex, Fin.append_left, Fin.append_right]
  let P (w : Fin (p+(1+(a+b))) → M) :=
    (w (Fin.natAdd p (Fin.castAdd (a+b) 0)) = iRVZero ∧ w ∘ L ∈ D.val ∧
      ∀ j, w (Fin.natAdd p (rvTagRightIndex a b j)) = iRVZero) ∨
    (w (Fin.natAdd p (Fin.castAdd (a+b) 0)) = iRVOne ∧ w ∘ R ∈ E.val ∧
      ∀ j, w (Fin.natAdd p (rvTagLeftIndex a b j)) = iRVZero)
  have h0 (i : Fin (p+(1+(a+b)))) : OriginalSortedPredicate B st (fun w => w i = iRVZero) :=
    OriginalSortedPredicate.equal_named_coordinate i iRVZero (RVNamedTuples.zero_definable B)
  have h1 (i : Fin (p+(1+(a+b)))) : OriginalSortedPredicate B st (fun w => w i = iRVOne) :=
    OriginalSortedPredicate.equal_named_coordinate i iRVOne (RVNamedTuples.one_definable B)
  have hP : OriginalSortedPredicate B st P :=
    ((h0 _).conj (((OriginalSortedPredicate.of_definable D.property).pullback L hL).conj
      (OriginalSortedPredicate.finite_all (fun j => h0 (Fin.natAdd p (rvTagRightIndex a b j)))))).disj
    ((h1 _).conj (((OriginalSortedPredicate.of_definable E.property).pullback R hR).conj
      (OriginalSortedPredicate.finite_all (fun j => h0 (Fin.natAdd p (rvTagLeftIndex a b j))))))
  exact ⟨{w | w ∈ sortedUniverse st ∧ P w}, hP⟩

theorem taggedParameterLeftIndex_row (z : Fin p → M) (w : Fin (1+(a+b)) → M) :
    Fin.append z w ∘ taggedParameterLeftIndex p a b = Fin.append z (w ∘ rvTagLeftIndex a b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply, taggedParameterLeftIndex, Fin.append_left, Fin.append_right]

theorem taggedParameterRightIndex_row (z : Fin p → M) (w : Fin (1+(a+b)) → M) :
    Fin.append z w ∘ taggedParameterRightIndex p a b = Fin.append z (w ∘ rvTagRightIndex a b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply, taggedParameterRightIndex, Fin.append_left, Fin.append_right]

theorem nativeRVTaggedDomain_row (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp)
    (z : Fin p → M) (w : Fin (1+(a+b)) → M) :
    Fin.append z w ∈ (nativeRVTaggedDomain D E).val ↔
      (∃ x : Fin a → M, Fin.append z x ∈ D.val ∧ w = rawRVLeftTag b x) ∨
      (∃ y : Fin b → M, Fin.append z y ∈ E.val ∧ w = rawRVRightTag a y) := by
  change (_ ∈ sortedUniverse _ ∧ ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _))) ↔ _
  rw [taggedParameterLeftIndex_row, taggedParameterRightIndex_row]
  simp only [Fin.append_right]
  constructor
  · rintro ⟨_, h | h⟩
    · exact Or.inl ⟨w ∘ rvTagLeftIndex a b, h.2.1, (rawRVLeftTag_eq w).mpr ⟨h.1, h.2.2⟩⟩
    · exact Or.inr ⟨w ∘ rvTagRightIndex a b, h.2.1, (rawRVRightTag_eq w).mpr ⟨h.1, h.2.2⟩⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · refine ⟨?_, Or.inl ⟨rfl, ?_, fun _ => by simp only [rawRVLeftTag, rvTagRightIndex, Fin.append_right]⟩⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left] using D.property.proper _ hx (Fin.castAdd a j)
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa only [rawRVLeftTag, Fin.append_right, Fin.append_left, sortEval, iRV] using rv_zero_mem hM
          · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
            · simpa only [rawRVLeftTag, Fin.append_right, Fin.append_left] using
                D.property.proper _ hx (Fin.natAdd p j)
            · simpa only [rawRVLeftTag, Fin.append_right, sortEval, iRV] using rv_zero_mem hM
      · simpa only [Function.comp_def, rawRVLeftTag, rvTagLeftIndex, Fin.append_left, Fin.append_right] using hx
    · refine ⟨?_, Or.inr ⟨rfl, ?_, fun _ => by simp only [rawRVRightTag, rvTagLeftIndex, Fin.append_right, Fin.append_left]⟩⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left] using E.property.proper _ hy (Fin.castAdd b j)
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa only [rawRVRightTag, Fin.append_right, Fin.append_left, sortEval, iRV] using rv_one_mem hM
          · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
            · simpa only [rawRVRightTag, Fin.append_right, Fin.append_left, sortEval, iRV] using rv_zero_mem hM
            · simpa only [rawRVRightTag, Fin.append_right] using E.property.proper _ hy (Fin.natAdd p j)
      · simpa only [Function.comp_def, rawRVRightTag, rvTagRightIndex, Fin.append_left, Fin.append_right] using hy

end DiamondIntegral.Section5
