import «section 3».GammaGroundRVInfiniteRows
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The finite coordinate substitution used to test one generic row. -/
def rvGenericCoordinateInput {n : ℕ} (i : Fin n) : Fin n → Fin (n+1) :=
  fun j => if j = i then Fin.last n else j.castSucc

/-- Generic truth in coordinate i, retaining the original tuple as a
full value-code tuple. It is an actual same-ground definable operation. -/
def rvGenericCoordinate {n : ℕ} (A : Set (Fin n → M)) (i : Fin n) : Set (Fin n → M) :=
  {p | (p ∘ (Fin.lastCases i id)) ∈ rvInfiniteLast
      {q : Fin (n+1) → M | q ∘ rvGenericCoordinateInput i ∈ A ∧
        q ∈ sortedUniverse (fun _ => .rv)} ∧ p ∈ sortedUniverse (fun _ => .rv)}

theorem rvGenericCoordinate_definableOverBase {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A) (i : Fin n) :
    DefinableOverBase B (fun _ => .rv) (rvGenericCoordinate A i) := by
  have h := hA.preimage_real (fun _ : Fin (n+1) => .rv) (rvGenericCoordinateInput i)
  have hi := rvInfiniteLast_definableOverBase hc hs h00 B hsmall _ h
  exact hi.preimage_real (fun _ : Fin n => .rv) (Fin.lastCases i id)

/-- Arbitrary finite iteration of the coordinate selectors stays over
the original ground, including the empty iteration in degree zero. -/
theorem rvGenericCoordinate_fold_definableOverBase {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (L : List (Fin n)) :
    DefinableOverBase B (fun _ => .rv) (L.foldl rvGenericCoordinate A) := by
  induction L generalizing A with
  | nil => exact hA
  | cons i L ih => exact ih _ (rvGenericCoordinate_definableOverBase hc hs h00 B hsmall A hA i)

/-- Pointwise semantics: the selector asks for infinitely many replacements
in the same value fibre, with every other coordinate fixed. -/
theorem mem_rvGenericCoordinate_iff {n : ℕ} (A : Set (Fin n → M)) (i : Fin n)
    (p : Fin n → M) (hp : ∀ j, sortEval .rv (p j)) :
    p ∈ rvGenericCoordinate A i ↔ NonzeroRV (p i) ∧
      {x | SameScalar x (p i) ∧ Function.update p i x ∈ A}.Infinite := by
  have he : p ∘ (Fin.lastCases i id) = Fin.snoc p (p i) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
  have hu (x : M) : Fin.snoc p x ∘ rvGenericCoordinateInput i = Function.update p i x := by
    funext j
    by_cases hj : j = i
    · simp [rvGenericCoordinateInput,hj]
    · simp [rvGenericCoordinateInput,hj,Ne.symm hj]
  change (_ ∧ p ∈ sortedUniverse (fun _ => .rv)) ↔ _
  rw [and_iff_left (show p ∈ sortedUniverse (fun _ => .rv) from hp)]
  rw [he]
  simp only [rvInfiniteLast,Set.mem_setOf_eq,Fin.snoc_last,Fin.init_snoc]
  apply and_congr_right
  intro hi
  have hs : {x | SameScalar x (p i) ∧
      Fin.snoc p x ∘ rvGenericCoordinateInput i ∈ A ∧
      Fin.snoc p x ∈ sortedUniverse (fun _ => .rv)} =
      {x | SameScalar x (p i) ∧ Function.update p i x ∈ A} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [hu x]
    constructor
    · exact fun h => ⟨h.1,h.2.1⟩
    · intro h
      refine ⟨h.1,h.2,?_⟩
      intro j
      refine Fin.lastCases ?_ (fun k => by simpa only [Fin.snoc_castSucc] using hp k) j
      simpa only [Fin.snoc_last,iRV,sortEval] using h.1.1.1
  rw [hs]

end DiamondIntegral.Section3
