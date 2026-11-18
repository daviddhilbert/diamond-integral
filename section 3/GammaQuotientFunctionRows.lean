import Integration7.GammaFunctionRowValidity

/-! The existing sorted row-quantifier machinery also checks functions
to an imaginary quotient. A row contains every representative of its
value; no representative is selected as a definable function. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

def gammaRepeatedRowIndices (p b : ℕ) : Fin (p+b) → Fin ((p+b)+b) :=
  Fin.addCases (fun j => Fin.castAdd b (Fin.castAdd b j)) (Fin.natAdd (p+b))

def gammaRowTargetPairIndices (p b : ℕ) : Fin (b+b) → Fin ((p+b)+b) :=
  Fin.addCases (fun j => Fin.castAdd b (Fin.natAdd p j)) (Fin.natAdd (p+b))

theorem gammaRepeatedRowIndices_append (z : Fin p → M) (y y' : Fin b → M) :
    Fin.append (Fin.append z y) y' ∘ gammaRepeatedRowIndices p b = Fin.append z y' := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [gammaRepeatedRowIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

theorem gammaRowTargetPairIndices_append (z : Fin p → M) (y y' : Fin b → M) :
    Fin.append (Fin.append z y) y' ∘ gammaRowTargetPairIndices p b = Fin.append y y' := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [gammaRowTargetPairIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

def gammaQuotientGraphRowValid (sp : Fin p → SortTag) (sy : Fin b → SortTag)
    (V : Set (Fin (p+b) → M)) (E : Set (Fin (b+b) → M)) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  ∀ y : Fin b → M, Fin.append z y ∈ V → ∀ y' : Fin b → M,
    (∀ j, sortEval (sy j) (y' j)) → (Fin.append z y' ∈ V ↔ Fin.append y y' ∈ E)

theorem gamma_quotient_graph_row_validity_definable
    (sp : Fin p → SortTag) (sy : Fin b → SortTag)
    {V : Set (Fin (p+b) → M)} {E : Set (Fin (b+b) → M)}
    (hV : DefinableOverBase B (Fin.append sp sy) V)
    (hE : DefinableOverBase B (Fin.append sy sy) E) :
    DefinableOverBase B sp {z | gammaQuotientGraphRowValid sp sy V E z} := by
  let ss := Fin.append (Fin.append sp sy) sy
  let K := {w : Fin ((p+b)+b) → M | w ∘ gammaRepeatedRowIndices p b ∈ V ∧ w ∈ sortedUniverse ss}
  let L := {w : Fin ((p+b)+b) → M | w ∘ gammaRowTargetPairIndices p b ∈ E ∧ w ∈ sortedUniverse ss}
  have hK : DefinableOverBase B ss K := hV.preimage_real ss (gammaRepeatedRowIndices p b)
  have hL : DefinableOverBase B ss L := hE.preimage_real ss (gammaRowTargetPairIndices p b)
  have hEq := gamma_family_row_eq_definable (Fin.append sp sy) sy hK hL
  have h := gamma_family_row_subset_definable sp sy hV hEq
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz,hall⟩
    refine ⟨hz,?_⟩
    intro y hy
    refine ⟨hV.proper _ hy,?_⟩
    intro y'
    change ((_ ∈ V ∧ _) ↔ (_ ∈ E ∧ _))
    rw [gammaRepeatedRowIndices_append,gammaRowTargetPairIndices_append]
    constructor
    · rintro ⟨hv,hs⟩
      have hy' : ∀ j, sortEval (sy j) (y' j) := by
        intro j
        simpa only [ss,Fin.append_right] using hs (Fin.natAdd (p+b) j)
      exact ⟨(hall y hy y' hy').mp hv,hs⟩
    · rintro ⟨he,hs⟩
      have hy' : ∀ j, sortEval (sy j) (y' j) := by
        intro j
        simpa only [ss,Fin.append_right] using hs (Fin.natAdd (p+b) j)
      exact ⟨(hall y hy y' hy').mpr he,hs⟩
  · rintro ⟨hz,hall⟩
    refine ⟨hz,?_⟩
    intro y hy y' hy'
    have hs0 := hV.proper _ hy
    have hs : Fin.append (Fin.append z y) y' ∈ sortedUniverse ss := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [ss,Fin.append_left] using hs0 j
      · simpa only [ss,Fin.append_right] using hy' j
    have he := (hall y hy).2 y'
    change ((_ ∈ V ∧ _) ↔ (_ ∈ E ∧ _)) at he
    rw [gammaRepeatedRowIndices_append,gammaRowTargetPairIndices_append] at he
    exact ⟨fun hv => (he.mp ⟨hv,hs⟩).1,fun he' => (he.mpr ⟨he',hs⟩).1⟩

def gammaQuotientFunctionRowValid (sp : Fin p → SortTag) (sx : Fin a → SortTag) (sy : Fin b → SortTag)
    (D : Set (Fin (p+a) → M)) (V : Set (Fin ((p+a)+b) → M)) (E : Set (Fin (b+b) → M))
    (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  (∀ x : Fin a → M, Fin.append z x ∈ D → ∃ y : Fin b → M, Fin.append (Fin.append z x) y ∈ V) ∧
  (∀ x : Fin a → M, ∀ y : Fin b → M, Fin.append (Fin.append z x) y ∈ V → Fin.append z x ∈ D) ∧
  ∀ x : Fin a → M, (∀ i, sortEval (sx i) (x i)) →
    gammaQuotientGraphRowValid (Fin.append sp sx) sy V E (Fin.append z x)

theorem gamma_quotient_function_row_validity_definable
    (sp : Fin p → SortTag) (sx : Fin a → SortTag) (sy : Fin b → SortTag)
    {D : Set (Fin (p+a) → M)} {V : Set (Fin ((p+a)+b) → M)} {E : Set (Fin (b+b) → M)}
    (hD : DefinableOverBase B (Fin.append sp sx) D)
    (hV : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) V)
    (hE : DefinableOverBase B (Fin.append sy sy) E) :
    DefinableOverBase B sp {z | gammaQuotientFunctionRowValid sp sx sy D V E z} := by
  have hExists := gamma_family_row_exists_definable (Fin.append sp sx) sy hV
  have hTotal := gamma_family_row_subset_definable sp sx hD hExists
  have hSource := gamma_family_row_subset_definable sp sx hExists hD
  have hGraph := gamma_quotient_graph_row_validity_definable (Fin.append sp sx) sy hV hE
  have hAll := gamma_family_row_forall_definable sp sx hGraph
  have h := hTotal.inter (hSource.inter hAll)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz,ht,hd,hg⟩
    exact ⟨⟨hz,ht⟩,⟨⟨hz,fun x ⟨y,hy⟩ => hd x y hy⟩,⟨hz,hg⟩⟩⟩
  · rintro ⟨⟨hz,ht⟩,⟨⟨_,hd⟩,⟨_,hg⟩⟩⟩
    exact ⟨hz,ht,fun x y hxy => hd x ⟨y,hxy⟩,hg⟩

end DiamondIntegral.Section3
