import «section 6».RelativeFibreGraphRestrictions
import Section4.PolynomialZero

/-! Complete original-base real graphs for relative polynomial lifts.
The inactive VF diagonal is imposed literally in the real graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def relativePolynomialGraph {E : Subfield (VF M)}
    (H : Fin n → MvPolynomial (Fin (n+n)) E) (i : Fin n) : Set (Fin (n+n) → M) :=
  {x | (∀ j,x ∈ PolynomialZero.zeroSet E (H j)) ∧
    ∀ j,j ≠ i → x (productRight n n j) = x (productLeft n n j)}

theorem relativePolynomialGraph_definable {E : Subfield (VF M)}
    (hE : ∀ c : E,c.val.val ∈ S) (H : Fin n → MvPolynomial (Fin (n+n)) E) (i : Fin n) :
    S.Definable LRV (relativePolynomialGraph H i) := by
  have hP : S.Definable LRV {x : Fin (n+n) → M | ∀ j,x ∈ PolynomialZero.zeroSet E (H j)} := by
    simp only [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun j =>
      (PolynomialZero.zeroSet_named_definable S E hE (H j)).raw_definable)
  have hD : S.Definable LRV {x : Fin (n+n) → M | ∀ j,j ≠ i →
      x (productRight n n j) = x (productLeft n n j)} := by
    have hD' : S.Definable LRV {x : Fin (n+n) → M | ∀ j : {j : Fin n // j ≠ i},
        x (productRight n n j.val) = x (productLeft n n j.val)} := by
      simp only [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite (fun j =>
        (Set.DefinableFun.proj LRV (i := productRight n n j.val)).ofPred_eq
          (Set.DefinableFun.proj LRV (i := productLeft n n j.val)))
    have he : {x : Fin (n+n) → M | ∀ j,j ≠ i →
        x (productRight n n j) = x (productLeft n n j)} =
        {x : Fin (n+n) → M | ∀ j : {j : Fin n // j ≠ i},
          x (productRight n n j.val) = x (productLeft n n j.val)} := by
      ext x
      exact ⟨fun h j => h j.val j.property,fun h j hj => h ⟨j,hj⟩⟩
    rw [he]
    exact hD'
  exact hP.inter hD

theorem relativePolynomialGraph_vf {E : Subfield (VF M)}
    (H : Fin n → MvPolynomial (Fin (n+n)) E) (i : Fin n)
    (x : Fin (n+n) → M) (hx : x ∈ relativePolynomialGraph H i) : ∀ j,iVF (x j) :=
  (hx.1 i).choose

theorem relativePolynomialGraph_iff {E : Subfield (VF M)}
    (H : Fin n → MvPolynomial (Fin (n+n)) E) (i : Fin n) (a b : Fin n → VF M) :
    productTuple (rawVF a) (rawVF b) ∈ relativePolynomialGraph H i ↔
      (∀ j,((H j).map E.subtype).eval (productTuple a b) = 0) ∧
        ∀ j,j ≠ i → b j = a j := by
  have hRaw : productTuple (rawVF a) (rawVF b) = rawVF (productTuple a b) := by
    apply productTuple_ext
    · intro j
      rw [productTuple_left]
      change (a j).val = (productTuple a b (productLeft n n j)).val
      rw [productTuple_left]
    · intro j
      rw [productTuple_right]
      change (b j).val = (productTuple a b (productRight n n j)).val
      rw [productTuple_right]
  rw [hRaw]
  change (∀ j,rawVF (productTuple a b) ∈ PolynomialZero.zeroSet E (H j)) ∧
    (∀ j,j ≠ i → (rawVF (productTuple a b)) (productRight n n j) =
      (rawVF (productTuple a b)) (productLeft n n j)) ↔ _
  apply and_congr
  · apply forall_congr'
    intro j
    rw [eval_map]
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨fun k => (productTuple a b k).property,h⟩⟩
  · constructor
    · intro h j hj
      apply Subtype.ext
      have he := h j hj
      change (productTuple a b (productRight n n j)).val =
        (productTuple a b (productLeft n n j)).val at he
      simpa only [productTuple_right,productTuple_left] using he
    · intro h j hj
      have he := congrArg Subtype.val (h j hj)
      change (productTuple a b (productRight n n j)).val =
        (productTuple a b (productLeft n n j)).val
      simpa only [productTuple_right,productTuple_left] using he

theorem relativePolynomialGraph_fibreBijection {G : Type} [LinearOrderedCommGroupWithZero G]
    (v : Valuation (VF M) G) {E : Subfield (VF M)}
    (H : Fin n → MvPolynomial (Fin (n+n)) E) (i : Fin n) (t s : Fin n → RVCalc.RV v)
    (hLift : FibreBijection v {p | ∀ j,((H j).map E.subtype).eval (productTuple p.1 p.2) = 0} t s)
    (hFixed : ∀ a ∈ RVFibre v t,∀ b ∈ RVFibre v s,
      (∀ j,((H j).map E.subtype).eval (productTuple a b) = 0) → ∀ j,j ≠ i → b j = a j) :
    FibreBijection v {p | productTuple (rawVF p.1) (rawVF p.2) ∈ relativePolynomialGraph H i} t s := by
  apply fibreBijection_congr_on_fibres v (fibreBijection_restrict_inactive_diagonal v i hLift hFixed)
  intro a ha b hb
  exact (relativePolynomialGraph_iff H i a b).symm

end DiamondIntegral.Section6
