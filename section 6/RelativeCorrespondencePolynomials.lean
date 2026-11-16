import «section 6».RelativeWeightedPolynomialLifting

/-! A genuine finite-to-finite RV correspondence with unchanged
inactive coordinates has original-field weighted lifting equations
whose full VF fibre bijection fixes those coordinates exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n : ℕ}

theorem exists_relative_correspondence_weighted_local_polynomials
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y)
    (C : Set (Fin (n+n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (t s : Fin n → RVCalc.RV v) (ht : ∀ j,t j ≠ none) (hs : ∀ j,s j ≠ none)
    (i : Fin n) (hFixed : ∀ j,j ≠ i → t j = s j)
    (hPair : productTuple (fun j => (CanonicalRV.equiv v hv (t j)).val)
      (fun j => (CanonicalRV.equiv v hv (s j)).val) ∈ C)
    (hRight : {b : Fin n → M | productTuple (fun j => (CanonicalRV.equiv v hv (t j)).val) b ∈ C}.Finite)
    (hLeft : {a : Fin n → M | productTuple a (fun j => (CanonicalRV.equiv v hv (s j)).val) ∈ C}.Finite) :
    let E := vfDefinableClosureFieldBase B
    ∃ (H : Fin n → MvPolynomial (Fin (n+n)) E) (w : Fin n → G),
      let W := fun j => (H j).map E.subtype
      (∀ j,IsGammaPolynomial v (fun k => RVCalc.vrv v (productTuple t s k)) (w j) (W j)) ∧
      ¬ IsResidueRoot v (productTuple t s) (jacobianValue (fun j => RVCalc.vrv v (t j)) w)
        (partialJacobianPolynomial (productLeft n n) W) ∧
      ¬ IsResidueRoot v (productTuple t s) (jacobianValue (fun j => RVCalc.vrv v (s j)) w)
        (partialJacobianPolynomial (productRight n n) W) ∧
      FibreBijection v {p | ∀ j,(W j).eval (productTuple p.1 p.2) = 0} t s ∧
      ∀ a ∈ RVFibre v t,∀ b ∈ RVFibre v s,
        (∀ j,(W j).eval (productTuple a b) = 0) → ∀ j,j ≠ i → b j = a j := by
  let raw (u : RVCalc.RV v) := (CanonicalRV.equiv v hv u).val
  have hAlgR : AlgebraicAtBase ⟨B.real ∪ Set.range (fun j => raw (t j)),B.gamma⟩ .rv (raw (s i)) :=
    correspondenceRight_algebraic B C hC (fun j => raw (t j)) (fun j => raw (s j)) hPair hRight i
  have hAlgL : AlgebraicAtBase ⟨B.real ∪ Set.range (fun j => raw (s j)),B.gamma⟩ .rv (raw (t i)) :=
    correspondenceLeft_algebraic B C hC (fun j => raw (t j)) (fun j => raw (s j)) hPair hLeft i
  obtain ⟨α,β,F,Q,hF,hQ,hFR,hQR,hFD,hQD,hFO,hQO,hDiag⟩ :=
    exists_relative_coordinate_polynomial_systems hκ hsat h00 B hsmall hB v hv t s ht hs i hFixed hAlgR hAlgL
  exact exists_weighted_relative_polynomial_lift h00 v hv (vfDefinableClosureFieldBase B)
    t s ht hs i hFixed α β F Q hF hQ hFR hQR hFD hQD hFO hQO hDiag

end DiamondIntegral.Section6
