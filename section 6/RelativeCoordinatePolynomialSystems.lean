import «section 6».RelativeDiagonalPolynomials

/-! Original-field local equations for a relatively unary RV
correspondence. Every inactive row is the literal diagonal equation;
only the active row uses the checked algebraic lifting polynomial. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n : ℕ}

theorem exists_relative_coordinate_polynomial_systems
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ v x ≤ v y)
    (t s : Fin n → RVCalc.RV v) (ht : ∀ j,t j ≠ none) (hs : ∀ j,s j ≠ none)
    (i : Fin n) (hFixed : ∀ j,j ≠ i → t j = s j)
    (hRight : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun j => (CanonicalRV.equiv v hv (t j)).val),B.gamma⟩
        .rv (CanonicalRV.equiv v hv (s i)).val)
    (hLeft : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun j => (CanonicalRV.equiv v hv (s j)).val),B.gamma⟩
        .rv (CanonicalRV.equiv v hv (t i)).val) :
    let E := vfDefinableClosureFieldBase B
    let u := productTuple t s
    let γ := fun j => RVCalc.vrv v (u j)
    ∃ (α β : Fin n → G) (F H : Fin n → MvPolynomial (Fin (n+n)) E),
      (∀ j,IsGammaPolynomial v γ (α j) ((F j).map E.subtype)) ∧
      (∀ j,IsGammaPolynomial v γ (β j) ((H j).map E.subtype)) ∧
      (∀ j,IsResidueRoot v u (α j) ((F j).map E.subtype)) ∧
      (∀ j,IsResidueRoot v u (β j) ((H j).map E.subtype)) ∧
      (∀ j,¬ IsResidueRoot v u (α j / γ (productRight n n j))
        (pderiv (productRight n n j) ((F j).map E.subtype))) ∧
      (∀ j,¬ IsResidueRoot v u (β j / γ (productLeft n n j))
        (pderiv (productLeft n n j) ((H j).map E.subtype))) ∧
      (∀ j l,j ≠ l → pderiv (productRight n n l) ((F j).map E.subtype) = 0) ∧
      (∀ j l,j ≠ l → pderiv (productLeft n n l) ((H j).map E.subtype) = 0) ∧
      ∀ j,j ≠ i → F j = relativeDiagonalPolynomial E n j ∧ H j = relativeDiagonalPolynomial E n j := by
  let E := vfDefinableClosureFieldBase B
  let L := productLeft n n
  let R := productRight n n
  let u := productTuple t s
  let γ := fun j => RVCalc.vrv v (u j)
  have hu (j : Fin (n+n)) : u j ≠ none := by
    obtain ⟨k,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)).surjective j
    cases k with
    | inl j =>
      change u (productLeft n n j) ≠ none
      simpa only [u,productTuple_left] using ht j
    | inr j =>
      change u (productRight n n j) ≠ none
      simpa only [u,productTuple_right] using hs j
  have hR (j : Fin n) : R j ∉ Set.range L := fun ⟨k,h⟩ => productLeft_ne_right k j h
  have hL (j : Fin n) : L j ∉ Set.range R := fun ⟨k,h⟩ => productLeft_ne_right j k h.symm
  have hRight' : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun j => (CanonicalRV.equiv v hv (u (L j))).val),B.gamma⟩
        .rv (CanonicalRV.equiv v hv (u (R i))).val := by
    simpa only [u,L,R,productTuple_left,productTuple_right] using hRight
  have hLeft' : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun j => (CanonicalRV.equiv v hv (u (R j))).val),B.gamma⟩
        .rv (CanonicalRV.equiv v hv (u (L i))).val := by
    simpa only [u,L,R,productTuple_left,productTuple_right] using hLeft
  obtain ⟨a,P,hPG,hPR,hPD,hPO⟩ := exists_originalPolynomial_for_coordinate
    hκ hsat h00 B hsmall hB v hv L (R i) (hR i) u hu hRight'
  obtain ⟨b,Q,hQG,hQR,hQD,hQO⟩ := exists_originalPolynomial_for_coordinate
    hκ hsat h00 B hsmall hB v hv R (L i) (hL i) u hu hLeft'
  let α (j : Fin n) := if j=i then a else RVCalc.vrv v (t j)
  let β (j : Fin n) := if j=i then b else RVCalc.vrv v (t j)
  let F (j : Fin n) := if j=i then P else relativeDiagonalPolynomial E n j
  let H (j : Fin n) := if j=i then Q else relativeDiagonalPolynomial E n j
  have hDiag (j : Fin n) (hj : j ≠ i) := relativeDiagonalPolynomial_weighted_data v t s ht hs j (hFixed j hj)
  refine ⟨α,β,F,H,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    by_cases hj : j=i
    · subst j
      simpa only [F,α,if_pos rfl] using hPG
    · simpa only [F,α,if_neg hj,E,relativeDiagonalPolynomial_map] using (hDiag j hj).1
  · intro j
    by_cases hj : j=i
    · subst j
      simpa only [H,β,if_pos rfl] using hQG
    · simpa only [H,β,if_neg hj,E,relativeDiagonalPolynomial_map] using (hDiag j hj).1
  · intro j
    by_cases hj : j=i
    · subst j
      simpa only [F,α,if_pos rfl] using hPR
    · simpa only [F,α,if_neg hj,E,relativeDiagonalPolynomial_map] using (hDiag j hj).2.1
  · intro j
    by_cases hj : j=i
    · subst j
      simpa only [H,β,if_pos rfl] using hQR
    · simpa only [H,β,if_neg hj,E,relativeDiagonalPolynomial_map] using (hDiag j hj).2.1
  · intro j
    by_cases hj : j=i
    · subst j
      simpa only [F,α,if_pos rfl] using hPD
    · simpa only [F,α,if_neg hj,E,relativeDiagonalPolynomial_map] using (hDiag j hj).2.2.1
  · intro j
    by_cases hj : j=i
    · subst j
      simpa only [H,β,if_pos rfl] using hQD
    · simpa only [H,β,if_neg hj,E,relativeDiagonalPolynomial_map] using (hDiag j hj).2.2.2
  · intro j l hjl
    by_cases hj : j=i
    · subst j
      simpa only [F,if_pos rfl] using hPO (R l) (hR l) (fun h => hjl (R.injective h).symm)
    · simpa only [F,if_neg hj,E,relativeDiagonalPolynomial_map] using
        (relativeDiagonalPolynomial_off_partials (K := VF M) j l hjl).1
  · intro j l hjl
    by_cases hj : j=i
    · subst j
      simpa only [H,if_pos rfl] using hQO (L l) (hL l) (fun h => hjl (L.injective h).symm)
    · simpa only [H,if_neg hj,E,relativeDiagonalPolynomial_map] using
        (relativeDiagonalPolynomial_off_partials (K := VF M) j l hjl).2
  · intro j hj
    simp only [F,H,if_neg hj,E,and_self]

end DiamondIntegral.Section6
