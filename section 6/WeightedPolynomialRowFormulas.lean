import «section 6».RelativeCoordinatePolynomialSystems

/-! A local strengthening of the checked weighted polynomial system
construction. Its integer row formula is retained explicitly, so exact
diagonal equations can be tracked through the construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Classical MvPolynomial IsLocalRing
open SpecialTransformations.Section7
namespace DiamondIntegral.Section6

set_option backward.isDefEq.respectTransparency true in
theorem polynomial_integer_row_eval {R : Type*} [CommRing R] {ι σ : Type*}
    (F G : ι → MvPolynomial σ R) (p q : ι → ℤ) (i : ι) (x : σ → R) :
    (integerPolynomialCombination F G p q i).eval x = p i • (F i).eval x + q i • (G i).eval x := by
  change (MvPolynomial.eval x) (p i • F i + q i • G i) = _
  exact ((MvPolynomial.eval x).map_add _ _).trans (congrArg₂ (fun a b : R => a+b)
    (_root_.map_zsmul (MvPolynomial.eval x) (p i) (F i))
    (_root_.map_zsmul (MvPolynomial.eval x) (q i) (G i)))

set_option backward.isDefEq.respectTransparency true in
theorem polynomial_integer_row_map {R T : Type*} [CommRing R] [CommRing T] {ι σ : Type*}
    (φ : R →+* T) (F G : ι → MvPolynomial σ R) (p q : ι → ℤ) (i : ι) :
    (integerPolynomialCombination F G p q i).map φ =
      integerPolynomialCombination (fun j => (F j).map φ) (fun j => (G j).map φ) p q i := by
  change (MvPolynomial.map φ) (p i • F i + q i • G i) = _
  exact ((MvPolynomial.map φ).map_add _ _).trans
    (congrArg₂ (fun a b : MvPolynomial σ T => a+b)
    (_root_.map_zsmul (MvPolynomial.map φ) (p i) (F i))
    (_root_.map_zsmul (MvPolynomial.map φ) (q i) (G i)))

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem exists_weighted_polynomial_system_with_row_formula [IsAlgClosed K]
    (v : Valuation K Γ) [CharZero (ResidueField v.valuationSubring)] (E : Subfield K)
    {n : ℕ} (t s : Fin n → RVCalc.RV v) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none)
    (α β : Fin n → Γ) (F G : Fin n → MvPolynomial (Fin (n + n)) E) :
    let u := productTuple t s
    let γ := fun j => RVCalc.vrv v (u j)
    let f := fun i => (F i).map E.subtype
    let g := fun i => (G i).map E.subtype
    (∀ i, IsGammaPolynomial v γ (α i) (f i)) →
    (∀ i, IsGammaPolynomial v γ (β i) (g i)) →
    (∀ i, IsResidueRoot v u (α i) (f i)) →
    (∀ i, IsResidueRoot v u (β i) (g i)) →
    (∀ i, ¬ IsResidueRoot v u (α i / γ (productRight n n i))
      (pderiv (productRight n n i) (f i))) →
    (∀ i, ¬ IsResidueRoot v u (β i / γ (productLeft n n i))
      (pderiv (productLeft n n i) (g i))) →
    (∀ i j, i ≠ j → pderiv (productRight n n j) (f i) = 0) →
    (∀ i j, i ≠ j → pderiv (productLeft n n j) (g i) = 0) →
    ∃ (H : Fin n → MvPolynomial (Fin (n + n)) E) (w : Fin n → Γ),
      let Z := fun i => (H i).map E.subtype
      (∀ i, IsGammaPolynomial v γ (w i) (Z i)) ∧
      ¬ IsResidueRoot v u (jacobianValue (fun j => γ (productLeft n n j)) w)
        (partialJacobianPolynomial (productLeft n n) Z) ∧
      ¬ IsResidueRoot v u (jacobianValue (fun j => γ (productRight n n j)) w)
        (partialJacobianPolynomial (productRight n n) Z) ∧
      FibreBijection v {p | ∀ i, (Z i).eval (productTuple p.1 p.2) = 0} t s ∧
      ∀ i, ∃ p q : ℤ, H i =
        p • ((X (productLeft n n i) * pderiv (productLeft n n i) (G i)) * F i) +
        q • ((X (productRight n n i) * pderiv (productRight n n i) (F i)) * G i) := by
  classical
  let u := productTuple t s
  let γ := fun j => RVCalc.vrv v (u j)
  let f := fun i => (F i).map E.subtype
  let g := fun i => (G i).map E.subtype
  let L := productLeft n n
  let R := productRight n n
  change (∀ i, IsGammaPolynomial v γ (α i) (f i)) →
    (∀ i, IsGammaPolynomial v γ (β i) (g i)) →
    (∀ i, IsResidueRoot v u (α i) (f i)) →
    (∀ i, IsResidueRoot v u (β i) (g i)) →
    (∀ i, ¬ IsResidueRoot v u (α i / γ (R i)) (pderiv (R i) (f i))) →
    (∀ i, ¬ IsResidueRoot v u (β i / γ (L i)) (pderiv (L i) (g i))) →
    (∀ i j, i ≠ j → pderiv (R j) (f i) = 0) →
    (∀ i j, i ≠ j → pderiv (L j) (g i) = 0) → _
  intro hf hg hfr hgr hdf hdg hoffF hoffG
  have hu (j : Fin (n + n)) : u j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change u (L i) ≠ none
      simpa [u, L] using ht i
    | inr i =>
      change u (R i) ≠ none
      simpa [u, R] using hs i
  obtain ⟨a, ha⟩ := rvFibre_nonempty v u
  have hav : ∀ j, v (a j) = γ j := rvFibre_value v ha
  have hγ (j : Fin (n + n)) : γ j ≠ 0 := by
    rw [← hav j]
    exact (Valuation.ne_zero_iff v).mpr (fun h => hu j ((ha j).symm.trans (h ▸ RVCalc.rv_zero)))
  have hvF (i : Fin n) : v ((pderiv (R i) (f i)).eval a) = α i / γ (R i) :=
    (not_residueRoot_iff_eval_eq v hu ((hf i).pderiv v (R i))).mp (hdf i) a ha
  have hvG (i : Fin n) : v ((pderiv (L i) (g i)).eval a) = β i / γ (L i) :=
    (not_residueRoot_iff_eval_eq v hu ((hg i).pderiv v (L i))).mp (hdg i) a ha
  let A := fun i => X (L i) * pderiv (L i) (g i)
  let D := fun i => X (R i) * pderiv (R i) (f i)
  have hA (i : Fin n) : IsGammaPolynomial v γ (β i) (A i) :=
    gammaPolynomial_derivativeMultiplier v (hg i) (L i)
  have hD (i : Fin n) : IsGammaPolynomial v γ (α i) (D i) :=
    gammaPolynomial_derivativeMultiplier v (hf i) (R i)
  have hAv (i : Fin n) : v ((A i).eval a) = β i :=
    derivativeMultiplier_eval_value v (hg i) (L i) a hav (hvG i)
  have hDv (i : Fin n) : v ((D i).eval a) = α i :=
    derivativeMultiplier_eval_value v (hf i) (R i) a hav (hvF i)
  let w := fun i => β i * α i
  let f' := fun i => A i * f i
  let g' := fun i => D i * g i
  have hf' (i : Fin n) : IsGammaPolynomial v γ (w i) (f' i) := (hA i).mul v (hf i)
  have hg' (i : Fin n) : IsGammaPolynomial v γ (w i) (g' i) := by
    simpa only [w, mul_comm (β i) (α i)] using (hD i).mul v (hg i)
  have hfr' (i : Fin n) : IsResidueRoot v u (w i) (f' i) :=
    residueRoot_mul_left v (hA i) (hfr i)
  have hgr' (i : Fin n) : IsResidueRoot v u (w i) (g' i) := by
    simpa only [w, mul_comm (β i) (α i)] using residueRoot_mul_left v (hD i) (hgr i)
  let e := fun i => ((A i).eval a * (D i).eval a)⁻¹
  have he (i : Fin n) : v (e i) * w i = 1 := by
    dsimp only [e, w]
    rw [map_inv₀, map_mul, hAv, hDv]
    exact inv_mul_cancel₀ (hf' i).2.1
  have hdF (i : Fin n) : v ((pderiv (R i) (f' i)).eval a) = w i / γ (R i) :=
    derivative_weighted_mul_eval_eq v (hA i) (R i) a hav (hfr i a ha) (hAv i) (hvF i)
  have hdG (i : Fin n) : v ((pderiv (L i) (g' i)).eval a) = w i / γ (L i) := by
    simpa only [w, mul_comm (β i) (α i)] using
      derivative_weighted_mul_eval_eq v (hD i) (L i) a hav (hgr i a ha) (hDv i) (hvG i)
  have hoF (i j : Fin n) (hij : i ≠ j) : v ((pderiv (R j) (f' i)).eval a) < w i / γ (R j) := by
    apply derivative_weighted_mul_eval_lt v (hA i) (R j) a hav (hfr i a ha) (hAv i)
    rw [hoffF i j hij, map_zero, map_zero]
    exact pos_iff_ne_zero.mpr (div_ne_zero (hf i).2.1 (hγ _))
  have hoG (i j : Fin n) (hij : i ≠ j) : v ((pderiv (L j) (g' i)).eval a) < w i / γ (L j) := by
    dsimp only [w]
    rw [mul_comm (β i) (α i)]
    apply derivative_weighted_mul_eval_lt v (hD i) (L j) a hav (hgr i a ha) (hDv i)
    rw [hoffG i j hij, map_zero, map_zero]
    exact pos_iff_ne_zero.mpr (div_ne_zero (hg i).2.1 (hγ _))
  have hdetF := residuePartialJacobian_det_ne_zero_of_diagonal v f' a e hf' hav he R hdF hoF
  have hdetG := residuePartialJacobian_det_ne_zero_of_diagonal v g' a e hg' hav he L hdG hoG
  obtain ⟨p, q, hR, hL⟩ :=
    exists_integerCombination_partialJacobians v f' g' a e hf' hg' hav he R L hdetF hdetG
  let Z := integerPolynomialCombination f' g' p q
  have hZ := integerPolynomialCombination_gamma v f' g' hf' hg' p q
  have hZr (i : Fin n) : IsResidueRoot v u (w i) (Z i) := by
    intro x hx
    change v ((integerPolynomialCombination f' g' p q i).eval x) < w i
    rw [polynomial_integer_row_eval]
    exact v.map_add_lt (valuation_zsmul_lt v (hfr' i x hx) (p i))
      (valuation_zsmul_lt v (hgr' i x hx) (q i))
  have hJR := partialJacobian_not_residueRoot_of_residue_det_ne_zero v hu Z hZ a ha e he R hR
  have hJL := partialJacobian_not_residueRoot_of_residue_det_ne_zero v hu Z hZ a ha e he L hL
  let H := integerPolynomialCombination
    (fun i => (X (L i) * pderiv (L i) (G i)) * F i)
    (fun i => (X (R i) * pderiv (R i) (F i)) * G i) p q
  have hmap : (fun i => (H i).map E.subtype) = Z := by
    funext i
    rw [polynomial_integer_row_map]
    simp only [Z, integerPolynomialCombination, f', g', A, D, f, g,
      (MvPolynomial.map E.subtype).map_mul,MvPolynomial.map_X E.subtype,pderiv_map]
  refine ⟨H, w, ?_⟩
  let W := fun i => (H i).map E.subtype
  change (∀ i, IsGammaPolynomial v γ (w i) (W i)) ∧
    ¬ IsResidueRoot v u (jacobianValue (fun j => γ (L j)) w) (partialJacobianPolynomial L W) ∧
    ¬ IsResidueRoot v u (jacobianValue (fun j => γ (R j)) w) (partialJacobianPolynomial R W) ∧
    FibreBijection v {p | ∀ i, (W i).eval (productTuple p.1 p.2) = 0} t s ∧
    ∀ i, ∃ p q : ℤ, H i =
      p • ((X (productLeft n n i) * pderiv (productLeft n n i) (G i)) * F i) +
      q • ((X (productRight n n i) * pderiv (productRight n n i) (F i)) * G i)
  rw [show W = Z from hmap]
  exact ⟨hZ, hJL, hJR, fibreBijection_of_polynomial_partialJacobians v t s ht hs Z hZ hZr
    (by simpa only [u, L, productTuple_left] using hJL)
    (by simpa only [u, R, productTuple_right] using hJR),fun i => ⟨p i,q i,rfl⟩⟩

end DiamondIntegral.Section6
