import «section 6».RVJacobianLifting
import Section7.CorrespondenceLifting

/-! Original-field diagonal equations for unchanged VF coordinates.
Their weighted residue roots have simple derivatives in both blocks,
so they can accompany the single active lifting equation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical MvPolynomial
open SpecialTransformations.Section7 SpecialTransformations.Section9
namespace DiamondIntegral.Section6
variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G] {n : ℕ}

def relativeDiagonalPolynomial (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin (n+n)) R := X (productRight n n j) - X (productLeft n n j)

theorem relativeDiagonalPolynomial_map {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (j : Fin n) :
    (relativeDiagonalPolynomial R n j).map f = relativeDiagonalPolynomial T n j := by
  change (MvPolynomial.map f) (X (productRight n n j) - X (productLeft n n j)) =
    X (productRight n n j) - X (productLeft n n j)
  rw [(MvPolynomial.map f).map_sub,MvPolynomial.map_X,MvPolynomial.map_X]

theorem relativeDiagonalPolynomial_partials (j : Fin n) :
    pderiv (productRight n n j) (relativeDiagonalPolynomial K n j) = 1 ∧
      pderiv (productLeft n n j) (relativeDiagonalPolynomial K n j) = -1 := by
  have h := productLeft_ne_right j j
  constructor
  · rw [relativeDiagonalPolynomial,(pderiv (productRight n n j)).map_sub,
      pderiv_X_self,pderiv_X_of_ne h,sub_zero]
  · rw [relativeDiagonalPolynomial,(pderiv (productLeft n n j)).map_sub,
      pderiv_X_of_ne h.symm,pderiv_X_self,zero_sub]

theorem relativeDiagonalPolynomial_off_partials (i j : Fin n) (hij : i ≠ j) :
    pderiv (productRight n n j) (relativeDiagonalPolynomial K n i) = 0 ∧
      pderiv (productLeft n n j) (relativeDiagonalPolynomial K n i) = 0 := by
  have hR : productRight n n j ≠ productRight n n i := fun h => hij ((productRight n n).injective h).symm
  have hL : productLeft n n j ≠ productLeft n n i := fun h => hij ((productLeft n n).injective h).symm
  have hRL := (productLeft_ne_right i j).symm
  have hLR := productLeft_ne_right j i
  constructor
  · rw [relativeDiagonalPolynomial,(pderiv (productRight n n j)).map_sub,
      pderiv_X_of_ne hR.symm,pderiv_X_of_ne hRL.symm,sub_self]
  · rw [relativeDiagonalPolynomial,(pderiv (productLeft n n j)).map_sub,
      pderiv_X_of_ne hLR.symm,pderiv_X_of_ne hL.symm,sub_self]

theorem relativeDiagonalPolynomial_weighted_data (v : Valuation K G)
    (t s : Fin n → RVCalc.RV v) (ht : ∀ i,t i ≠ none) (hs : ∀ i,s i ≠ none)
    (j : Fin n) (hj : t j = s j) :
    let u := productTuple t s
    let γ := fun i => RVCalc.vrv v (u i)
    let α := RVCalc.vrv v (t j)
    let P := relativeDiagonalPolynomial K n j
    IsGammaPolynomial v γ α P ∧ IsResidueRoot v u α P ∧
      ¬ IsResidueRoot v u (α / γ (productRight n n j)) (pderiv (productRight n n j) P) ∧
      ¬ IsResidueRoot v u (α / γ (productLeft n n j)) (pderiv (productLeft n n j) P) := by
  let u := productTuple t s
  let γ := fun i => RVCalc.vrv v (u i)
  let α := RVCalc.vrv v (t j)
  let P := relativeDiagonalPolynomial K n j
  have hu (i : Fin (n+n)) : u i ≠ none := by
    obtain ⟨a,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)).surjective i
    cases a with
    | inl i =>
      change u (productLeft n n i) ≠ none
      simpa only [u,productTuple_left] using ht i
    | inr i =>
      change u (productRight n n i) ≠ none
      simpa only [u,productTuple_right] using hs i
  obtain ⟨a,ha⟩ := rvFibre_nonempty v u
  have hγ (i : Fin (n+n)) : γ i ≠ 0 := by
    change RVCalc.vrv v (u i) ≠ 0
    rw [← rvFibre_value v ha i]
    exact v.ne_zero_iff.mpr (fun he => hu i ((ha i).symm.trans (he ▸ RVCalc.rv_zero)))
  have hL : γ (productLeft n n j) = α := by
    change RVCalc.vrv v (productTuple t s (productLeft n n j)) = RVCalc.vrv v (t j)
    rw [productTuple_left]
  have hR : γ (productRight n n j) = α := by
    change RVCalc.vrv v (productTuple t s (productRight n n j)) = _
    rw [productTuple_right,← hj]
  have hα : α ≠ 0 := hL ▸ hγ (productLeft n n j)
  have hPG : IsGammaPolynomial v γ α P := by
    have h₁ := isGammaPolynomial_X v hγ (productRight n n j)
    have h₂ := isGammaPolynomial_X v hγ (productLeft n n j)
    rw [hR] at h₁
    rw [hL] at h₂
    simpa only [P,relativeDiagonalPolynomial,sub_eq_add_neg] using h₁.add v (h₂.neg v)
  have hPR : IsResidueRoot v u α P := by
    intro x hx
    have hz : x (productLeft n n j) ≠ 0 := by
      intro he
      exact hu (productLeft n n j) (((hx (productLeft n n j)).symm.trans (he ▸ RVCalc.rv_zero)))
    have heq : RVCalc.rv v (x (productRight n n j)) = RVCalc.rv v (x (productLeft n n j)) := by
      rw [hx (productRight n n j),hx (productLeft n n j)]
      exact (productTuple_right t s j).trans (hj.symm.trans (productTuple_left t s j).symm)
    have h := (rv_eq_centre_iff v hz _).mp heq
    change v ((P.eval x)) < α
    have heval : P.eval x = x (productRight n n j) - x (productLeft n n j) := by
      change (MvPolynomial.eval x) (X (productRight n n j) - X (productLeft n n j)) = _
      rw [(MvPolynomial.eval x).map_sub,MvPolynomial.eval_X,MvPolynomial.eval_X]
    rw [heval,← hL]
    change v (x (productRight n n j) - x (productLeft n n j)) < RVCalc.vrv v (u (productLeft n n j))
    rw [← rvFibre_value v hx (productLeft n n j)]
    exact h
  have hParts := relativeDiagonalPolynomial_partials (K := K) j
  refine ⟨hPG,hPR,?_,?_⟩
  · intro h
    have hRatio : α / γ (productRight n n j) = 1 := by rw [hR,div_self hα]
    have h' : v ((pderiv (productRight n n j) P).eval a) < (1 : G) := hRatio ▸ h a ha
    rw [hParts.1] at h'
    rw [(MvPolynomial.eval a).map_one,v.map_one] at h'
    exact (lt_irrefl (1 : G)) h'
  · intro h
    have hRatio : α / γ (productLeft n n j) = 1 := by rw [hL,div_self hα]
    have h' : v ((pderiv (productLeft n n j) P).eval a) < (1 : G) := hRatio ▸ h a ha
    rw [hParts.2] at h'
    rw [(MvPolynomial.eval a).map_neg,(MvPolynomial.eval a).map_one,v.map_neg,v.map_one] at h'
    exact (lt_irrefl (1 : G)) h'

end DiamondIntegral.Section6
