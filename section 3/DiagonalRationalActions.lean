import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.FractionRing
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type*} [Field K] {ι : Type*}

def diagonalPolynomialEquiv (a : ι → Kˣ) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.C (a i : K) * MvPolynomial.X i)
    (MvPolynomial.aeval fun i => MvPolynomial.C (((a i)⁻¹ : Kˣ) : K) * MvPolynomial.X i)
    (by apply MvPolynomial.algHom_ext; intro i; simp [← mul_assoc, ← MvPolynomial.C_mul])
    (by apply MvPolynomial.algHom_ext; intro i; simp [← mul_assoc, ← MvPolynomial.C_mul])

@[simp] theorem diagonalPolynomialEquiv_X (a : ι → Kˣ) (i : ι) :
    diagonalPolynomialEquiv a (MvPolynomial.X i) =
      MvPolynomial.C (a i : K) * MvPolynomial.X i := by
  simp [diagonalPolynomialEquiv]

abbrev TorusRationalFunction (K : Type*) [Field K] (n : ℕ) :=
  FractionRing (MvPolynomial (Fin n) K)

def torusRationalVariable (K : Type*) [Field K] {n : ℕ} (i : Fin n) :
    TorusRationalFunction K n :=
  algebraMap (MvPolynomial (Fin n) K) (TorusRationalFunction K n) (MvPolynomial.X i)

def diagonalRationalEquiv {n : ℕ} (a : Fin n → Kˣ) :
    TorusRationalFunction K n ≃ₐ[K] TorusRationalFunction K n :=
  IsFractionRing.algEquivOfAlgEquiv (diagonalPolynomialEquiv a)

@[simp] theorem diagonalRationalEquiv_variable {n : ℕ}
    (a : Fin n → Kˣ) (i : Fin n) :
    diagonalRationalEquiv a (torusRationalVariable K i) =
      algebraMap K (TorusRationalFunction K n) (a i : K) * torusRationalVariable K i := by
  simp [diagonalRationalEquiv,torusRationalVariable,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (TorusRationalFunction K n) (a i : K)).symm

theorem torusRationalVariable_ne_zero (K : Type*) [Field K] {n : ℕ} (i : Fin n) :
    torusRationalVariable K i ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := K) i
  apply IsFractionRing.injective (MvPolynomial (Fin n) K) (TorusRationalFunction K n)
  exact h.trans (map_zero _).symm

@[simp] theorem diagonalRationalEquiv_one {n : ℕ} :
    diagonalRationalEquiv (fun _ : Fin n => (1 : Kˣ)) = AlgEquiv.refl := by
  apply AlgEquiv.toRingEquiv_injective
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) K)
  intro p
  change diagonalRationalEquiv (fun _ : Fin n => (1 : Kˣ))
    (algebraMap _ (TorusRationalFunction K n) p) = algebraMap _ _ p
  have hp : diagonalPolynomialEquiv (fun _ : Fin n => (1 : Kˣ)) = AlgEquiv.refl := by
    have he : (diagonalPolynomialEquiv (fun _ : Fin n => (1 : Kˣ))).toAlgHom =
        AlgHom.id K (MvPolynomial (Fin n) K) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [diagonalPolynomialEquiv]
    exact AlgEquiv.ext (fun p => AlgHom.congr_fun he p)
  simp [diagonalRationalEquiv,IsFractionRing.algEquivOfAlgEquiv_algebraMap,hp]

end DiamondIntegral.Section3
