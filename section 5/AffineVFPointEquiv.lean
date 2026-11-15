import «section 5».AffineVFNativePoints
import «section 5».ComplexAffineCoordinates

/-! Actual ambient-field points of every affine variety are identified
with the native VF object cut out by its original complex equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open DiamondIntegral.Section3
local instance affinePointSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance affinePointSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))

def nativeAffineCoordinateEquiv {n : ℕ} (s : Finset (MvPolynomial (Fin n) ℂ)) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    {x : Fin n → VFType (M := N) | ∀ p ∈ s,MvPolynomial.aeval x p = 0} ≃
      (nativeAffineVFObject e G hB hc s).domain := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact {
    toFun x := ⟨(x.val,Fin.elim0),(nativeAffineVFObject_mem e G hB hc s _).mpr (by
      intro p hp
      exact x.property p hp)⟩
    invFun q := ⟨q.val.1,by
      intro p hp
      exact (nativeAffineVFObject_mem e G hB hc s q.val).mp q.property p hp⟩
    left_inv x := Subtype.ext rfl
    right_inv q := by
      apply Subtype.ext
      change ((q.val.1,Fin.elim0) : Section2.Mixed N n 0) = q.val
      have ht : (Fin.elim0 : Fin 0 → CanonicalRV.RVSort N) = q.val.2 := by
        funext i
        exact i.elim0
      exact congrArg (fun r : Fin 0 → CanonicalRV.RVSort N => (q.val.1,r)) ht }

def nativeAffineAlgebraPointEquiv {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (P : FiniteAffineAlgebraPresentation A) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    (A →ₐ[ℂ] VFType (M := N)) ≃ (nativeAffineVFObject e G hB hc P.equations).domain := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact (finiteAffinePointEquiv P).trans (nativeAffineCoordinateEquiv e G hB hc P.equations)

attribute [local instance] ComplexVariety.coordinateAlgebra

def nativeAffineVarietyPointEquiv (X : ComplexVariety) [IsAffine X.scheme]
    (P : FiniteAffineAlgebraPresentation Γ(X.scheme, ⊤)) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    X.Point (K := VFType (M := N)) ≃ (nativeAffineVFObject e G hB hc P.equations).domain := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact X.affinePointEquiv.trans (nativeAffineAlgebraPointEquiv e G hB hc P)

end DiamondIntegral.Section5.PuiseuxOriginal
