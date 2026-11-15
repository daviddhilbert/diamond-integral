import «section 5».AffinePointFiniteEquations
import «section 5».VFPolynomialNativeDomains
import «section 5».PuiseuxAmbientFields

/-! Finite affine algebra equations, after the actual complex coefficient
embedding, define native VF objects with exactly the original parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
local instance affineNativeSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance affineNativeSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable {n : ℕ}

def ambientPolynomialEquations (s : Finset (MvPolynomial (Fin n) ℂ)) :
    Finset (MvPolynomial (Fin n) (VFType (M := N))) := s.image (MvPolynomial.map (ambientComplexFieldHom e))

include hB in
theorem ambientPolynomialEquations_coefficients (s : Finset (MvPolynomial (Fin n) ℂ)) :
    ∀ p ∈ ambientPolynomialEquations e s,∀ d,(p.coeff d).val ∈ G.base.real := by
  intro p hp d
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  rw [MvPolynomial.coeff_map]
  exact ambientComplexFieldHom_base_mem e G hB (q.coeff d)

def nativeAffineVFObject (hc : CanonicalStructure.IsCanonical (M := N))
    (s : Finset (MvPolynomial (Fin n) ℂ)) : GammaGroundFiniteVFObject hc G.base :=
  nativeVFPolynomialObject hc (ambientPolynomialEquations e s) (ambientPolynomialEquations_coefficients e G hB s)

theorem nativeAffineVFObject_mem (hc : CanonicalStructure.IsCanonical (M := N))
    (s : Finset (MvPolynomial (Fin n) ℂ)) (q : Section2.Mixed N n 0) :
    q ∈ (nativeAffineVFObject e G hB hc s).domain.carrier ↔
      ∀ p ∈ s,MvPolynomial.eval₂ (ambientComplexFieldHom e) q.1 p = 0 := by
  rw [show (nativeAffineVFObject e G hB hc s).domain =
    nativeVFPolynomialDomain hc (ambientPolynomialEquations e s) (ambientPolynomialEquations_coefficients e G hB s) from rfl]
  rw [nativeVFPolynomialDomain_mem]
  constructor
  · intro h p hp
    exact (MvPolynomial.eval_map (ambientComplexFieldHom e) q.1 p).symm.trans
      (h _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  · intro h p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    exact (MvPolynomial.eval_map (ambientComplexFieldHom e) q.1 r).trans (h r hr)

end DiamondIntegral.Section5.PuiseuxOriginal
