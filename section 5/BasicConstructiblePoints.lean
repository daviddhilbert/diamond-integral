import «section 5».BasicConstructibleSchemes

/-! Complex points of the reduced basic constructible scheme are
exactly the original complex algebra points satisfying its equations
and inequation. Both directions and both compositions are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem basicPointIdeal_le_ker (D : PrimeSpectrum.BasicConstructibleSetData A)
    (ψ : A →ₐ[ℂ] ℂ) (hψ : complexAlgebraPoint ψ ∈ D.toSet) :
    basicConstructibleIdeal D ≤ RingHom.ker ψ.toRingHom := by
  have hspan : Ideal.span (Set.range D.g) ≤ RingHom.ker ψ.toRingHom :=
    Ideal.span_le.mpr (fun a ha => hψ.1 ha)
  exact (Ideal.radical_mono hspan).trans_eq
    (RingHom.ker_isPrime ψ.toRingHom).isRadical.radical

def basicConstructiblePointLift (D : PrimeSpectrum.BasicConstructibleSetData A)
    (ψ : A →ₐ[ℂ] ℂ) (hψ : complexAlgebraPoint ψ ∈ D.toSet) :
    BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f)
    (f := Ideal.Quotient.liftₐ _ ψ (basicPointIdeal_le_ker D ψ hψ))
    (isUnit_iff_ne_zero.mpr (by
      simpa [PrimeSpectrum.mem_zeroLocus, complexAlgebraPoint, RingHom.mem_ker] using hψ.2))

theorem basicConstructiblePointLift_coordinateMap
    (D : PrimeSpectrum.BasicConstructibleSetData A)
    (ψ : A →ₐ[ℂ] ℂ) (hψ : complexAlgebraPoint ψ ∈ D.toSet) :
    (basicConstructiblePointLift D ψ hψ).comp (basicConstructibleCoordinateMap D) = ψ := by
  ext a
  simp only [AlgHom.comp_apply, basicConstructibleCoordinateMap,
    IsScalarTower.toAlgHom_apply, basicConstructiblePointLift,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    Ideal.Quotient.liftₐ_apply]
  rfl

theorem basicConstructiblePoint_ext (D : PrimeSpectrum.BasicConstructibleSetData A)
    (φ ψ : BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ)
    (he : φ.comp (basicConstructibleCoordinateMap D) = ψ.comp (basicConstructibleCoordinateMap D)) :
    φ = ψ := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (basicConstructibleIdeal D) D.f))
  ext a
  exact AlgHom.congr_fun he a

def basicConstructiblePointEquiv (D : PrimeSpectrum.BasicConstructibleSetData A) :
    (BasicConstructibleCoordinateRing D →ₐ[ℂ] ℂ) ≃
      {ψ : A →ₐ[ℂ] ℂ | complexAlgebraPoint ψ ∈ D.toSet} where
  toFun φ := ⟨φ.comp (basicConstructibleCoordinateMap D), basicConstructiblePoint_mem D φ⟩
  invFun ψ := basicConstructiblePointLift D ψ.val ψ.property
  left_inv φ := basicConstructiblePoint_ext D _ _
    (basicConstructiblePointLift_coordinateMap D _ (basicConstructiblePoint_mem D φ))
  right_inv ψ := Subtype.ext (basicConstructiblePointLift_coordinateMap D ψ.val ψ.property)

end DiamondIntegral.Section5
