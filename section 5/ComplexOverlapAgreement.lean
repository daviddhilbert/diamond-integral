import «section 5».OverlapAlgebras
import «section 5».ComplexPointNilpotence

/-! Agreement on compatible complex points forces agreement on every
reduced overlap algebra. This is the compatibility needed to glue the
regular maps carried by the finitely many graph pieces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {S T A B : Type} [CommRing S] [CommRing T] [CommRing A] [CommRing B]
variable [Algebra ℂ S] [Algebra ℂ T] [Algebra ℂ A] [Algebra ℂ B]
variable [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B]

theorem complex_overlap_agreement (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B)
    (a : T →ₐ[ℂ] A) (b : T →ₐ[ℂ] B)
    (hc : ∀ (φ : A →ₐ[ℂ] ℂ) (ψ : B →ₐ[ℂ] ℂ), φ.comp f = ψ.comp g → φ.comp a = ψ.comp b)
    {R : Type} [CommRing R] [Algebra ℂ R] [IsReduced R]
    (u : A →ₐ[ℂ] R) (v : B →ₐ[ℂ] R) (he : u.comp f = v.comp g) : u.comp a = v.comp b := by
  letI := overlapAlgebra_finiteType f g
  have hpoint (φ : OverlapAlgebra f g →ₐ[ℂ] ℂ) :
      φ.comp ((overlapLeft f g).comp a) = φ.comp ((overlapRight f g).comp b) := by
    have hi : (φ.comp (overlapLeft f g)).comp f = (φ.comp (overlapRight f g)).comp g := by
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, overlap_commutes]
    simpa only [AlgHom.comp_assoc] using hc (φ.comp (overlapLeft f g)) (φ.comp (overlapRight f g)) hi
  let r := overlapLift f g u v he
  have hL : r.comp (overlapLeft f g) = u := by
    ext x
    exact overlapLift_left f g u v he x
  have hR : r.comp (overlapRight f g) = v := by
    ext x
    exact overlapLift_right f g u v he x
  have h := complex_points_maps_agree_after_reduction _ _ hpoint r
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hL, hR] at h
  exact h

theorem complex_overlap_ring_agreement (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B)
    (a : T →ₐ[ℂ] A) (b : T →ₐ[ℂ] B)
    (hc : ∀ (φ : A →ₐ[ℂ] ℂ) (ψ : B →ₐ[ℂ] ℂ), φ.comp f = ψ.comp g → φ.comp a = ψ.comp b)
    {R : Type} [CommRing R] [IsReduced R] (u : A →+* R) (v : B →+* R)
    (he : u.comp f.toRingHom = v.comp g.toRingHom) : u.comp a.toRingHom = v.comp b.toRingHom := by
  letI : Algebra ℂ R := (u.comp (algebraMap ℂ A)).toAlgebra
  let U : A →ₐ[ℂ] R := { u with commutes' := fun _ => rfl }
  have hv (c : ℂ) : v (algebraMap ℂ B c) = algebraMap ℂ R c := by
    have h := RingHom.congr_fun he (algebraMap ℂ S c)
    change u (f (algebraMap ℂ S c)) = v (g (algebraMap ℂ S c)) at h
    rw [f.commutes, g.commutes] at h
    exact h.symm
  let V : B →ₐ[ℂ] R := { v with commutes' := hv }
  have hUV : U.comp f = V.comp g := by
    apply AlgHom.toRingHom_injective
    exact he
  have h := complex_overlap_agreement f g a b hc U V hUV
  exact congrArg AlgHom.toRingHom h

end DiamondIntegral.Section5
