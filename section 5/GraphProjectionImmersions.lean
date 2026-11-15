import «section 5».PrincipalRationalMaps
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! A rational graph projection is an actual immersion whenever the
original graph inclusion is an immersion. The rational section and its
full algebra square are constructed explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {A : Type} [CommRing A] [Algebra ℂ A]

def polynomialGraphMap {n m : ℕ}
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (g : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A) :
    MvPolynomial (Fin n ⊕ Fin m) ℂ →ₐ[ℂ] A :=
  MvPolynomial.aeval (Sum.elim (fun i => f (MvPolynomial.X i)) (fun j => g (MvPolynomial.X j)))

def principalGraphSection {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n ⊕ Fin m) ℂ →ₐ[ℂ] Localization.Away q :=
  MvPolynomial.aeval (Sum.elim
    (fun i => algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away q) (MvPolynomial.X i))
    (fun j => algebraMap _ _ (p j) * IsLocalization.Away.invSelf q))

def graphLocalizationLift {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (q : MvPolynomial (Fin n) ℂ) (hq : IsUnit (f q)) : Localization.Away q →ₐ[ℂ] A :=
  IsLocalization.Away.liftAlgHom q hq

theorem principalGraphSection_square {n m : ℕ}
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (g : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hq : IsUnit (f q)) (hr : ∀ j, g (MvPolynomial.X j) * f q = f (p j)) :
    (graphLocalizationLift f q hq).comp (principalGraphSection p q) = polynomialGraphMap f g := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
    simp only [AlgHom.comp_apply, principalGraphSection, polynomialGraphMap, MvPolynomial.aeval_X,
      Sum.elim_inl, graphLocalizationLift, IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
    rfl
  | inr j =>
    simp only [AlgHom.comp_apply, principalGraphSection, polynomialGraphMap, MvPolynomial.aeval_X,
      Sum.elim_inr, map_mul, graphLocalizationLift, IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
    have h := congrArg (IsLocalization.Away.lift q (g := f.toRingHom) hq)
      (IsLocalization.Away.mul_invSelf q (S := Localization.Away q))
    rw [map_mul, map_one, IsLocalization.Away.lift_eq] at h
    change f q * (IsLocalization.Away.lift q (g := f.toRingHom) hq) (IsLocalization.Away.invSelf q) = 1 at h
    change f (p j) * (IsLocalization.Away.lift q (g := f.toRingHom) hq) (IsLocalization.Away.invSelf q) = g (MvPolynomial.X j)
    rw [← hr j, mul_assoc, h, mul_one]

theorem rational_graph_projection_isImmersion {n m : ℕ}
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (g : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hq : IsUnit (f q)) (hr : ∀ j, g (MvPolynomial.X j) * f q = f (p j))
    (hgraph : IsImmersion (Spec.map (CommRingCat.ofHom (polynomialGraphMap f g).toRingHom))) :
    IsImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  let L := graphLocalizationLift f q hq
  let S := principalGraphSection p q
  have hsquare : Spec.map (CommRingCat.ofHom L.toRingHom) ≫
      Spec.map (CommRingCat.ofHom S.toRingHom) =
      Spec.map (CommRingCat.ofHom (polynomialGraphMap f g).toRingHom) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg
      (fun a : MvPolynomial (Fin n ⊕ Fin m) ℂ →ₐ[ℂ] A => CommRingCat.ofHom a.toRingHom)
      (principalGraphSection_square f g p q hq hr))
  letI : IsImmersion (Spec.map (CommRingCat.ofHom L.toRingHom)) := by
    haveI : IsImmersion (Spec.map (CommRingCat.ofHom L.toRingHom) ≫
        Spec.map (CommRingCat.ofHom S.toRingHom)) := hsquare.symm ▸ hgraph
    exact IsImmersion.of_comp (Spec.map (CommRingCat.ofHom L.toRingHom))
      (Spec.map (CommRingCat.ofHom S.toRingHom))
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away q)))) :=
    IsOpenImmersion.of_isLocalization q
  have he : L.comp (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin n) ℂ) (Localization.Away q)) = f := by
    exact AlgHom.ext (fun a => IsLocalization.Away.lift_eq q (g := f.toRingHom) hq a)
  have he' : Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom L.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away q))) := by
    rw [← Spec.map_comp]
    exact (congrArg Spec.map (congrArg
      (fun a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A => CommRingCat.ofHom a.toRingHom) he)).symm
  rw [he']
  infer_instance

end DiamondIntegral.Section5
