import «section 3».GammaGroundNameReduction
import «section 3».NamedRVCategories

/-! RV and RES categories over all actual Gamma parameters of the
fixed ground base. Every individual object has a finite name support. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundRVObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  arity : ℕ
  domain : GammaGroundDefSet hc ground (rawRVSpace (M := M) arity)
  volume : GammaGroundMap domain (GammaGroundDefSet.univ hc ground (rawRVSpace k))
  finite : volume.FiniteFibres
  nonzero : ∀ a : domain, ∀ i, ((volume a).val i).val ≠ iRVZero

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

instance gammaGroundRVObjectGroupoid : Groupoid (GammaGroundRVObject hc ground k) where
  Hom U V := GammaGroundBijection U.domain V.domain
  id U := GammaGroundBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  inv_comp f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.map.apply_inverse f.bijective a
  comp_inv f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.map.inverse_apply f.bijective a

def GammaGroundRVObject.ofReal (U : RVObject (M := M) ground.real k) : GammaGroundRVObject hc ground k where
  arity := U.arity
  domain := GammaGroundDefSet.ofReal U.domain
  volume := GammaGroundMap.ofReal U.volume
  finite := U.finite
  nonzero := U.nonzero

def GammaGroundRVObject.ofNamed {P : Space LRV M} {p : P.Carrier}
    (U : NamedRVObject P p ground.real k) (hp : GammaGroundDefinable hc ground P {p}) : GammaGroundRVObject hc ground k where
  arity := U.arity
  domain := GammaGroundDefSet.ofNamed U.domain hp
  volume := GammaGroundMap.ofNamed U.volume hp
  finite := U.finite
  nonzero := U.nonzero

def gammaGroundResProperty : ObjectProperty (GammaGroundRVObject hc ground k) :=
  fun U => ((fun t i => Values.vrv (t i)) '' U.domain.carrier).Finite

abbrev GammaGroundRESObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  (gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).FullSubcategory

theorem GammaGroundRVObject.finiteSupport (U : GammaGroundRVObject hc ground k) :
    ∃ n, ∃ γ : Fin n → Values.Gamma (M := M), ∃ hγ : ∀ i, γ i ∈ ground.gamma,
      ∃ V : NamedRVObject ((volumeGammaSpace hc).power (Fin n)) γ ground.real k,
        GammaGroundRVObject.ofNamed V (GammaGroundDefinable.gammaTuple_singleton γ hγ) = U := by
  obtain ⟨n, γ, hγ, hD⟩ := U.domain.definable
  obtain ⟨m, δ, hδ, hV⟩ := U.volume.graph_definable
  let θ := Fin.append γ δ
  have hθ : ∀ i, θ i ∈ ground.gamma := gammaGroundNames_append hγ hδ
  have hD' := hD.changeName (universalPowerProjection (volumeGammaSpace hc) ground.real (Fin.castAdd m))
    (gammaPowerProjection_left_append ground.real n m γ δ)
  have hV' := hV.changeName (universalPowerProjection (volumeGammaSpace hc) ground.real (Fin.natAdd n))
    (gammaPowerProjection_right_append ground.real n m γ δ)
  let D : NamedDefSet ((volumeGammaSpace hc).power (Fin (n + m))) θ (rawRVSpace (M := M) U.arity) ground.real :=
    ⟨U.domain.carrier, hD'⟩
  let f : NamedMap D (NamedDefSet.univ ((volumeGammaSpace hc).power (Fin (n + m))) θ (rawRVSpace k) ground.real) :=
    ⟨U.volume.toFun, hV'⟩
  let V : NamedRVObject ((volumeGammaSpace hc).power (Fin (n + m))) θ ground.real k :=
    ⟨U.arity, D, f, U.finite, U.nonzero⟩
  exact ⟨n + m, θ, hθ, V, rfl⟩

theorem GammaGroundRVObject.degree_zero_finite (U : GammaGroundRVObject hc ground 0) : U.domain.carrier.Finite := by
  obtain ⟨n, γ, hγ, V, rfl⟩ := U.finiteSupport
  exact V.degree_zero_finite

theorem GammaGroundRVObject.degree_zero_res (U : GammaGroundRVObject hc ground 0) : gammaGroundResProperty U :=
  U.degree_zero_finite.image _

end DiamondIntegral.Section3
