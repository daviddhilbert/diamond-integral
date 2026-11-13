import «section 3».GammaGroundRVScissors
import «section 3».VFCategories
import «section 3».NamedVFCategories

/-! VF objects and genuine bijections over fixed imaginary names use
the actual section 2 interior dimension and literal finite RV fibres. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]

structure GammaGroundVFObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  vfArity : ℕ
  rvArity : ℕ
  domain : GammaGroundDefSet hc ground (rawMixedSpace (M := M) vfArity rvArity)
  dimension : Section2.vfDimension domain.carrier ≤ (k : WithBot ℕ)
  finite : ∀ a : Fin vfArity → Section2.VF M, {t | (a, t) ∈ domain.carrier}.Finite

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

instance gammaGroundVFObjectGroupoid : Groupoid (GammaGroundVFObject hc ground k) where
  Hom U V := GammaGroundBijection U.domain V.domain
  id U := GammaGroundBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  inv_comp f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.map.apply_inverse f.bijective a
  comp_inv f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.map.inverse_apply f.bijective a

def GammaGroundVFObject.raise (U : GammaGroundVFObject hc ground k) {l : ℕ} (hkl : k ≤ l) : GammaGroundVFObject hc ground l :=
  {U with dimension := U.dimension.trans (by exact_mod_cast hkl)}

def GammaGroundVFObject.restrict (U : GammaGroundVFObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hX : X.carrier ⊆ U.domain.carrier) : GammaGroundVFObject hc ground k where
  vfArity := U.vfArity
  rvArity := U.rvArity
  domain := X
  dimension := (vf_dimension_mono hX).trans U.dimension
  finite a := (U.finite a).subset (fun _ hx => hX hx)

def GammaGroundVFObject.ofReal (U : VFObject (M := M) ground.real k) : GammaGroundVFObject hc ground k :=
  ⟨U.vfArity, U.rvArity, GammaGroundDefSet.ofReal U.domain, U.dimension, U.finite⟩


def GammaGroundVFObject.ofNamed {P : Space LRV M} {p : P.Carrier}
    (U : NamedVFObject P p ground.real k) (hp : GammaGroundDefinable hc ground P {p}) : GammaGroundVFObject hc ground k :=
  ⟨U.vfArity, U.rvArity, GammaGroundDefSet.ofNamed U.domain hp, U.dimension, U.finite⟩

theorem GammaGroundVFObject.finiteSupport (U : GammaGroundVFObject hc ground k) :
    ∃ n, ∃ γ : Fin n → Values.Gamma (M := M), ∃ hγ : ∀ i, γ i ∈ ground.gamma,
      ∃ V : NamedVFObject ((volumeGammaSpace hc).power (Fin n)) γ ground.real k,
        GammaGroundVFObject.ofNamed V (GammaGroundDefinable.gammaTuple_singleton γ hγ) = U := by
  obtain ⟨n, γ, hγ, hD⟩ := U.domain.definable
  let D : NamedDefSet ((volumeGammaSpace hc).power (Fin n)) γ (rawMixedSpace (M := M) U.vfArity U.rvArity) ground.real :=
    ⟨U.domain.carrier, hD⟩
  exact ⟨n, γ, hγ, ⟨U.vfArity, U.rvArity, D, U.dimension, U.finite⟩, rfl⟩

end DiamondIntegral.Section3
