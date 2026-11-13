import «section 3».GammaGroundVFCategories

/-! Unbounded finite-RV-fibre VF objects over the complete Gamma ground.
Every such object occurs in the actual dimension filtration. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundFiniteVFObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) where
  vfArity : ℕ
  rvArity : ℕ
  domain : GammaGroundDefSet hc ground (rawMixedSpace (M := M) vfArity rvArity)
  finite : ∀ a : Fin vfArity → Section2.VF M, {t | (a, t) ∈ domain.carrier}.Finite

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

instance gammaGroundFiniteVFObjectGroupoid : Groupoid (GammaGroundFiniteVFObject hc ground) where
  Hom U V := GammaGroundBijection U.domain V.domain
  id U := GammaGroundBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  inv_comp f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.map.apply_inverse f.bijective a
  comp_inv f := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.map.inverse_apply f.bijective a

def GammaGroundFiniteVFObject.ofBound [TopologicalSpace (Section2.VF M)] {k : ℕ}
    (U : GammaGroundVFObject hc ground k) : GammaGroundFiniteVFObject hc ground :=
  ⟨U.vfArity, U.rvArity, U.domain, U.finite⟩

def GammaGroundFiniteVFObject.toBound [TopologicalSpace (Section2.VF M)]
    (U : GammaGroundFiniteVFObject hc ground) : GammaGroundVFObject hc ground U.vfArity :=
  ⟨U.vfArity, U.rvArity, U.domain, vf_dimension_le_arity _, U.finite⟩

@[simp] theorem GammaGroundFiniteVFObject.of_toBound [TopologicalSpace (Section2.VF M)]
    (U : GammaGroundFiniteVFObject hc ground) : GammaGroundFiniteVFObject.ofBound U.toBound = U := rfl

def GammaGroundFiniteVFObject.restrict (U : GammaGroundFiniteVFObject hc ground)
    (X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hX : X.carrier ⊆ U.domain.carrier) : GammaGroundFiniteVFObject hc ground :=
  ⟨U.vfArity, U.rvArity, X, fun a => (U.finite a).subset (fun _ hx => hX hx)⟩

def GammaGroundFiniteVFObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundFiniteVFObject hc ground where
  vfArity := 0
  rvArity := 0
  domain := GammaGroundDefSet.empty hc ground (rawMixedSpace 0 0)
  finite _ := Set.finite_empty

def GammaGroundFiniteVFObject.unit (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundFiniteVFObject hc ground where
  vfArity := 0
  rvArity := 0
  domain := GammaGroundDefSet.univ hc ground (rawMixedSpace 0 0)
  finite _ := Set.Subsingleton.finite (fun x _ y _ => funext (fun i => i.elim0))

end DiamondIntegral.Section3
