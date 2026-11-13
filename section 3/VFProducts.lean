import «section 3».VFCategories
import «section 3».VFDimensionComparison
import Section4.VFProducts
import Section4.ProductBijections

/-! Actual VF products retain all RV labels and finite RV fibres. Their
dimension bound is transported through the proved section 2 comparison. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [TopologicalSpace (Section2.VF M)] {S : Set M} {k l : ℕ}

def VFObject.toCompanionAll (U : VFObject (M := M) S k) : VFAllObject S :=
  ⟨(U.vfArity, U.rvArity), U.domain⟩

def VFObject.unit (S : Set M) : VFObject (M := M) S 0 where
  vfArity := 0
  rvArity := 0
  domain := DefSet.univ (rawMixedSpace 0 0) S
  dimension := vf_dimension_le_arity _
  finite a := by
    change Set.Finite {t : Fin 0 → Section2.RVInfinity M |
      (a, t) ∈ (DefSet.univ (rawMixedSpace 0 0) S).carrier}
    exact Set.Subsingleton.finite (fun x _ y _ => funext (fun i => i.elim0))

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {k l : ℕ}

def VFObject.product (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : VFObject (M := M) S k) (V : VFObject (M := M) S l) : VFObject S (k + l) where
  vfArity := U.vfArity + V.vfArity
  rvArity := U.rvArity + V.rvArity
  domain := mixedProductDomain U.domain V.domain
  dimension := (vfDimension_le_iff_companion hc hs hS hv _ _).mpr
    ((vfDim_mixed_product_le (rawRVSpace 1) U.domain V.domain).trans
      (Nat.add_le_add ((vfDimension_le_iff_companion hc hs hS hv _ _).mp U.dimension)
        ((vfDimension_le_iff_companion hc hs hS hv _ _).mp V.dimension)))
  finite := finiteRVFibres_product (U := U.toCompanionAll) (V := V.toCompanionAll) U.finite V.finite

def vfProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U U' : VFObject (M := M) S k} {V V' : VFObject (M := M) S l}
    (f : DefinableBijection U.domain U'.domain) (g : DefinableBijection V.domain V'.domain) :
    DefinableBijection (U.product hc hs hS hv V).domain (U'.product hc hs hS hv V').domain where
  map := vfAllProductHom (U := U.toCompanionAll) (U' := U'.toCompanionAll)
    (V := V.toCompanionAll) (V' := V'.toCompanionAll) f.map g.map
  bijective := (mixedPackToImage_bijective U'.domain V'.domain).comp
    ((Map.prodMap_bijective f.map g.map f.bijective g.bijective).comp
      (Equiv.ofBijective (mixedPack U.domain V.domain).toImage
        (mixedPackToImage_bijective U.domain V.domain)).symm.bijective)

end DiamondIntegral.Section3
