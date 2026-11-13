import «section 3».GammaGroundFamilyBranchMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {A : GammaGroundFiniteFamily hc B P} {D : GammaGroundFiniteFamily hc B Q}

/-- Every branch of a family bijection is an actual same-ground
bijection to its definable image. -/
def GammaGroundFamilyBijection.branchBijection (F : GammaGroundFamilyBijection A D)
    (i : Fin A.tags) (j : Fin D.tags) :
    GammaGroundBijection (F.toFamilyMap.branchSource i j) (F.toFamilyMap.branchMap i j).image :=
  ⟨(F.toFamilyMap.branchMap i j).toImage,
    (F.toFamilyMap.branchMap i j).toImage_bijective
      (F.toFamilyMap.branchMap_injective F.equiv.injective i j)⟩

theorem GammaGroundFamilyBijection.branchImage_subset (F : GammaGroundFamilyBijection A D)
    (i : Fin A.tags) (j : Fin D.tags) :
    (F.toFamilyMap.branchMap i j).image.carrier ⊆ (D.piece j).carrier := by
  rintro x ⟨a,rfl⟩
  exact (F.toFamilyMap.branchMap i j a).property

/-- The images of the incoming branches form a genuine finite disjoint
partition of each target piece. -/
theorem GammaGroundFamilyBijection.branchImage_partition (F : GammaGroundFamilyBijection A D)
    (j : Fin D.tags) (b : D.piece j) :
    ∃! i, b.val ∈ (F.toFamilyMap.branchMap i j).image.carrier := by
  let a := F.equiv.symm ⟨j,b⟩
  have hFab : F.equiv a = ⟨j,b⟩ := F.equiv.apply_symm_apply _
  obtain ⟨ha,hab⟩ := F.toFamilyMap.branchMap_point a.1 j a.2 b hFab
  refine ⟨a.1,⟨⟨a.2.val,ha⟩,congrArg Subtype.val hab⟩,?_⟩
  rintro i ⟨u,hu⟩
  obtain ⟨a',ha',b',hFab'⟩ := (F.toFamilyMap.mem_branchSource i j u.val).mp u.property
  obtain ⟨ha'',hab'⟩ := F.toFamilyMap.branchMap_point i j a' b' hFab'
  have hau : (⟨a'.val,ha''⟩ : F.toFamilyMap.branchSource i j) = u := Subtype.ext ha'
  have hb'b : b' = b := Subtype.ext
    ((congrArg Subtype.val hab').symm.trans ((congrArg (fun t => (F.toFamilyMap.branchMap i j t).val) hau).trans hu))
  have hsame : (⟨i,a'⟩ : A.Carrier) = a := F.equiv.injective
    (hFab'.trans ((congrArg (Sigma.mk j) hb'b).trans hFab.symm))
  exact congrArg Sigma.fst hsame

end DiamondIntegral.Section3
