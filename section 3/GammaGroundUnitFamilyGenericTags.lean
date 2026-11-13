import «section 3».GammaGroundFamilyBranchMaps
import «section 3».GammaGroundGenericDomainPartitions
import «section 3».GammaGroundRVGenericTupleContraction
import «section 3».GammaGroundGammaSinglePiece
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Keep every finite tag and every full nonzero RV value preimage. -/
def GammaGroundGammaObject.unitFamily (A : GammaGroundGammaObject hc B n) :
    GammaGroundFiniteFamily hc B (rawRVUnitSpace (M := M) n) :=
  ⟨A.tags,fun i => gammaGroundRVUnitGammaPreimage (A.piece i)⟩

/-- On each source value fibre, exactly one actual output tag receives
the residue generic. Its locus is definable over the original ground. -/
theorem gammaGroundUnitFamily_generic_tags {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyMap A.unitFamily D.unitFamily) (i : Fin A.tags) :
    (∀ j, (gammaGroundRVGenericValueImage hs h00 B hsmall (F.branchSource i j)).carrier ⊆ (A.piece i).carrier) ∧
    ∀ γ : A.piece i, ∃! j, γ.val ∈
      (gammaGroundRVGenericValueImage hs h00 B hsmall (F.branchSource i j)).carrier := by
  obtain ⟨hsub,hpart⟩ := gammaGroundRVGenericValueImage_partition hs h00 B hsmall hκ (A.piece i)
    (fun j => F.branchSource i j) (fun j => F.branchSource_subset i j)
    (fun u => F.branchSource_partition i u)
  exact ⟨hsub,fun γ => hpart γ.val γ.property⟩

/-- Forgetting the finite target tag still gives one interpreted generic
value tuple on each whole source piece. -/
theorem gammaGroundUnitFamily_generic_values {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyMap A.unitFamily D.unitFamily) (i : Fin A.tags) :
    ∃ h : GammaGroundMap (A.piece i)
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))),
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        (((GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp
          (F.valueMap i)).equalizer (h.comp (gammaGroundFullPreimageValueMap (A.piece i))))).carrier =
        (A.piece i).carrier :=
  gammaGroundRVGeneric_tuple_contraction hκ hs h00 hsmall hγsmall (A.piece i)
    ((GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp (F.valueMap i))

end DiamondIntegral.Section3
