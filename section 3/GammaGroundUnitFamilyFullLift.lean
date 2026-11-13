import «section 3».GammaGroundFamilyBranchImages
import «section 3».GammaGroundFamilyPartitionBijections
import «section 3».GammaGroundFamilyPieceValueMaps
import «section 3».GammaGroundSingleFullLift
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- Pointwise old-ground unimodular formulas on an interpreted Gamma
family bijection yield an actual full RV family lift. Source and target
branch partitions keep all finite tags. -/
theorem gammaGroundUnitFamily_affine_full_lift {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A D : GammaGroundGammaObject hc B n) (H : GammaGroundFamilyBijection A D)
    (hpoint : ∀ γ : A.Carrier, ∃ F : OriginalGroundAffineRVFormula hc B n,
      (H.equiv γ).2.val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.2.val) :
    ∃ L : GammaGroundFamilyBijection A.unitFamily D.unitFamily,
      ∀ u, D.unitValueFamilyMap.toFun (L.equiv u) = H.equiv (A.unitValueFamilyMap.toFun u) := by
  let R := fun i j => H.toFamilyMap.branchSource i j
  let S := fun i j => (H.toFamilyMap.branchMap i j).image
  let h := fun i j => H.branchBijection i j
  have hex (i : Fin A.tags) (j : Fin D.tags) :
      ∃ L : GammaGroundBijection (gammaGroundRVUnitGammaPreimage (R i j)) (gammaGroundRVUnitGammaPreimage (S i j)),
        ∀ u, gammaGroundFullPreimageValueMap (S i j) (L.map u) =
          (h i j).map (gammaGroundFullPreimageValueMap (R i j) u) := by
    apply gammaGroundAffine_full_lift hκ hs hsmall hγsmall (R i j) (S i j) (h i j)
    intro γ
    let a : A.piece i := ⟨γ.val,H.toFamilyMap.branchSource_subset i j γ.property⟩
    obtain ⟨F,hF⟩ := hpoint ⟨i,a⟩
    exact ⟨F,hF⟩
  choose L hL using hex
  let U := fun i j => gammaGroundRVUnitGammaPreimage (R i j)
  let V := fun i j => gammaGroundRVUnitGammaPreimage (S i j)
  have hU : ∀ i j, (U i j).carrier ⊆ (A.unitFamily.piece i).carrier :=
    fun i j _ hu => H.toFamilyMap.branchSource_subset i j hu
  have hV : ∀ i j, (V i j).carrier ⊆ (D.unitFamily.piece j).carrier :=
    fun i j _ hv => H.branchImage_subset i j hv
  have hUc : ∀ i (u : A.unitFamily.piece i), ∃! j, u.val ∈ (U i j).carrier :=
    fun i u => H.toFamilyMap.branchSource_partition i (gammaGroundFullPreimageValueMap (A.piece i) u)
  have hVc : ∀ j (v : D.unitFamily.piece j), ∃! i, v.val ∈ (V i j).carrier :=
    fun j v => H.branchImage_partition j (gammaGroundFullPreimageValueMap (D.piece j) v)
  obtain ⟨T,hT⟩ := gammaGroundFamilyBijection_of_partitions A.unitFamily D.unitFamily U V hU hV hUc hVc L
  refine ⟨T,?_⟩
  rintro ⟨i,u⟩
  obtain ⟨j,huj,_⟩ := hUc i u
  have ht := hT i j u huj
  let pu : U i j := ⟨u.val,huj⟩
  have hΓtag : (H.equiv ⟨i,gammaGroundFullPreimageValueMap (A.piece i) u⟩).1 = j :=
    (H.toFamilyMap.mem_branchSource_iff_tag i j (gammaGroundFullPreimageValueMap (A.piece i) u)).mp huj
  apply gammaGroundFamilyCarrier_ext D (ht.1.trans hΓtag.symm)
  change rvUnitTupleValues (T.equiv ⟨i,u⟩).2.val =
    (H.equiv ⟨i,gammaGroundFullPreimageValueMap (A.piece i) u⟩).2.val
  have hv := congrArg Subtype.val (hL i j pu)
  exact (congrArg rvUnitTupleValues ht.2).trans hv

end DiamondIntegral.Section3
