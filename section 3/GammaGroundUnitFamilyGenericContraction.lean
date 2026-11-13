import «section 3».GammaGroundUnitFamilyTagValues
import «section 3».GammaGroundFamilySelectedMaps
import «section 3».GammaGroundFamilyPieceValueMaps
import «section 3».GammaGroundFamilyEqualizers
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- An actual full-preimage family map has a same-ground interpreted
Gamma family map whose complete tagged output agrees on each residue
generic. It is not yet asserted to have a full bijective RV lift. -/
theorem gammaGroundUnitFamily_generic_contraction {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyMap A.unitFamily D.unitFamily) :
    ∃ H : GammaGroundFamilyMap A D, ∀ i,
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        ((D.unitValueFamilyMap.comp F).equalizerPiece (H.comp A.unitValueFamilyMap) i)).carrier =
          (A.piece i).carrier := by
  choose h hh using fun i => gammaGroundUnitFamily_generic_values hκ hs h00 hsmall hγsmall A D F i
  let P := fun i j => gammaGroundRVGenericValueImage hs h00 B hsmall (F.branchSource i j)
  have hcover : ∀ i (γ : A.piece i), ∃! j, γ.val ∈ (P i j).carrier :=
    fun i => (gammaGroundUnitFamily_generic_tags hκ hs h00 hsmall A D F i).2
  have hrange : ∀ i j (γ : A.piece i), γ.val ∈ (P i j).carrier → (h i γ).val ∈ (D.piece j).carrier :=
    fun i j γ => gammaGroundUnitFamily_generic_value_range hκ hs h00 hsmall A D F i (h i) (hh i) j γ
  obtain ⟨H,hTag,hValue⟩ := gammaGroundFamilyMap_of_selected_values A D P hcover h hrange
  let L := D.unitValueFamilyMap.comp F
  let R := H.comp A.unitValueFamilyMap
  let E := fun i => L.equalizerPiece R i
  refine ⟨H,fun i => Set.Subset.antisymm ?_ ?_⟩
  · intro γ hγ
    obtain ⟨u,hu,hval⟩ := gammaGroundRVGenericValueImage_subset_values hs h00 B hsmall (E i) hγ
    have huA : u ∈ (A.unitFamily.piece i).carrier := L.equalizerPiece_subset R i hu
    exact hval ▸ huA
  · intro γ hγ
    let αγ : A.piece i := ⟨γ,hγ⟩
    obtain ⟨j,hj,_⟩ := hcover i αγ
    let w : GammaGroundMap (A.unitFamily.piece i)
        (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
      (GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp (F.valueMap i)
    let EV := w.equalizer ((h i).comp (gammaGroundFullPreimageValueMap (A.piece i)))
    let T : Option Bool → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
      fun t => t.elim (E i) (fun b => if b then F.branchSource i j else EV)
    obtain ⟨u,hu,hT⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ T γ
    apply (hT none).mpr
    obtain ⟨a,ha,hea⟩ := (hT (some false)).mp ((hh i).symm ▸ hγ)
    obtain ⟨a',ha',b,hF⟩ := (F.mem_branchSource i j u).mp ((hT (some true)).mp hj)
    have heaa : a' = a := Subtype.ext (ha'.trans ha.symm)
    subst a'
    have hvγ : gammaGroundFullPreimageValueMap (A.piece i) a = αγ :=
      Subtype.ext ((congrArg rvUnitTupleValues ha).trans hu)
    have hpred : (gammaGroundFullPreimageValueMap (A.piece i) a).val ∈ (P i j).carrier := hvγ.symm ▸ hj
    have heq : L.toFun ⟨i,a⟩ = R.toFun ⟨i,a⟩ := by
      apply gammaGroundFamilyCarrier_ext D
      · change (F.toFun ⟨i,a⟩).1 = (H.toFun ⟨i,gammaGroundFullPreimageValueMap (A.piece i) a⟩).1
        exact (congrArg Sigma.fst hF).trans ((hTag i _ j).mpr hpred).symm
      · change rvUnitTupleValues (F.toFun ⟨i,a⟩).2.val =
          (H.toFun ⟨i,gammaGroundFullPreimageValueMap (A.piece i) a⟩).2.val
        change rvUnitTupleValues (F.toFun ⟨i,a⟩).2.val =
          (h i (gammaGroundFullPreimageValueMap (A.piece i) a)).val at hea
        exact hea.trans (hValue i _).symm
    have haE : a.val ∈ (E i).carrier := (L.mem_equalizerPiece_at R i a).mpr heq
    exact ha ▸ haE

end DiamondIntegral.Section3
