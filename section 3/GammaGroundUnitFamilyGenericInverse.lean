import «section 3».GammaGroundUnitFamilyGenericContraction
import «section 3».RVGenericMapCoefficients
import «section 3».GammaGroundGenericNormalizedTests
import «section 3».GammaGroundRVUnitRawMaps
import «section 3».RVResidueFullFibreCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Generic contraction commutes with the actual inverse of a bijection
of full RV families. The residue generic determines both target tag and
value, and the argument uses the actual partial branch graph. -/
theorem gammaGroundUnitFamily_generic_inverse_at {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyBijection A.unitFamily D.unitFamily)
    (H : GammaGroundFamilyMap A D) (K : GammaGroundFamilyMap D A)
    (hh : ∀ i, (gammaGroundRVGenericValueImage hs h00 B hsmall
      ((D.unitValueFamilyMap.comp F.toFamilyMap).equalizerPiece (H.comp A.unitValueFamilyMap) i)).carrier = (A.piece i).carrier)
    (hk : ∀ j, (gammaGroundRVGenericValueImage hs h00 B hsmall
      ((A.unitValueFamilyMap.comp F.symm.toFamilyMap).equalizerPiece (K.comp D.unitValueFamilyMap) j)).carrier = (D.piece j).carrier)
    (γ : A.Carrier) : K.toFun (H.toFun γ) = γ := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero h00
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let i := γ.1
  let j := (H.toFun γ).1
  let α : A.piece i := γ.2
  let β : D.piece j := (H.toFun γ).2
  let Eh := (D.unitValueFamilyMap.comp F.toFamilyMap).equalizerPiece (H.comp A.unitValueFamilyMap) i
  let Ek := (A.unitValueFamilyMap.comp F.symm.toFamilyMap).equalizerPiece (K.comp D.unitValueFamilyMap) j
  obtain ⟨a,ha⟩ := rvUnitTupleValues_surjective (M := M) n α.val
  obtain ⟨b,hb⟩ := rvUnitTupleValues_surjective (M := M) n β.val
  let V : Bool → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun t => if t then Ek else Eh
  let T := fun t => rvUnitValues '' (V t).carrier
  have hT : ∀ t, DefinableOverBase B (fun _ => .rv) (T t) :=
    fun t => (gammaGroundRVUnit_definable_iff (V t).carrier).mp (V t).definable
  let normalizer : Bool → Fin n → (CanonicalRV.RVSort M)ˣ := fun t => if t then b else a
  let f := F.toFamilyMap.branchMap i j
  let R := rvNormalizedMapRelation f.unitRaw a b
  have hR : ResiduePurity.PureDef R := rvNormalizedMapRelation_pure hκ.le hsmall f.unitRaw a b
  obtain ⟨E,hE,_,hEV,hER⟩ := rvGeneric_family_extra_coefficients hc hκ.le hs h00 B hsmall
    T hT normalizer (List.finRange n) (fun _ : Unit => Fin n ⊕ Fin n) (fun _ => R) (fun _ => hR)
  obtain ⟨x,hx⟩ := exists_residue_generic_over_countable hc hκ hs h00 E hE n
  have hx0 : ∀ q, x q ≠ 0 := algebraicallyIndependent_coordinate_ne_zero E x hx
  let u := rvNormalizedUnitTuple a x hx0
  have huval : rvUnitTupleValues u = α.val := (rvNormalizedUnitTuple_values a x hx0).trans ha
  have huA : u ∈ (A.unitFamily.piece i).carrier := by
    change rvUnitTupleValues u ∈ (A.piece i).carrier
    exact huval.symm ▸ α.property
  let au : A.unitFamily.piece i := ⟨u,huA⟩
  have huv : gammaGroundFullPreimageValueMap (A.piece i) au = α := Subtype.ext huval
  have hEx : ∀ q ≤ n, (E : Set (ModelResidue M)).Definable Language.ring
      {z : Fin n → ModelResidue M | rvNormalizedTuple a z ∈
        ((List.finRange n).take q).foldl rvGenericCoordinate (rvUnitValues '' Eh.carrier)} := by
    intro q hq
    exact hEV false q (by simpa using hq)
  have huEh : u ∈ Eh.carrier :=
    (gammaGroundRVGeneric_normalized_test hs h00 B hsmall Eh a E hEx x hx hx0).mp
      (ha.symm ▸ (hh i).symm ▸ α.property)
  have hforward := ((D.unitValueFamilyMap.comp F.toFamilyMap).mem_equalizerPiece_at
    (H.comp A.unitValueFamilyMap) i au).mp huEh
  change D.unitValueFamilyMap.toFun (F.equiv ⟨i,au⟩) = H.toFun ⟨i,gammaGroundFullPreimageValueMap (A.piece i) au⟩ at hforward
  rw [huv] at hforward
  have htag : (F.equiv ⟨i,au⟩).1 = j := congrArg Sigma.fst hforward
  have huBranch : u ∈ (F.toFamilyMap.branchSource i j).carrier :=
    (F.toFamilyMap.mem_branchSource_iff_tag i j au).mpr htag
  let pu : F.toFamilyMap.branchSource i j := ⟨u,huBranch⟩
  let v := f pu
  have hFuv : F.equiv ⟨i,au⟩ = ⟨j,v⟩ := by
    apply gammaGroundFamilyCarrier_ext D.unitFamily htag
    rfl
  have hvval : rvUnitTupleValues v.val = β.val := by
    have he := congrArg (fun t : D.Carrier => t.2.val) hforward
    change rvUnitTupleValues (F.equiv ⟨i,au⟩).2.val = β.val at he
    rw [hFuv] at he
    exact he
  have hvb : rvUnitTupleValues v.val = rvUnitTupleValues b := hvval.trans hb.symm
  obtain ⟨y,hy0,hy⟩ := rvNormalizedTuple_surjective_on_fibre b v.val hvb
  have hxy : Sum.elim x y ∈ R := rvNormalizedUnitMap_point f a b x y pu rfl hy.symm
  have hyind : AlgebraicIndependent E y := acf_definable_bijection_target_independent E R (hER ()) x y hxy
    (fun z hz => (rvNormalizedMapRelation_functional f.unitRaw a b x y z hxy hz).symm)
    (fun z hz => rvNormalizedMapRelation_inverse_functional f.unitRaw
      (f.unitRaw_injective (F.toFamilyMap.branchMap_injective F.equiv.injective i j)) a b x z y hxy hz) hx
  have hEy : ∀ q ≤ n, (E : Set (ModelResidue M)).Definable Language.ring
      {z : Fin n → ModelResidue M | rvNormalizedTuple b z ∈
        ((List.finRange n).take q).foldl rvGenericCoordinate (rvUnitValues '' Ek.carrier)} := by
    intro q hq
    exact hEV true q (by simpa using hq)
  have hyv : rvNormalizedUnitTuple b y hy0 = v.val := by
    apply rvUnitValues_injective
    exact (rvNormalizedUnitTuple_raw b y hy0).trans hy
  have hvEk : v.val ∈ Ek.carrier := by
    rw [← hyv]
    apply (gammaGroundRVGeneric_normalized_test hs h00 B hsmall Ek b E hEy y hyind hy0).mp
    exact hb.symm ▸ (hk j).symm ▸ β.property
  have hback := ((A.unitValueFamilyMap.comp F.symm.toFamilyMap).mem_equalizerPiece_at
    (K.comp D.unitValueFamilyMap) j v).mp hvEk
  change A.unitValueFamilyMap.toFun (F.equiv.symm ⟨j,v⟩) =
    K.toFun ⟨j,gammaGroundFullPreimageValueMap (D.piece j) v⟩ at hback
  rw [← hFuv,F.equiv.symm_apply_apply] at hback
  have hvβ : gammaGroundFullPreimageValueMap (D.piece j) v = β := Subtype.ext hvval
  change (⟨i,gammaGroundFullPreimageValueMap (A.piece i) au⟩ : A.Carrier) =
    K.toFun ⟨j,gammaGroundFullPreimageValueMap (D.piece j) v⟩ at hback
  rw [huv,hvβ] at hback
  exact hback.symm

end DiamondIntegral.Section3
