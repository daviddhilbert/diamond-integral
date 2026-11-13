import «section 3».GammaGroundUnitFamilyGenericContraction
import «section 3».RVGenericMapCoefficients
import «section 3».GammaGroundGenericNormalizedTests
import «section 3».GammaGroundRVUnitRawMaps
import «section 3».RVResidueFullFibreCoordinates
import «section 3».RVOriginalGroundMonomialCoefficients
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

/-- The original-ground unimodular coefficient conclusion retains every
finite source and target tag. It is obtained from the actual generic
point of the appropriate partial branch graph. -/
theorem gammaGroundUnitFamily_generic_original_coefficients [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyMap A.unitFamily D.unitFamily) (hF : Function.Injective F.toFun)
    (H : GammaGroundFamilyMap A D)
    (hh : ∀ i, (gammaGroundRVGenericValueImage hs h00 B hsmall
      ((D.unitValueFamilyMap.comp F).equalizerPiece (H.comp A.unitValueFamilyMap) i)).carrier = (A.piece i).carrier)
    (γ : A.Carrier) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, ∃ c : Fin n → (CanonicalRV.RVSort M)ˣ,
      IsUnit C.det ∧ (∀ q, DefinableClosureAtBase B .rv (rvUnitValues c q)) ∧
      (H.toFun γ).2.val = rvUnitTupleValues c * integerMonomialMap (G := Values.Gamma (M := M)) C γ.2.val ∧
      GammaGroundDefinable hc B (rawRVUnitSpace n) {c} := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let i := γ.1
  let j := (H.toFun γ).1
  let α : A.piece i := γ.2
  let β : D.piece j := (H.toFun γ).2
  let Eh := (D.unitValueFamilyMap.comp F).equalizerPiece (H.comp A.unitValueFamilyMap) i
  obtain ⟨a,ha⟩ := rvUnitTupleValues_surjective (M := M) n α.val
  obtain ⟨b,hb⟩ := rvUnitTupleValues_surjective (M := M) n β.val
  let T := rvUnitValues '' Eh.carrier
  have hT : DefinableOverBase B (fun _ => .rv) T :=
    (gammaGroundRVUnit_definable_iff Eh.carrier).mp Eh.definable
  let f := F.branchMap i j
  let R := rvNormalizedMapRelation f.unitRaw a b
  have hR : ResiduePurity.PureDef R := rvNormalizedMapRelation_pure hκ.le hsmall f.unitRaw a b
  obtain ⟨E,hE,hclosed,hET,hER⟩ := rvGeneric_family_extra_coefficients hc hκ.le hs h00 B hsmall
    (fun _ : Unit => T) (fun _ => hT) (fun _ => a) (List.finRange n)
    (fun _ : Unit => Fin n ⊕ Fin n) (fun _ => R) (fun _ => hR)
  letI : IsAlgClosed E := hclosed
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
        ((List.finRange n).take q).foldl rvGenericCoordinate T} := by
    intro q hq
    exact hET () q (by simpa using hq)
  have huEh : u ∈ Eh.carrier :=
    (gammaGroundRVGeneric_normalized_test hs h00 B hsmall Eh a E hEx x hx hx0).mp
      (ha.symm ▸ (hh i).symm ▸ α.property)
  have hforward := ((D.unitValueFamilyMap.comp F).mem_equalizerPiece_at
    (H.comp A.unitValueFamilyMap) i au).mp huEh
  change D.unitValueFamilyMap.toFun (F.toFun ⟨i,au⟩) = H.toFun ⟨i,gammaGroundFullPreimageValueMap (A.piece i) au⟩ at hforward
  rw [huv] at hforward
  have htag : (F.toFun ⟨i,au⟩).1 = j := congrArg Sigma.fst hforward
  have huBranch : u ∈ (F.branchSource i j).carrier := (F.mem_branchSource_iff_tag i j au).mpr htag
  let pu : F.branchSource i j := ⟨u,huBranch⟩
  let v := f pu
  have hFuv : F.toFun ⟨i,au⟩ = ⟨j,v⟩ := by
    apply gammaGroundFamilyCarrier_ext D.unitFamily htag
    rfl
  have hvval : rvUnitTupleValues v.val = β.val := by
    have he := congrArg (fun t : D.Carrier => t.2.val) hforward
    change rvUnitTupleValues (F.toFun ⟨i,au⟩).2.val = β.val at he
    rw [hFuv] at he
    exact he
  have hvb : rvUnitTupleValues v.val = rvUnitTupleValues b := hvval.trans hb.symm
  obtain ⟨y,_,hy⟩ := rvNormalizedTuple_surjective_on_fibre b v.val hvb
  have hxy : Sum.elim x y ∈ R := rvNormalizedUnitMap_point f a b x y pu rfl hy.symm
  obtain ⟨C,c,hC,hcdef,hweights,hcsingle⟩ := rvMap_residue_generic_original_coefficients E
    f.unitRaw (f.unitRaw_injective (F.branchMap_injective hF i j)) a b (RY E hE a b) (hER ()) x y hx hxy
  rw [ha,hb] at hweights
  exact ⟨C,c,hC,hcdef,hweights,hcsingle⟩

end DiamondIntegral.Section3
