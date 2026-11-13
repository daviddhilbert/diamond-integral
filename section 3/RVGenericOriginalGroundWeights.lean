import «section 3».GammaGroundRVUnitRawMaps
import «section 3».RVGenericMapCoefficients
import «section 3».GammaGroundGenericNormalizedTests
import «section 3».RVResidueFullFibreCoordinates
import «section 3».GammaGroundRVGenericContraction
import «section 3».RVOriginalGroundMonomialCoefficients
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
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

/-- Each value of the actual generic contraction has a unimodular
formula with actual original-ground definable RV coefficients. The only
cited input is the approved diagonal birational classification. -/
theorem gammaGroundRVGeneric_original_coefficients [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (H : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (f : GammaGroundMap (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J))
    (hf : Function.Injective f) (h : GammaGroundMap G J)
    (hh : (gammaGroundRVGenericValueImage hs h00 B hsmall
      (((gammaGroundFullPreimageValueMap J).comp f).equalizer
        (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier)
    (γ : G) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, ∃ c : Fin n → (CanonicalRV.RVSort M)ˣ,
      IsUnit C.det ∧ (∀ i, DefinableClosureAtBase B .rv (rvUnitValues c i)) ∧
      (h γ).val = rvUnitTupleValues c * integerMonomialMap (G := Values.Gamma (M := M)) C γ.val ∧
      GammaGroundDefinable hc B (rawRVUnitSpace n) {c} := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let A := gammaGroundRVUnitGammaPreimage G
  let Eh := ((gammaGroundFullPreimageValueMap J).comp f).equalizer
    (h.comp (gammaGroundFullPreimageValueMap G))
  obtain ⟨a,ha⟩ := rvUnitTupleValues_surjective (M := M) n γ.val
  obtain ⟨b,hb⟩ := rvUnitTupleValues_surjective (M := M) n (h γ).val
  let T := rvUnitValues '' Eh.carrier
  have hT : DefinableOverBase B (fun _ => .rv) T :=
    (gammaGroundRVUnit_definable_iff Eh.carrier).mp Eh.definable
  let R := rvNormalizedMapRelation f.unitRaw a b
  have hR : ResiduePurity.PureDef R := rvNormalizedMapRelation_pure hκ.le hsmall f.unitRaw a b
  obtain ⟨E,hE,hclosed,hET,hER⟩ := rvGeneric_family_extra_coefficients hc hκ.le hs h00 B hsmall
    (fun _ : Unit => T) (fun _ => hT) (fun _ => a) (List.finRange n)
    (fun _ : Unit => Fin n ⊕ Fin n) (fun _ => R) (fun _ => hR)
  letI : IsAlgClosed E := hclosed
  obtain ⟨x,hx⟩ := exists_residue_generic_over_countable hc hκ hs h00 E hE n
  have hx0 : ∀ i, x i ≠ 0 := algebraicallyIndependent_coordinate_ne_zero E x hx
  let u := rvNormalizedUnitTuple a x hx0
  have huval : rvUnitTupleValues u = γ.val := (rvNormalizedUnitTuple_values a x hx0).trans ha
  have huA : u ∈ A.carrier := by
    change rvUnitTupleValues u ∈ G.carrier
    exact huval.symm ▸ γ.property
  let au : A := ⟨u,huA⟩
  have huv : gammaGroundFullPreimageValueMap G au = γ := Subtype.ext huval
  have hEx : ∀ q ≤ n, (E : Set (ModelResidue M)).Definable Language.ring
      {z : Fin n → ModelResidue M | rvNormalizedTuple a z ∈
        ((List.finRange n).take q).foldl rvGenericCoordinate T} := by
    intro q hq
    exact hET () q (by simpa using hq)
  have huEh : u ∈ Eh.carrier :=
    (gammaGroundRVGeneric_normalized_test hs h00 B hsmall Eh a E hEx x hx hx0).mp
      (ha.symm ▸ hh.symm ▸ γ.property)
  obtain ⟨au',hau',hvalue⟩ := huEh
  have hsame : au' = au := Subtype.ext hau'
  subst au'
  change rvUnitTupleValues (f au).val = (h (gammaGroundFullPreimageValueMap G au)).val at hvalue
  rw [huv] at hvalue
  have hvb : rvUnitTupleValues (f au).val = rvUnitTupleValues b := hvalue.trans hb.symm
  obtain ⟨y,_,hy⟩ := rvNormalizedTuple_surjective_on_fibre b (f au).val hvb
  have hxy : Sum.elim x y ∈ R := rvNormalizedUnitMap_point f a b x y au rfl hy.symm
  obtain ⟨C,c,hC,hcdef,hweights,hcsingle⟩ := rvMap_residue_generic_original_coefficients E
    f.unitRaw (f.unitRaw_injective hf) a b (H E hE a b) (hER ()) x y hx hxy
  rw [ha,hb] at hweights
  exact ⟨C,c,hC,hcdef,hweights,hcsingle⟩

end DiamondIntegral.Section3
