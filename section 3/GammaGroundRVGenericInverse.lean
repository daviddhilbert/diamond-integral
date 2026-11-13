import «section 3».GammaGroundRVGenericContraction
import «section 3».GammaGroundRVUnitRawMaps
import «section 3».RVGenericMapCoefficients
import «section 3».GammaGroundGenericNormalizedTests
import «section 3».RVResidueFullFibreCoordinates
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

/-- The generic contraction of an actual full-preimage bijection and that
of its inverse are inverse at every source value. Coefficients used to
test residue genericity are constructed in the proof and never added to
the original ground. -/
theorem gammaGroundRVGeneric_inverse_at {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (f : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J))
    (h : GammaGroundMap G J) (k : GammaGroundMap J G)
    (hh : (gammaGroundRVGenericValueImage hs h00 B hsmall
      (((gammaGroundFullPreimageValueMap J).comp f.map).equalizer
        (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier)
    (hk : (gammaGroundRVGenericValueImage hs h00 B hsmall
      (((gammaGroundFullPreimageValueMap G).comp f.symm.map).equalizer
        (k.comp (gammaGroundFullPreimageValueMap J)))).carrier = J.carrier)
    (γ : G) : k (h γ) = γ := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero h00
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  let A := gammaGroundRVUnitGammaPreimage G
  let D := gammaGroundRVUnitGammaPreimage J
  let Eh := ((gammaGroundFullPreimageValueMap J).comp f.map).equalizer
    (h.comp (gammaGroundFullPreimageValueMap G))
  let Ek := ((gammaGroundFullPreimageValueMap G).comp f.symm.map).equalizer
    (k.comp (gammaGroundFullPreimageValueMap J))
  obtain ⟨a,ha⟩ := rvUnitTupleValues_surjective (M := M) n γ.val
  obtain ⟨b,hb⟩ := rvUnitTupleValues_surjective (M := M) n (h γ).val
  let V : Bool → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := fun i => if i then Ek else Eh
  let T := fun i => rvUnitValues '' (V i).carrier
  have hT : ∀ i, DefinableOverBase B (fun _ => .rv) (T i) :=
    fun i => (gammaGroundRVUnit_definable_iff (V i).carrier).mp (V i).definable
  let normalizer : Bool → Fin n → (CanonicalRV.RVSort M)ˣ := fun i => if i then b else a
  let R := rvNormalizedMapRelation f.map.unitRaw a b
  have hR : ResiduePurity.PureDef R := rvNormalizedMapRelation_pure hκ.le hsmall f.map.unitRaw a b
  obtain ⟨E,hE,hclosed,hEV,hER⟩ := rvGeneric_family_extra_coefficients hc hκ.le hs h00 B hsmall
    T hT normalizer (List.finRange n) (fun _ : Unit => Fin n ⊕ Fin n) (fun _ => R) (fun _ => hR)
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
        ((List.finRange n).take q).foldl rvGenericCoordinate (rvUnitValues '' Eh.carrier)} := by
    intro q hq
    exact hEV false q (by simpa using hq)
  have huEh : u ∈ Eh.carrier :=
    (gammaGroundRVGeneric_normalized_test hs h00 B hsmall Eh a E hEx x hx hx0).mp
      (ha.symm ▸ hh.symm ▸ γ.property)
  obtain ⟨au',hau',hvalue⟩ := huEh
  have hsame : au' = au := Subtype.ext hau'
  subst au'
  change rvUnitTupleValues (f.map au).val = (h (gammaGroundFullPreimageValueMap G au)).val at hvalue
  rw [huv] at hvalue
  have hvb : rvUnitTupleValues (f.map au).val = rvUnitTupleValues b := hvalue.trans hb.symm
  obtain ⟨y,hy0,hy⟩ := rvNormalizedTuple_surjective_on_fibre b (f.map au).val hvb
  have hxy : Sum.elim x y ∈ R := rvNormalizedUnitMap_point f.map a b x y au rfl hy.symm
  have hyind : AlgebraicIndependent E y := acf_definable_bijection_target_independent E R (hER ()) x y hxy
    (fun z hz => (rvNormalizedMapRelation_functional f.map.unitRaw a b x y z hxy hz).symm)
    (fun z hz => rvNormalizedMapRelation_inverse_functional f.map.unitRaw
      (f.map.unitRaw_injective f.bijective.1) a b x z y hxy hz) hx
  have hEy : ∀ q ≤ n, (E : Set (ModelResidue M)).Definable Language.ring
      {z : Fin n → ModelResidue M | rvNormalizedTuple b z ∈
        ((List.finRange n).take q).foldl rvGenericCoordinate (rvUnitValues '' Ek.carrier)} := by
    intro q hq
    exact hEV true q (by simpa using hq)
  have hyv : rvNormalizedUnitTuple b y hy0 = (f.map au).val := by
    apply rvUnitValues_injective
    exact (rvNormalizedUnitTuple_raw b y hy0).trans hy
  have hvEk : (f.map au).val ∈ Ek.carrier := by
    rw [← hyv]
    apply (gammaGroundRVGeneric_normalized_test hs h00 B hsmall Ek b E hEy y hyind hy0).mp
    exact hb.symm ▸ hk.symm ▸ (h γ).property
  obtain ⟨v,hv,hkv⟩ := hvEk
  have hvfu : v = f.map au := Subtype.ext hv
  subst v
  change rvUnitTupleValues (f.symm.map (f.map au)).val =
    (k (gammaGroundFullPreimageValueMap J (f.map au))).val at hkv
  have hback : f.symm.map (f.map au) = au := f.map.inverse_apply f.bijective au
  rw [hback] at hkv
  have hvtarget : gammaGroundFullPreimageValueMap J (f.map au) = h γ := Subtype.ext hvalue
  rw [hvtarget,huval] at hkv
  exact Subtype.ext hkv.symm

end DiamondIntegral.Section3
