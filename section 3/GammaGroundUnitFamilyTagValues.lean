import «section 3».GammaGroundUnitFamilyGenericTags
import «section 3».GammaGroundGenericFibreTests
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

/-- The generic output value belongs to the actual Gamma piece indexed
by the generic output tag. Both assertions are tested at one actual RV
point of the prescribed full source fibre. -/
theorem gammaGroundUnitFamily_generic_value_range {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ)
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyMap A.unitFamily D.unitFamily) (i : Fin A.tags)
    (h : GammaGroundMap (A.piece i) (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))))
    (hh : (gammaGroundRVGenericValueImage hs h00 B hsmall
      (((GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp
        (F.valueMap i)).equalizer (h.comp (gammaGroundFullPreimageValueMap (A.piece i))))).carrier = (A.piece i).carrier)
    (j : Fin D.tags) (γ : A.piece i)
    (hγ : γ.val ∈ (gammaGroundRVGenericValueImage hs h00 B hsmall (F.branchSource i j)).carrier) :
    (h γ).val ∈ (D.piece j).carrier := by
  let w : GammaGroundMap (gammaGroundRVUnitGammaPreimage (A.piece i))
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
    (GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp (F.valueMap i)
  let E := w.equalizer (h.comp (gammaGroundFullPreimageValueMap (A.piece i)))
  let T : Bool → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) :=
    fun b => if b then F.branchSource i j else E
  obtain ⟨u,hu,hT⟩ := gammaGroundGeneric_finite_fibre_test hs h00 B hsmall hκ T γ.val
  obtain ⟨a,ha,hea⟩ := (hT false).mp (hh.symm ▸ γ.property)
  have huTag := (hT true).mp hγ
  obtain ⟨a',ha',b,hFab⟩ := (F.mem_branchSource i j u).mp huTag
  have heaa : a' = a := Subtype.ext (ha'.trans ha.symm)
  subst a'
  have hvγ : gammaGroundFullPreimageValueMap (A.piece i) a = γ :=
    Subtype.ext ((congrArg rvUnitTupleValues ha).trans hu)
  have hvb : (w a).val = rvUnitTupleValues b.val := by
    change rvUnitTupleValues (F.toFun ⟨i,a⟩).2.val = rvUnitTupleValues b.val
    rw [hFab]
  change (w a).val = (h (gammaGroundFullPreimageValueMap (A.piece i) a)).val at hea
  rw [hvγ] at hea
  have hb : rvUnitTupleValues b.val ∈ (D.piece j).carrier := b.property
  exact (hvb.symm.trans hea) ▸ hb

end DiamondIntegral.Section3
