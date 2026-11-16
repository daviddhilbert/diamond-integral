import «section 6».SmallPairedBoundaryData

/-! Pointwise eventual paired boundary data for an arbitrary original
mixed centre family. This separates the local geometric argument from
the uniform bound over retained RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem point_eventual_small_paired_boundary_data
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) (p : E) :
    ∃ η : Gamma M,∀ c : positiveBoundaryCoefficients (S := S) hc,η.val<vfValue (c.val 0) →
      (uniformPairedBoundaryDataMap hc f E hEA hRV hD (boundaryPairInput hc E p c)).val ∈
        (smallPairedBoundaryData f α β hα hβ).carrier := by
  obtain ⟨α',hα'⟩ := exists_gt α
  obtain ⟨β',hβ'⟩ := exists_gt β
  have hLocal := unary_mixed_paired_disc_offset_codes_at_point hc hκ hs hsmall hv f h
    ⟨p.val,hEA p.property⟩ α' β'
  have hp0 : p.val.1 0≠0 := hD.nonzero (hEA p.property) 0
  refine ⟨hLocal.choose/finiteValue (p.val.1 0) hp0,fun c hcSmall => ?_⟩
  let z := boundaryPairInput hc E p c
  let d := c.val 0*p.val.1 0
  have hd : d≠0 := mul_ne_zero c.property.1 hp0
  have hRadius : hLocal.choose<finiteValue (c.val 0) c.property.1*finiteValue (p.val.1 0) hp0 :=
    (div_lt_iff_lt_mul).mp hcSmall
  have hRadiusVal : hLocal.choose.val<vfValue d := by
    change hLocal.choose.val<Values.vfValueHom (c.val 0*p.val.1 0)
    rw [map_mul,valueHom_eq_value,valueHom_eq_value]
    exact hRadius
  obtain ⟨q,hqx,hqu,hqv,he,ha,hb,hCode⟩ := hLocal.choose_spec d hd hRadiusVal
  have hqActual : q=uniformBoundaryMap hc E hEA hRV hD z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i
      exact hqx
    · exact hqu
  subst q
  have hSourceSmall : α.val<vfValue d := hα'.trans_le ha
  have hTargetSmall : β.val<vfValue
      ((f (uniformBoundaryMap hc E hEA hRV hD z)).val.1 0-(f ⟨p.val,hEA p.property⟩).val.1 0) :=
    hβ'.trans_le hb
  refine ⟨?_,⟨Set.mem_univ _,?_⟩,he,hTargetSmall⟩
  · change pairedBoundaryDataCodes _ ∈ parameterizedPairedDiscCodes (unaryMixedScalarGraph f)
    rw [uniformPairedBoundaryDataMap_codes]
    simpa only [uniformBoundaryCoreCodes,uniformTargetBoundaryOffsetMap_value,
      uniformBoundaryCenterMap,boundaryPairInput,z,d] using hCode
  · change (p.val.1 0+c.val 0*p.val.1 0)-p.val.1 0≠0 ∧
      α.val<vfValue ((p.val.1 0+c.val 0*p.val.1 0)-p.val.1 0)
    simpa only [add_sub_cancel_left] using (show d≠0 ∧ α.val<vfValue d from ⟨hd,hSourceSmall⟩)

end DiamondIntegral.Section6
