import «section 6».UniformBoundaryEvaluation
import «section 6».MixedPairedDiscOffsetCodes

/-! Uniform actual paired-core codes over every point of a finite
center family. All sufficiently small coefficients work simultaneously,
and the target offsets are evaluated from the original map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def boundaryPairInput (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (p : E) (c : positiveBoundaryCoefficients (S := S) hc) :
    E.prod (positiveBoundaryCoefficients hc) := ⟨(p.val,c.val),p.property,c.property⟩

def uniformBoundaryCoreCodes (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (z : E.prod (positiveBoundaryCoefficients hc)) : Fin (r+s) ⊕ Fin 4 → M :=
  Sum.elim (rvValues (Fin.append z.val.1.2 (f (uniformBoundaryCenterMap hc E hEA z)).val.2))
    ![(z.val.1.1 0).val,((f (uniformBoundaryCenterMap hc E hEA z)).val.1 0).val,
      (z.val.2 0*z.val.1.1 0).val,((uniformTargetBoundaryOffsetMap hc f E hEA hRV hD z).val 0).val]

def uniformBoundaryCoreGood (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (c : positiveBoundaryCoefficients (S := S) hc) : Prop :=
  ∀ p : E,uniformBoundaryCoreCodes hc f E hEA hRV hD (boundaryPairInput hc E p c) ∈
    parameterizedPairedDiscCodes (unaryMixedScalarGraph f)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_centers_eventual_paired_boundary_codes
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hFinite : E.carrier.Finite) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ c : positiveBoundaryCoefficients (S := S) hc,
      η.val < vfValue (c.val 0) → uniformBoundaryCoreGood hc f E hEA hRV hD c := by
  letI : Fintype E := hFinite.fintype
  have hLocal (p : E) := unary_mixed_paired_disc_offset_codes_at_point hc hκ hs hsmall hv f h
    ⟨p.val,hEA p.property⟩ 1 1
  have hp0 (p : E) : p.val.1 0 ≠ 0 := hD.nonzero (hEA p.property) 0
  let cutoff (p : E) : Gamma M := (hLocal p).choose/finiteValue (p.val.1 0) (hp0 p)
  obtain ⟨b,hb⟩ := (Set.finite_range cutoff).bddAbove
  refine ⟨max b 1,le_max_right _ _,fun c hcSmall p => ?_⟩
  let z := boundaryPairInput hc E p c
  let d := c.val 0*p.val.1 0
  have hd : d ≠ 0 := mul_ne_zero c.property.1 (hp0 p)
  have hcSmall' : max b 1 < finiteValue (c.val 0) c.property.1 := hcSmall
  have hCut : cutoff p < finiteValue (c.val 0) c.property.1 :=
    (hb (Set.mem_range_self p)).trans_lt ((le_max_left _ _).trans_lt hcSmall')
  have hRadius : (hLocal p).choose < finiteValue (c.val 0) c.property.1*finiteValue (p.val.1 0) (hp0 p) :=
    (div_lt_iff_lt_mul).mp hCut
  have hRadiusVal : (hLocal p).choose.val < vfValue d := by
    change (hLocal p).choose.val < Values.vfValueHom (c.val 0*p.val.1 0)
    rw [map_mul,valueHom_eq_value,valueHom_eq_value]
    exact hRadius
  obtain ⟨q,hqx,hqu,hqv,he,hα,hβ,hCode⟩ := (hLocal p).choose_spec d hd hRadiusVal
  have hqActual : q=uniformBoundaryMap hc E hEA hRV hD z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i
      change q.val.1 0=p.val.1 0+c.val 0*p.val.1 0
      exact hqx
    · exact hqu
  subst q
  simpa only [uniformBoundaryCoreCodes,uniformTargetBoundaryOffsetMap_value,
    uniformBoundaryCenterMap,boundaryPairInput,z,d] using hCode

end DiamondIntegral.Section6
