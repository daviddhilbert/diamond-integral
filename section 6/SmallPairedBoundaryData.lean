import «section 6».UniformBoundaryConditions

/-! Paired cores can be required to lie beyond any two original-base
named radius floors before the common coefficient is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

def puncturedRadiusDefSet (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    DefSet (rawVFSpace (M := M) 1) S := by
  refine ⟨puncturedRadiusBall δ,?_⟩
  change S.Definable LRV ((rawVFSpace (M := M) 1).preimage (puncturedRadiusBall δ))
  have hEq : (rawVFSpace (M := M) 1).preimage (puncturedRadiusBall δ)=vfValues '' puncturedRadiusBall δ := by
    ext z
    constructor
    · rintro ⟨hz,hP⟩
      exact ⟨(rawVFSpace (M := M) 1).decode ⟨z,hz⟩,hP,vfValues_decode _⟩
    · rintro ⟨p,hp,rfl⟩
      refine ⟨Set.mem_range_self p,?_⟩
      have hDecode : (rawVFSpace (M := M) 1).decode ⟨vfValues p,Set.mem_range_self p⟩=p :=
        vfValues_injective (vfValues_decode _)
      exact hDecode.symm ▸ hp
  rw [hEq]
  exact puncturedRadiusBall_definable δ hδ

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def smallPairedBoundaryData (f : Map A B) (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    DefSet (pairedBoundaryDataSpace M (r+s)) S := by
  let F := goodPairedBoundaryData (unaryMixedScalarGraph f) (unaryMixedScalarGraph_definable f)
  let U := ((DefSet.univ (rawMixedSpace (M := M) 2 (r+s)) S).prod (puncturedRadiusDefSet α hα)).prod
    (puncturedRadiusDefSet β hβ)
  exact ⟨F.carrier ∩ U.carrier,F.definable.inter _ U.definable⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_centers_eventual_small_paired_boundary_data
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hFinite : E.carrier.Finite)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ c : positiveBoundaryCoefficients (S := S) hc,
      η.val < vfValue (c.val 0) → ∀ p : E,
        (uniformPairedBoundaryDataMap hc f E hEA hRV hD (boundaryPairInput hc E p c)).val ∈
          (smallPairedBoundaryData f α β hα hβ).carrier := by
  letI : Fintype E := hFinite.fintype
  obtain ⟨α',hα'⟩ := exists_gt α
  obtain ⟨β',hβ'⟩ := exists_gt β
  have hLocal (p : E) := unary_mixed_paired_disc_offset_codes_at_point hc hκ hs hsmall hv f h
    ⟨p.val,hEA p.property⟩ α' β'
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
  obtain ⟨q,hqx,hqu,hqv,he,ha,hb',hCode⟩ := (hLocal p).choose_spec d hd hRadiusVal
  have hqActual : q=uniformBoundaryMap hc E hEA hRV hD z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i
      change q.val.1 0=p.val.1 0+c.val 0*p.val.1 0
      exact hqx
    · exact hqu
  subst q
  have hSourceSmall : α.val < vfValue d := hα'.trans_le ha
  have hTargetSmall : β.val < vfValue
      ((f (uniformBoundaryMap hc E hEA hRV hD z)).val.1 0-(f ⟨p.val,hEA p.property⟩).val.1 0) :=
    hβ'.trans_le hb'
  refine ⟨?_,⟨Set.mem_univ _,?_⟩,?_⟩
  · change pairedBoundaryDataCodes _ ∈ parameterizedPairedDiscCodes (unaryMixedScalarGraph f)
    rw [uniformPairedBoundaryDataMap_codes]
    simpa only [uniformBoundaryCoreCodes,uniformTargetBoundaryOffsetMap_value,
      uniformBoundaryCenterMap,boundaryPairInput,z,d] using hCode
  · change (p.val.1 0+c.val 0*p.val.1 0)-p.val.1 0 ≠ 0 ∧
      α.val < vfValue ((p.val.1 0+c.val 0*p.val.1 0)-p.val.1 0)
    simpa only [add_sub_cancel_left] using
      (show d ≠ 0 ∧ α.val < vfValue d from ⟨hd,hSourceSmall⟩)
  · exact ⟨he,hTargetSmall⟩

theorem exists_named_small_paired_boundary_coefficient
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hFinite : E.carrier.Finite)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    ∃ (c : VF M) (hc0 : c ≠ 0) (hcPos : (1 : GammaInfinity M) < vfValue c),
      S.Definable₁ LRV {c.val} ∧ ∀ p : E,
        (uniformPairedBoundaryDataMap hc f E hEA hRV hD
          (boundaryPairInput hc E p ⟨(fun _ => c),hc0,hcPos⟩)).val ∈
          (smallPairedBoundaryData f α β hα hβ).carrier :=
  exists_named_boundary_coefficient_for_data h00 hc hv V hV hVS hSV hnt f E hEA hRV hD _
    (finite_centers_eventual_small_paired_boundary_data hc hκ hs hsmall hv f h hRV hD E hEA hFinite α β hα hβ)

end DiamondIntegral.Section6
