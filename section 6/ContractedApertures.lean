import «section 6».RelativeApertureChains
import «section 6».ApertureCore
import «section 6».NonzeroBranchTags
import «section 6».ScalarCodeAlgebra
import «section 2».DefinableVFInverse
import Section3.RVOperations

/-! Definition 6.11, contracted layer. The manuscript first defines the
centripetal transformation (CT) from RV-only aperture data: an aperture
`τ : U → RV` with a bound `0 ≤ vrv τ ≤ Δ`, the absolute cutoff
`γ_𝔭 = rad(pr₁ 𝔭) + vrv τ(u)` and the contracted value `t_𝔭 = τ(u) rv(pr₁ 𝔭)`.
A bijective lift adds a continuous VF section `b` with `rv b = t_𝔭`.

`RelativeApertureData` packages the lifted data directly. This file shows the
two presentations agree:
* `ContractedApertureData` is the RV-only data, with the contracted
  transformation `contractedPoint`;
* `RelativeApertureData.toContracted` reads off the aperture
  `τ = rv(b / x₁)` from a lift;
* `RelativeApertureData.point_contracts` : the lifted map `RV`-contracts to
  CT (on the core, `rv` of the new coordinate is `t_𝔭`; elsewhere the maps
  agree);
* `ContractedApertureData.lift` : contracted data together with a section `b`
  satisfying the manuscript's conditions are lift data, with the given
  aperture. Hence the class of lifts is exactly the manuscript's. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The RV-only data of a centripetal transformation (Definition 6.11, before
lifting). The aperture is a definable RV code on active points, constant on
each retained label. -/
structure ContractedApertureData (A : DefSet (rawMixedSpace (M := M) n r) S) where
  coordinate : Fin n
  activeTags : DefSet (rawRVSpace (M := M) r) S
  focus : (Fin n → VF M) → (Fin r → RVInfinity M) → VF M
  focusMap : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace 1) S)
  focusMap_eq : ∀ p : focusActive A activeTags,
    (focusMap p).val 0 = focus (Function.update p.val.1 coordinate 0) p.val.2
  sourceProper : ProperInvariant S A.carrier
  sourceDoublyBounded : VFDoublyBounded A.carrier
  tagged : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  continuous : ∀ u ∈ activeTags.carrier,
    ContinuousOn (fun x => focus (Function.update x coordinate 0) u) (vfFibre A.carrier u)
  focusRV : ∀ p ∈ A.carrier, p.2 ∈ activeTags.carrier →
    rv M (focus (Function.update p.1 coordinate 0) p.2) = rv M (p.1 coordinate)
  apertureCode : (Fin n ⊕ Fin r → M) → M
  aperture_definable : S.DefinableFun LRV apertureCode
  aperture_nonzero : ∀ p : focusActive A activeTags, GammaParameters.NonzeroRV (apertureCode (mixedValues p.val))
  aperture_label : ∀ p q : focusActive A activeTags, p.val.2 = q.val.2 →
    apertureCode (mixedValues p.val) = apertureCode (mixedValues q.val)
  apertureBound : Gamma M
  apertureBound_nonnegative : 1 ≤ apertureBound
  apertureBound_named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {apertureBound}}
  aperture_lower : ∀ p : focusActive A activeTags, 1 ≤ GammaParameters.codeValue (apertureCode (mixedValues p.val))
  aperture_upper : ∀ p : focusActive A activeTags,
    GammaParameters.codeValue (apertureCode (mixedValues p.val)) ≤ apertureBound
  covariance : ∀ u ∈ activeTags.carrier, ∃ α : Gamma M, ∃ β : Fin n → Gamma M,
    (S ∪ Set.range (rvValues u)).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}} ∧
    NamedGammaTuple (S ∪ Set.range (rvValues u)) β ∧
    AlphaInvariant (fun i => if i = coordinate then α else β i) (vfFibre A.carrier u) ∧
    (∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent β (Function.update a coordinate 0) (Function.update b coordinate 0) →
      α.val < vfValue (focus (Function.update a coordinate 0) u - focus (Function.update b coordinate 0) u)) ∧
    (∀ a (_ : (a,u) ∈ A.carrier),
      α.val ≤ (GammaParameters.codeValue (apertureCode (mixedValues (a,u)))).val * vfValue (a coordinate))

namespace ContractedApertureData
variable {A : DefSet (rawMixedSpace (M := M) n r) S} (C : ContractedApertureData A)

/-- The aperture `τ(u)` at an active point, as an RV element. -/
def aperture (p : focusActive A C.activeTags) : RVInfinity M :=
  ⟨C.apertureCode (mixedValues p.val),(C.aperture_nonzero p).1⟩

/-- The absolute cutoff `γ_𝔭 = rad(pr₁ 𝔭) + vrv τ(u)`. -/
def cutoff (p : focusActive A C.activeTags) : GammaInfinity M :=
  (GammaParameters.codeValue (C.apertureCode (mixedValues p.val))).val * vfValue (p.val.1 C.coordinate)

/-- The contracted value `t_𝔭 = τ(u) rv(pr₁ 𝔭)`. -/
def contractedValue (p : focusActive A C.activeTags) : RVInfinity M :=
  C.aperture p * rv M (p.val.1 C.coordinate)

/-- The core clause of (CT). -/
def core (p : focusActive A C.activeTags) : Prop :=
  C.cutoff p < vfValue (p.val.1 C.coordinate - C.focus (Function.update p.val.1 C.coordinate 0) p.val.2)

/-- The centripetal transformation (CT) on active points: the core is sent to
its contracted value `t_𝔭`, recorded as an RV tag after the branch tag; the
annulus is translated by the focus. -/
def contractedPoint (p : focusActive A C.activeTags) : Mixed M n (2+r) :=
  if C.core p then
    (Function.update p.val.1 C.coordinate 0,
      Fin.append ![branchTag (M := M) true,C.contractedValue p] p.val.2)
  else
    (Function.update p.val.1 C.coordinate
        (p.val.1 C.coordinate - C.focus (Function.update p.val.1 C.coordinate 0) p.val.2),
      Fin.append ![branchTag (M := M) false,branchTag (M := M) false] p.val.2)

end ContractedApertureData

theorem vfValue_mul_eq (x y : VF M) : vfValue (x*y) = vfValue x*vfValue y := by
  change Values.vfValueHom (x*y) = Values.vfValueHom x*Values.vfValueHom y
  exact map_mul _ _ _

theorem codeValue_iRv_val {y : VF M} (hy : y ≠ 0) :
    (GammaParameters.codeValue (iRv y.val)).val = vfValue y := by
  exact nonzero_rv_codeValue_val (rv M y) (fun he => hy ((rv_eq_zero_iff y).mp he))

namespace RelativeApertureData
variable {A : DefSet (rawMixedSpace (M := M) n r) S} (D : RelativeApertureData (G := G) A)

theorem coordinate_ne_zero (p : focusActive A D.activeTags) : p.val.1 D.coordinate ≠ 0 := by
  intro h0
  have hrv := D.focusRV p.val p.property.1 p.property.2
  rw [h0,rv_zero] at hrv
  have hf : D.focus (Function.update p.val.1 D.coordinate 0) p.val.2 = 0 := (rv_eq_zero_iff _).mp hrv
  have hle := D.endpoint_nonnegative p
  rw [hf] at hle
  have he0 := D.endpoint_nonzero p
  have hlt := (rv_eq_iff_value_close he0).mp
    (rfl : rv M (D.endpoint (Function.update p.val.1 D.coordinate 0) p.val.2) =
      rv M (D.endpoint (Function.update p.val.1 D.coordinate 0) p.val.2))
  rw [sub_self] at hlt
  exact (not_le.mpr hlt) hle

/-- The quotient `b / x₁` at an active point. -/
def apertureRatio (p : focusActive A D.activeTags) : VF M :=
  (D.endpointMap p).val 0 * (p.val.1 D.coordinate)⁻¹

theorem apertureRatio_ne_zero (p : focusActive A D.activeTags) : D.apertureRatio p ≠ 0 :=
  mul_ne_zero (by rw [D.endpointMap_eq]; exact D.endpoint_nonzero p) (inv_ne_zero (D.coordinate_ne_zero p))

/-- The aperture code `rv(b / x₁)` of a lift. -/
def apertureCode (z : Fin n ⊕ Fin r → M) : M :=
  iRv (iVFMul (scalarCodeExtension D.endpointMap z) (rawVFInverse (z (.inl D.coordinate))))

theorem apertureCode_at (p : focusActive A D.activeTags) :
    D.apertureCode (mixedValues p.val) = iRv (D.apertureRatio p).val := by
  unfold apertureCode apertureRatio
  rw [scalarCodeExtension_at]
  change iRv (iVFMul _ (rawVFInverse (p.val.1 D.coordinate).val)) = _
  rw [rawVFInverse_vf]
  rfl

end RelativeApertureData

section Algebra

theorem vfValue_inv_mul {x : VF M} (hx : x ≠ 0) : vfValue x⁻¹ * vfValue x = 1 := by
  rw [← vfValue_mul_eq,inv_mul_cancel₀ hx]
  change Values.vfValueHom 1 = 1
  exact map_one _

theorem rv_mul_inv (x y : VF M) : rv M (x * y⁻¹) = rv M x * (rv M y)⁻¹ := by
  change RVOperations.rvHom (x * y⁻¹) = RVOperations.rvHom x * (RVOperations.rvHom y)⁻¹
  rw [map_mul,map_inv₀]

theorem vfValue_eq_of_rv_eq {x y : VF M} (h : rv M x = rv M y) : vfValue x = vfValue y := by
  change Values.vrv (rv M x) = Values.vrv (rv M y)
  rw [h]

theorem rv_ne_zero_of_ne {y : VF M} (hy : y ≠ 0) : rv M y ≠ rvZero M :=
  fun he => hy ((rv_eq_zero_iff y).mp he)

theorem iRv_nonzero {y : VF M} (hy : y ≠ 0) : GammaParameters.NonzeroRV (iRv y.val) :=
  ⟨(rv M y).property,fun he => rv_ne_zero_of_ne hy (Subtype.ext he)⟩

end Algebra

namespace RelativeApertureData
variable {A : DefSet (rawMixedSpace (M := M) n r) S} (D : RelativeApertureData (G := G) A)

theorem focus_value_active (p : focusActive A D.activeTags) :
    vfValue (D.focus (Function.update p.val.1 D.coordinate 0) p.val.2) = vfValue (p.val.1 D.coordinate) :=
  vfValue_eq_of_rv_eq (D.focusRV p.val p.property.1 p.property.2)

theorem ratio_value (p : focusActive A D.activeTags) :
    vfValue (D.apertureRatio p) * vfValue (p.val.1 D.coordinate) = vfValue ((D.endpointMap p).val 0) := by
  unfold apertureRatio
  rw [vfValue_mul_eq,mul_assoc,vfValue_inv_mul (D.coordinate_ne_zero p),mul_one]

theorem apertureCode_value (p : focusActive A D.activeTags) :
    (GammaParameters.codeValue (D.apertureCode (mixedValues p.val))).val = vfValue (D.apertureRatio p) := by
  rw [D.apertureCode_at]
  exact codeValue_iRv_val (D.apertureRatio_ne_zero p)

theorem cutoff_value (p : focusActive A D.activeTags) :
    (GammaParameters.codeValue (D.apertureCode (mixedValues p.val))).val * vfValue (p.val.1 D.coordinate) =
      vfValue ((D.endpointMap p).val 0) := by
  rw [D.apertureCode_value,D.ratio_value]

/-- The contracted (RV-only) data of a lift: the aperture is `rv(b / x₁)`. -/
def toContracted : ContractedApertureData A where
  coordinate := D.coordinate
  activeTags := D.activeTags
  focus := D.focus
  focusMap := D.focusMap
  focusMap_eq := D.focusMap_eq
  sourceProper := D.sourceProper
  sourceDoublyBounded := D.sourceDoublyBounded
  tagged := D.tagged
  continuous := D.continuous
  focusRV := D.focusRV
  apertureCode := D.apertureCode
  aperture_definable := rv_scalarCode_definable (scalarMulCode_definable
    (scalarCodeExtension_definable D.endpointMap) (rawVFInverse_definable S (Sum.inl D.coordinate : Fin n ⊕ Fin r)))
  aperture_nonzero p := by
    rw [D.apertureCode_at]
    exact iRv_nonzero (D.apertureRatio_ne_zero p)
  aperture_label p q hpq := by
    rw [D.apertureCode_at,D.apertureCode_at]
    have hx : rv M (p.val.1 D.coordinate) = rv M (q.val.1 D.coordinate) :=
      congrFun (D.tagged p.val p.property.1 q.val q.property.1 hpq) D.coordinate
    have hb := D.endpoint_RV_constant p q hpq
    change (rv M (D.apertureRatio p)).val = (rv M (D.apertureRatio q)).val
    unfold apertureRatio
    rw [rv_mul_inv,rv_mul_inv,hx,hb]
  apertureBound := D.apertureBound
  apertureBound_nonnegative := D.apertureBound_nonnegative
  apertureBound_named := D.apertureBound_named
  aperture_lower p := by
    change (1 : Gamma M).val ≤ (GammaParameters.codeValue (D.apertureCode (mixedValues p.val))).val
    rw [D.apertureCode_value]
    have hle := D.endpoint_nonnegative p
    rw [D.focus_value_active,← D.endpointMap_eq,← D.ratio_value] at hle
    have h := mul_le_mul' hle (le_refl (vfValue (p.val.1 D.coordinate)⁻¹))
    rw [mul_comm (vfValue (p.val.1 D.coordinate)),vfValue_inv_mul (D.coordinate_ne_zero p),mul_assoc,
      mul_comm (vfValue (p.val.1 D.coordinate)),vfValue_inv_mul (D.coordinate_ne_zero p),mul_one] at h
    exact h
  aperture_upper p := by
    change (GammaParameters.codeValue (D.apertureCode (mixedValues p.val))).val ≤ D.apertureBound.val
    rw [D.apertureCode_value]
    have hle := D.endpoint_upper_bound p
    rw [← D.ratio_value] at hle
    have h := mul_le_mul' hle (le_refl (vfValue (p.val.1 D.coordinate)⁻¹))
    rw [mul_assoc,mul_comm (vfValue (p.val.1 D.coordinate)),vfValue_inv_mul (D.coordinate_ne_zero p),mul_one,
      mul_assoc,mul_comm (vfValue (p.val.1 D.coordinate)),vfValue_inv_mul (D.coordinate_ne_zero p),mul_one] at h
    exact h
  covariance u hu := by
    obtain ⟨α,β,hα,hβ,hInv,hCov,hEnd⟩ := D.covariance u hu
    refine ⟨α,β,hα,hβ,hInv,hCov,fun a ha => ?_⟩
    let p : focusActive A D.activeTags := ⟨(a,u),ha,hu⟩
    have h := D.cutoff_value p
    rw [D.endpointMap_eq] at h
    change α.val ≤ (GammaParameters.codeValue (D.apertureCode (mixedValues p.val))).val * vfValue (p.val.1 D.coordinate)
    rw [h]
    exact hEnd a ha

theorem toContracted_cutoff (p : focusActive A D.activeTags) :
    D.toContracted.cutoff p = vfValue ((D.endpointMap p).val 0) := D.cutoff_value p

theorem toContracted_contractedValue (p : focusActive A D.activeTags) :
    D.toContracted.contractedValue p = rv M ((D.endpointMap p).val 0) := by
  have hx := rv_ne_zero_of_ne (D.coordinate_ne_zero p)
  have hτ : D.toContracted.aperture p = rv M (D.apertureRatio p) :=
    Subtype.ext (D.apertureCode_at p)
  change D.toContracted.aperture p * rv M (p.val.1 D.coordinate) = _
  rw [hτ]
  unfold apertureRatio
  have hx0 : rv M (p.val.1 D.coordinate) ≠ 0 := fun h => hx (Subtype.ext ((congrArg Subtype.val h).trans RVOperations.zero_val))
  rw [rv_mul_inv,mul_assoc,inv_mul_cancel₀ hx0,mul_one]

/-- The lifted map `RV`-contracts to the centripetal transformation: the core
clauses agree, on the core the new coordinate has RV value `t_𝔭`, and on the
annulus the two maps agree. -/
theorem point_contracts (p : focusActive A D.activeTags) :
    (D.core p.val = true ↔ D.toContracted.core p) ∧
    (D.toContracted.core p →
      rv M ((D.point p.val).1 D.coordinate) = D.toContracted.contractedValue p) ∧
    (¬ D.toContracted.core p → (D.point p.val).1 = (D.toContracted.contractedPoint p).1) := by
  have hF := D.extendedFocus_active p.property.1 p.property.2
  have hE : D.extendedEndpoint p.val = (D.endpointMap p).val 0 :=
    (D.extendedEndpoint_active p.property.1 p.property.2).trans (D.endpointMap_eq p).symm
  have hcore : D.core p.val = true ↔ D.toContracted.core p := by
    unfold core ContractedApertureData.core
    rw [decide_eq_true_iff,D.toContracted_cutoff,hE,hF]
    rfl
  refine ⟨hcore,fun hc => ?_,fun hc => ?_⟩
  · have hc' : D.core p.val = true := hcore.mpr hc
    rw [D.toContracted_contractedValue]
    unfold point
    rw [hc']
    simp only [ite_true]
    change rv M (Function.update p.val.1 D.coordinate
      (p.val.1 D.coordinate - D.extendedFocus p.val + D.extendedEndpoint p.val) D.coordinate) = _
    rw [Function.update_self,hE]
    have hb := D.endpoint_nonzero p
    rw [← D.endpointMap_eq] at hb
    apply (rv_eq_iff_value_close hb).mpr
    rw [add_sub_cancel_right,hF]
    have hcv : D.toContracted.cutoff p < _ := hc
    rw [D.toContracted_cutoff] at hcv
    exact hcv
  · have hc' : D.core p.val = false := by
      cases h : D.core p.val
      · rfl
      · exact absurd (hcore.mp h) hc
    unfold point ContractedApertureData.contractedPoint
    rw [hc']
    simp only [hc,ite_false,Bool.false_eq_true,add_zero,hF]
    rfl

end RelativeApertureData

namespace ContractedApertureData
variable {A : DefSet (rawMixedSpace (M := M) n r) S} (C : ContractedApertureData A)

theorem aperture_ne_zero (p : focusActive A C.activeTags) : C.aperture p ≠ rvZero M :=
  fun he => (C.aperture_nonzero p).2 (congrArg Subtype.val he)

theorem aperture_vrv (p : focusActive A C.activeTags) :
    Values.vrv (C.aperture p) = (GammaParameters.codeValue (C.apertureCode (mixedValues p.val))).val :=
  (nonzero_rv_codeValue_val (C.aperture p) (C.aperture_ne_zero p)).symm

theorem contractedValue_vrv (p : focusActive A C.activeTags) :
    Values.vrv (C.contractedValue p) = C.cutoff p := by
  unfold contractedValue cutoff
  rw [RVOperations.vrv_mul,C.aperture_vrv]
  rfl

theorem focus_value_active (p : focusActive A C.activeTags) :
    vfValue (C.focus (Function.update p.val.1 C.coordinate 0) p.val.2) = vfValue (p.val.1 C.coordinate) :=
  vfValue_eq_of_rv_eq (C.focusRV p.val p.property.1 p.property.2)

/-- A bijective lift of contracted aperture data: a continuous nonzero VF
section `b` with `rv b = t_𝔭` (Definition 6.11). The result is lift data in
the sense of `RelativeApertureData`. -/
def lift (endpoint : (Fin n → VF M) → (Fin r → RVInfinity M) → VF M)
    (endpointMap : Map (focusActive A C.activeTags) (DefSet.univ (rawVFSpace 1) S))
    (endpointMap_eq : ∀ p : focusActive A C.activeTags,
      (endpointMap p).val 0 = endpoint (Function.update p.val.1 C.coordinate 0) p.val.2)
    (endpoint_continuous : ∀ u ∈ C.activeTags.carrier,
      ContinuousOn (fun x => endpoint (Function.update x C.coordinate 0) u) (vfFibre A.carrier u))
    (endpoint_nonzero : ∀ p : focusActive A C.activeTags,
      endpoint (Function.update p.val.1 C.coordinate 0) p.val.2 ≠ 0)
    (endpoint_rv : ∀ p : focusActive A C.activeTags, rv M ((endpointMap p).val 0) = C.contractedValue p) :
    RelativeApertureData (G := G) A where
  coordinate := C.coordinate
  activeTags := C.activeTags
  focus := C.focus
  focusMap := C.focusMap
  focusMap_eq := C.focusMap_eq
  sourceProper := C.sourceProper
  sourceDoublyBounded := C.sourceDoublyBounded
  tagged := C.tagged
  continuous := C.continuous
  focusRV := C.focusRV
  endpoint := endpoint
  endpointMap := endpointMap
  endpointMap_eq := endpointMap_eq
  endpoint_continuous := endpoint_continuous
  endpoint_nonzero := endpoint_nonzero
  endpoint_nonnegative p := by
    rw [C.focus_value_active,← endpointMap_eq]
    have hv : vfValue ((endpointMap p).val 0) = C.cutoff p := by
      rw [← C.contractedValue_vrv,← endpoint_rv p]
      rfl
    rw [hv]
    unfold cutoff
    have h1 : (1 : Gamma M).val ≤ (GammaParameters.codeValue (C.apertureCode (mixedValues p.val))).val :=
      C.aperture_lower p
    have h := mul_le_mul' h1 (le_refl (vfValue (p.val.1 C.coordinate)))
    rw [Values.gamma_val_one,one_mul] at h
    exact h
  endpoint_RV_constant p q hpq := by
    rw [endpoint_rv,endpoint_rv]
    unfold contractedValue aperture
    have hx : rv M (p.val.1 C.coordinate) = rv M (q.val.1 C.coordinate) :=
      congrFun (C.tagged p.val p.property.1 q.val q.property.1 hpq) C.coordinate
    rw [hx]
    congr 2
    exact C.aperture_label p q hpq
  apertureBound := C.apertureBound
  apertureBound_nonnegative := C.apertureBound_nonnegative
  apertureBound_named := C.apertureBound_named
  endpoint_upper_bound p := by
    have hv : vfValue ((endpointMap p).val 0) = C.cutoff p := by
      rw [← C.contractedValue_vrv,← endpoint_rv p]
      rfl
    rw [hv]
    have h1 : (GammaParameters.codeValue (C.apertureCode (mixedValues p.val))).val ≤ C.apertureBound.val :=
      C.aperture_upper p
    exact mul_le_mul' h1 (le_refl _)
  covariance u hu := by
    obtain ⟨α,β,hα,hβ,hInv,hCov,hEnd⟩ := C.covariance u hu
    refine ⟨α,β,hα,hβ,hInv,hCov,fun a ha => ?_⟩
    let p : focusActive A C.activeTags := ⟨(a,u),ha,hu⟩
    have hv : vfValue ((endpointMap p).val 0) = C.cutoff p := by
      rw [← C.contractedValue_vrv,← endpoint_rv p]
      rfl
    rw [endpointMap_eq] at hv
    change α.val ≤ vfValue (endpoint (Function.update p.val.1 C.coordinate 0) p.val.2)
    rw [hv]
    exact hEnd a ha

/-- The lift recovers the given aperture: lifting and then contracting is the
identity on the RV aperture data. -/
theorem lift_aperture (endpoint : (Fin n → VF M) → (Fin r → RVInfinity M) → VF M)
    (endpointMap : Map (focusActive A C.activeTags) (DefSet.univ (rawVFSpace 1) S))
    (endpointMap_eq : ∀ p : focusActive A C.activeTags,
      (endpointMap p).val 0 = endpoint (Function.update p.val.1 C.coordinate 0) p.val.2)
    (endpoint_continuous : ∀ u ∈ C.activeTags.carrier,
      ContinuousOn (fun x => endpoint (Function.update x C.coordinate 0) u) (vfFibre A.carrier u))
    (endpoint_nonzero : ∀ p : focusActive A C.activeTags,
      endpoint (Function.update p.val.1 C.coordinate 0) p.val.2 ≠ 0)
    (endpoint_rv : ∀ p : focusActive A C.activeTags, rv M ((endpointMap p).val 0) = C.contractedValue p)
    (p : focusActive A C.activeTags) :
    (C.lift (G := G) endpoint endpointMap endpointMap_eq endpoint_continuous endpoint_nonzero
      endpoint_rv).toContracted.apertureCode (mixedValues p.val) = C.apertureCode (mixedValues p.val) := by
  let D := C.lift (G := G) endpoint endpointMap endpointMap_eq endpoint_continuous endpoint_nonzero endpoint_rv
  have hx := rv_ne_zero_of_ne (D.coordinate_ne_zero p)
  have hx0 : rv M (p.val.1 C.coordinate) ≠ 0 :=
    fun h => hx (Subtype.ext ((congrArg Subtype.val h).trans RVOperations.zero_val))
  change D.apertureCode (mixedValues p.val) = _
  rw [D.apertureCode_at]
  change (rv M (D.apertureRatio p)).val = (C.aperture p).val
  congr 1
  unfold RelativeApertureData.apertureRatio
  rw [rv_mul_inv]
  change rv M ((endpointMap p).val 0) * (rv M (p.val.1 C.coordinate))⁻¹ = _
  rw [endpoint_rv]
  unfold contractedValue
  rw [mul_assoc,mul_inv_cancel₀ hx0,mul_one]

end ContractedApertureData

end DiamondIntegral.Section6
