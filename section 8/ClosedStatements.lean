import «section 8».Remark815

/-! # The main theorems with every hypothesis supplied

Theorems 7.26 and 8.11 and Remarks 8.14 and 8.15 are proved for any Puiseux ambient `P` and any
valuation `Gv` on its valued field that is compatible with the language (`hv`) and nontrivial on
the base (`hntB`). Here these data are supplied once and for all:

* `ambient` is the Puiseux ambient of Section 5, chosen from `puiseuxAmbient_nonempty`: a
  saturated, strongly homogeneous elementary extension of the complex Puiseux series field whose
  real base is the field of Laurent series `ℂ((t))`, with the canonical structure;
* `ValueGroup` and `valued` are a valuation compatible with the language, which exists in every
  model of ACVF (`Values.presentationValuation`, `Values.presentation_compatible`);
* `base_nontrivial_value`: the uniformizer `t` of the base has value `≠ 1`
  (`ambientLaurentField_nontrivial`).

The statements below therefore have no hypotheses: for every complex polynomial `f`, the motivic
zeta function of `f` is rational of degree at most `0`, and the motivic Milnor fiber
`𝒮_f = −lim_{T → ∞} Z_f(T)` equals `Θ 𝔼^◇ ∫^◇ [𝒳_f]`, which is `Vol [𝒳_f]` and `Vol [𝒳_t]`.
The smooth-variety forms keep the étale chart as their one explicit hypothesis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Closed

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section5
open DiamondIntegral.Section5.PuiseuxOriginal
open DiamondIntegral.Section8.Hm DiamondIntegral.Section8.RationalSeries DiamondIntegral.Section8.Milnor

/-- The Puiseux ambient of Section 5 (Notation 5.3), chosen from its existence theorem. -/
abbrev ambient : PuiseuxAmbient := puiseuxAmbient

/-- The value group of a valuation on the ambient's valued field compatible with the language. -/
abbrev ValueGroup : Type := Values.presentationType (M := ambient.N)

instance : LinearOrderedCommGroupWithZero ValueGroup := Values.presentationOrder

/-- The compatible valuation as a `Valued` structure. -/
instance valued : Valued (VF ambient.N) ValueGroup := Valued.mk' Values.presentationValuation

/-- The valuation is compatible with the language. -/
theorem compatible (x y : VF ambient.N) : VFValued.predV x y ↔ Valued.v x ≤ Valued.v y :=
  Values.presentation_compatible x y

/-- The base field contains an element of value `≠ 1`: the uniformizer `t`. -/
theorem base_nontrivial_value : ∃ x : ambient.G.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1 := by
  obtain ⟨u, hu⟩ := ambientLaurentField_nontrivial ambient.e ambient.G ambient.hB
  refine ⟨(u : ambient.G.fieldBase.field), u.ne_zero, fun h => hu ?_⟩
  apply Subtype.ext
  change Values.vrv (CanonicalRV.encodedRv ((u : ambient.G.fieldBase.field) : VF ambient.N)) =
    (1 : Values.Gamma (M := ambient.N)).val
  have h1 : Valued.v ((u : ambient.G.fieldBase.field) : VF ambient.N) = Valued.v (1 : VF ambient.N) := by
    rw [h, map_one]
  have hle := (compatible _ _).mpr h1.le
  have hge := (compatible _ _).mpr h1.ge
  refine ((Values.vrv_eq_iff _ _).mpr ?_).trans Values.vf_value_one
  exact ⟨hge, hle⟩

/-! ### Theorem 7.26 in the Puiseux ambient -/

open DiamondIntegral.Section7.Theorem726 in
/-- **Theorem 7.26** in the Puiseux ambient, over its real base:
`K μVF^◇[*] ≅ K μRV^db[*] / J_var`. -/
def theorem_7_26 :=
  Section7.Theorem726.theorem_7_26 ValueGroup ambient.G.model00 ambient.hc ambient.G.uncountable
    ambient.G.saturated compatible ambient.G.real ambient.G.small_real (base_nontrivial ambient)
    ambient.G.fieldBase base_nontrivial_value

open DiamondIntegral.Section7.Theorem726 in
/-- **Theorem 7.26, graded form**, in the Puiseux ambient. -/
def theorem_7_26_graded :=
  Section7.Theorem726.theorem_7_26_graded ValueGroup ambient.G.model00 ambient.hc
    ambient.G.uncountable ambient.G.saturated compatible ambient.G.real ambient.G.small_real
    (base_nontrivial ambient) ambient.G.fieldBase base_nontrivial_value

/-! ### Theorem 8.11 and Remarks 8.14 and 8.15 for every complex polynomial -/

/-- **Theorem 8.11 (`direct:mil`)** with no hypothesis, for `X = 𝔸^d` and any complex polynomial
`f`: `Z_f(T)` lies in `K^μ̂ Var_ℂ[[𝔸]⁻¹][T]†`, has degree at most `0`, and
`𝒮_f = −lim_{T → ∞} Z_f(T) = Θ 𝔼^◇ ∫^◇ [𝒳_f]`. -/
theorem theorem_8_11 {d : ℕ} (f : MvPolynomial (Fin d) ℂ) :
    HasLimit Lunit (milnorZeta ambient ValueGroup compatible base_nontrivial_value f)
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc
        (milnorClass ambient ValueGroup compatible base_nontrivial_value f))) :=
  theorem_8_11_milnor ambient ValueGroup compatible base_nontrivial_value f

/-- **Remark 8.14** with no hypothesis: `Θ 𝔼^◇ ∫^◇ [𝒳_f] = Vol [𝒳_f]`, with `Vol` the motivic
volume of Notation 5.3; with `theorem_8_11`, `𝒮_f = Vol [𝒳_f]`. -/
theorem remark_8_14 {d : ℕ} (f : MvPolynomial (Fin d) ℂ) :
    milnorClass ambient ValueGroup compatible base_nontrivial_value f =
      puiseuxBoundedVFVolume ambient (Algebra.GrothendieckAddGroup.of
        (gammaGroundVFSemiringClass (Section7.Remark728.forgetVF ambient.hc ambient.G
          (milnorObject ambient f)))) :=
  VolComparison.remark_8_14_milnor ambient ValueGroup compatible base_nontrivial_value f

/-- **Remark 8.15** with no hypothesis: `Θ 𝔼^◇ ∫^◇ [𝒳_f] = Vol [𝒳_t]`. -/
theorem remark_8_15 {d : ℕ} (f : MvPolynomial (Fin d) ℂ) :
    milnorClass ambient ValueGroup compatible base_nontrivial_value f =
      puiseuxBoundedVFVolume ambient (Algebra.GrothendieckAddGroup.of
        (gammaGroundVFSemiringClass (Remark815.XtObj ambient Remark815.g0 f))) :=
  Remark815.remark_8_15_milnor ambient f ValueGroup compatible base_nontrivial_value

end DiamondIntegral.Section8.Closed
