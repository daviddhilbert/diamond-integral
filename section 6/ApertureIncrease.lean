import «section 6».ContractedApertures

/-! Remark 6.12 (`bigger:aper`). Two admissible apertures on the same locus
and focus with `γ'(u) > γ(u)` everywhere, the full label `u` retained and
distinct core tags. On a polydisc `𝔭`, increasing the aperture replaces the
old endpoint `t_𝔭` by the relative annulus and the new endpoint
`rv(𝔐_{γ_𝔭} ∖ 𝔐_{γ'_𝔭}) ⊎ {t'_𝔭}`; outside the old core the two
transformations agree; when the old contracted clause occurs the whole old
core is present, so the released part is nonempty.

* `ApertureIncrease C` : a larger aperture code for the contracted data `C`,
  and `ApertureIncrease.target` the resulting contracted data (same locus,
  focus and labels);
* `agree_outside` : outside the old core the transformations agree;
* `old_core` : on the old core the new transformation gives either the new
  endpoint (new core, branch tag `true`) or a translated point in the released
  annulus `γ_𝔭 < v(a - λ) ≤ γ'_𝔭` (branch tag `false`);
* `released_attained` : every point of the released annulus over the fibre
  occurs (invariance makes the whole old core present);
* `released_nonempty` : the released annulus is nonempty when the old core
  clause occurs. -/

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

namespace ContractedApertureData
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

/-- A strictly larger admissible aperture on the same locus and focus. -/
structure ApertureIncrease (C : ContractedApertureData (G := G) A) where
  code : (Fin n ⊕ Fin r → M) → M
  definable : S.DefinableFun LRV code
  nonzero : ∀ p : focusActive A C.activeTags, GammaParameters.NonzeroRV (code (mixedValues p.val))
  label : ∀ p q : focusActive A C.activeTags, p.val.2 = q.val.2 →
    code (mixedValues p.val) = code (mixedValues q.val)
  bound : Gamma M
  bound_one : 1 ≤ bound
  bound_named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {bound}}
  upper : ∀ p : focusActive A C.activeTags, GammaParameters.codeValue (code (mixedValues p.val)) ≤ bound
  increase : ∀ p : focusActive A C.activeTags,
    (GammaParameters.codeValue (C.apertureCode (mixedValues p.val))).val <
      (GammaParameters.codeValue (code (mixedValues p.val))).val

namespace ApertureIncrease
variable {C : ContractedApertureData (G := G) A} (I : ApertureIncrease C)

/-- The contracted data with the larger aperture. -/
def target : ContractedApertureData (G := G) A where
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
  apertureCode := I.code
  aperture_definable := I.definable
  aperture_nonzero := I.nonzero
  aperture_label := I.label
  apertureBound := I.bound
  apertureBound_nonnegative := I.bound_one
  apertureBound_named := I.bound_named
  aperture_lower p := by
    change (1 : Gamma M).val ≤ (GammaParameters.codeValue (I.code (mixedValues p.val))).val
    exact (show (1 : Gamma M).val ≤ _ from C.aperture_lower p).trans (I.increase p).le
  aperture_upper := I.upper
  covariance u hu := by
    obtain ⟨α,β,hα,hβ,hInv,hCov,hEnd⟩ := C.covariance u hu
    refine ⟨α,β,hα,hβ,hInv,hCov,fun a ha => ?_⟩
    let p : focusActive A C.activeTags := ⟨(a,u),ha,hu⟩
    exact (hEnd a ha).trans (mul_le_mul' (I.increase p).le (le_refl _))

theorem cutoff_le (p : focusActive A C.activeTags) : C.cutoff p ≤ I.target.cutoff p :=
  mul_le_mul' (I.increase p).le (le_refl _)

theorem core_of_target_core (p : focusActive A C.activeTags) (h : I.target.core p) : C.core p := by
  unfold ContractedApertureData.core at h ⊢
  exact (I.cutoff_le p).trans_lt h

/-- Outside the old core the two transformations agree. -/
theorem agree_outside (p : focusActive A C.activeTags) (h : ¬ C.core p) :
    I.target.contractedPoint p = C.contractedPoint p := by
  have h' : ¬ I.target.core p := fun h' => h (I.core_of_target_core p h')
  unfold ContractedApertureData.contractedPoint
  simp only [h,h',ite_false]
  rfl

/-- On the old core, the larger aperture either contracts to the new endpoint
`t'_𝔭` (new core) or releases the point into the relative annulus
`γ_𝔭 < v(a - λ) ≤ γ'_𝔭`, where it is translated by the focus. The two cases
carry distinct branch tags. -/
theorem old_core (p : focusActive A C.activeTags) (h : C.core p) :
    (I.target.core p ∧ I.target.contractedPoint p =
      (Function.update p.val.1 C.coordinate 0,
        Fin.append ![branchTag (M := M) true,I.target.contractedValue p] p.val.2)) ∨
    (¬ I.target.core p ∧
      C.cutoff p < vfValue (p.val.1 C.coordinate - C.focus (Function.update p.val.1 C.coordinate 0) p.val.2) ∧
      vfValue (p.val.1 C.coordinate - C.focus (Function.update p.val.1 C.coordinate 0) p.val.2) ≤
        I.target.cutoff p ∧
      I.target.contractedPoint p =
        (Function.update p.val.1 C.coordinate
            (p.val.1 C.coordinate - C.focus (Function.update p.val.1 C.coordinate 0) p.val.2),
          Fin.append ![branchTag (M := M) false,branchTag (M := M) false] p.val.2)) := by
  by_cases h' : I.target.core p
  · refine Or.inl ⟨h',?_⟩
    unfold ContractedApertureData.contractedPoint
    simp only [h',ite_true]
    rfl
  · refine Or.inr ⟨h',h,?_,?_⟩
    · have h'' : ¬ (I.target.cutoff p < vfValue (p.val.1 C.coordinate -
          C.focus (Function.update p.val.1 C.coordinate 0) p.val.2)) := h'
      exact not_lt.mp h''
    · unfold ContractedApertureData.contractedPoint
      simp only [h',ite_false]
      rfl

theorem cutoff_label (D : ContractedApertureData (G := G) A) (p q : focusActive A D.activeTags)
    (hpq : p.val.2 = q.val.2) : D.cutoff p = D.cutoff q := by
  unfold ContractedApertureData.cutoff
  have hx : rv M (p.val.1 D.coordinate) = rv M (q.val.1 D.coordinate) :=
    congrFun (D.tagged p.val p.property.1 q.val q.property.1 hpq) D.coordinate
  rw [D.aperture_label p q hpq,vfValue_eq_of_rv_eq hx]

/-- Every point of the released annulus over the fibre of an old core point
occurs: invariance makes the whole old core present. -/
theorem released_attained (p : focusActive A C.activeTags) (h : C.core p) (d : VF M)
    (hd₁ : C.cutoff p < vfValue d) (hd₂ : vfValue d ≤ I.target.cutoff p) :
    ∃ q : focusActive A C.activeTags, q.val.2 = p.val.2 ∧
      Function.update q.val.1 C.coordinate 0 = Function.update p.val.1 C.coordinate 0 ∧
      C.core q ∧ ¬ I.target.core q ∧
      I.target.contractedPoint q =
        (Function.update p.val.1 C.coordinate d,
          Fin.append ![branchTag (M := M) false,branchTag (M := M) false] p.val.2) := by
  let c := C.coordinate
  let u := p.val.2
  let l := C.focus (Function.update p.val.1 c 0) u
  let x' := Function.update p.val.1 c (l + d)
  obtain ⟨α,β,_,_,hInv,_,hEnd⟩ := C.covariance u p.property.2
  have hEndp : α.val ≤ C.cutoff p := hEnd p.val.1 p.property.1
  have hcore : C.cutoff p < vfValue (p.val.1 c - l) := h
  have hcong : Congruent (fun i => if i = c then α else β i) p.val.1 x' := by
    intro i
    by_cases hi : i = c
    · rw [hi]
      simp only [ite_true]
      have hm := SpecialTransformations.Section9.vfValue_min_le_sub (p.val.1 c - l) d
      rw [show p.val.1 c - l - d = p.val.1 c - x' c by simp only [x',Function.update_self]; abel] at hm
      exact hEndp.trans_lt ((lt_min hcore hd₁).trans_le hm)
    · simp only [hi,ite_false]
      have hx : x' i = p.val.1 i := Function.update_of_ne hi _ _
      change (β i).val < vfValue (p.val.1 i - x' i)
      rw [hx]
      exact Congruent.refl β p.val.1 i
  have hx' : (x',u) ∈ A.carrier := (hInv p.val.1 x' hcong).mp p.property.1
  let q : focusActive A C.activeTags := ⟨(x',u),hx',p.property.2⟩
  have hupd : Function.update x' c 0 = Function.update p.val.1 c 0 := Function.update_idem _ _ _
  have hfocus : C.focus (Function.update q.val.1 c 0) q.val.2 = l := by
    change C.focus (Function.update x' c 0) u = l
    rw [hupd]
  have hdiff : q.val.1 c - C.focus (Function.update q.val.1 c 0) q.val.2 = d := by
    rw [hfocus]
    change Function.update p.val.1 c (l + d) c - l = d
    rw [Function.update_self]
    abel
  have hcut : C.cutoff q = C.cutoff p := cutoff_label C q p rfl
  have hcut' : I.target.cutoff q = I.target.cutoff p := cutoff_label I.target q p rfl
  have hqcore : C.core q := by
    unfold ContractedApertureData.core
    rw [hdiff,hcut]
    exact hd₁
  have hqcore' : ¬ I.target.core q := by
    intro hq
    have hq' : I.target.cutoff q < vfValue (q.val.1 c - C.focus (Function.update q.val.1 c 0) q.val.2) := hq
    rw [hdiff,hcut'] at hq'
    exact (not_lt.mpr hd₂) hq'
  refine ⟨q,rfl,hupd,hqcore,hqcore',?_⟩
  unfold ContractedApertureData.contractedPoint
  simp only [hqcore',ite_false]
  change (Function.update q.val.1 c (q.val.1 c - C.focus (Function.update q.val.1 c 0) q.val.2),
    Fin.append ![branchTag (M := M) false,branchTag (M := M) false] u) = _
  rw [hdiff]
  change (Function.update x' c d,_) = _
  rw [Function.update_idem]

theorem coordinate_ne_zero_of_core (D : ContractedApertureData (G := G) A) (p : focusActive A D.activeTags)
    (h : D.core p) : p.val.1 D.coordinate ≠ 0 := by
  intro h0
  have hrv := D.focusRV p.val p.property.1 p.property.2
  rw [h0,rv_zero] at hrv
  have hf : D.focus (Function.update p.val.1 D.coordinate 0) p.val.2 = 0 := (rv_eq_zero_iff _).mp hrv
  have hv0 : vfValue (0 : VF M) = 0 := ((vfValue_eq_infinity_iff 0).mpr rfl).trans Values.infinity_eq_zero
  have h' : D.cutoff p < vfValue (p.val.1 D.coordinate - D.focus (Function.update p.val.1 D.coordinate 0) p.val.2) := h
  unfold ContractedApertureData.cutoff at h'
  rw [hf,h0,sub_zero,hv0,mul_zero] at h'
  exact lt_irrefl _ h'

/-- When the old contracted clause occurs, the released annulus
`γ_𝔭 < v(d) ≤ γ'_𝔭` is nonempty. -/
theorem released_nonempty (p : focusActive A C.activeTags) (h : C.core p) :
    ∃ d : VF M, C.cutoff p < vfValue d ∧ vfValue d ≤ I.target.cutoff p := by
  have hx := coordinate_ne_zero_of_core C p h
  have hv0 : vfValue (p.val.1 C.coordinate) ≠ 0 := by
    intro he
    rw [← Values.infinity_eq_zero,vfValue_eq_infinity_iff] at he
    exact hx he
  have hlt : C.cutoff p < I.target.cutoff p := by
    refine lt_of_le_of_ne (I.cutoff_le p) (fun he => (I.increase p).ne ?_)
    have he' : (GammaParameters.codeValue (C.apertureCode (mixedValues p.val))).val *
        vfValue (p.val.1 C.coordinate) =
        (GammaParameters.codeValue (I.code (mixedValues p.val))).val * vfValue (p.val.1 C.coordinate) := he
    exact mul_right_cancel₀ hv0 he'
  obtain ⟨d,hd⟩ := vfValue_surjective (I.target.cutoff p)
  exact ⟨d,hd ▸ hlt,hd.le⟩

/-- The new endpoint `t'_𝔭` has value `γ'_𝔭`, strictly beyond the old one. -/
theorem endpoint_values (p : focusActive A C.activeTags) (h : C.core p) :
    Values.vrv (C.contractedValue p) = C.cutoff p ∧
    Values.vrv (I.target.contractedValue p) = I.target.cutoff p ∧
    C.cutoff p < I.target.cutoff p := by
  obtain ⟨d,h₁,h₂⟩ := I.released_nonempty p h
  exact ⟨C.contractedValue_vrv p,I.target.contractedValue_vrv p,h₁.trans_le h₂⟩

end ApertureIncrease
end ContractedApertureData
end DiamondIntegral.Section6
