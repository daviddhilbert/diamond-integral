import «section 7».TwoCellGeometry
import «section 6».ShearContractionStages
import «section 6».SpecialCovariantChains
import «section 6».CentripetalHomeomorphism
import «section 6».UniformMixedRadius
import «section 6».BoundedApertureCoefficients
import «section 6».InvariantValueBounds
import «section 2».ClosedGraphCriterion

/-! Balanced translation stages (for Lemma 7.21, the balanced case).

Let `X ⊆ VF² × RV^q` be a definable set. For a label value `u`, its cell is
`X_u = {(x, y) : (x, y, u) ∈ X}` (`cell`); coordinate `0` is the base and
coordinate `1` the fibre. Suppose that `X` is proper invariant, VF-doubly
bounded and tagged, that every nonempty cell `X_u` is balanced with positioning
function `ε(u, ·)` and paradigms `t₁(u)`, `t(u)` (Definition 7.17), that the
graphs of `ε` and `t` are definable, and that the shift is genuine: `ε(u, x)`
lies in the RV-disc of `y` for `(x, y) ∈ X_u` (`BalancedShearInput`). Then
`(x, y, u) ↦ (x, y - ε(u, x))` is the first stage of a standard contraction of
`X` contracting the fibre coordinate. As the paper puts it, the translation is
centripetal with focus in the RV-disc of the changed coordinate, and for an
aperture whose cutoff exceeds `vrv(t)` the core clause never occurs.

* By Definition 7.17, `(x, y) ∈ X_u` iff `x` lies in the first projection and
  `y - ε(u, x) ∈ t(u)^♯` (`TwoCellGeometry.balanced_mem_right`). Let `δ` be a
  named uniform invariance radius of the label fibres. The point `(x, ε(u, x))`
  is not in `X_u`, so `v(y - ε(u, x)) = vrv(t(u)) ≤ δ`
  (`BalancedShearInput.paradigm_value_le`). The values `ε(u, x)` have the
  leading terms of `y`, so they are bounded below by the double bound of `X`,
  and the support data `V ⊆ S ⊆ acl(V)` give a named coefficient `c` with
  `δ < v(c · ε(u, x))` on `X` (`TranslationRadii`, `exists_translationRadii`).
* With these, `(x, y, u) ↦ ε(u, x)` is centripetal data on the fibre coordinate
  (`translationData`, Definition 6.11). The active radius over `u` is the
  paradigm value `vrv(t(u))`, named over the labels through the graph of `t`,
  and the complementary radius is `δ`. If two points of `X_u` have bases closer
  than `δ`, both shifted values `y - ε(u, x)` and `y - ε(u, x')` lie in
  `t(u)^♯`, so the foci are closer than `vrv(t(u))` (`covariance_at`). The focus
  is continuous on each fibre because `ε(u, ·)` is `rv`-affine
  (`focus_continuousOn`).
* The core clause `v(c · ε) < v(y - ε)` never holds, since
  `v(y - ε) ≤ δ < v(c · ε)` (`translation_core_false`). Hence the point map is
  the translation `(x, y - ε(u, x))`, with the centripetal tag `branchTag false`
  in front of the old labels (`translation_point`).
* The centripetal transformation followed by regularization is a special
  covariant chain (`translationLift_chain`). It fixes `x`; its displacement
  `-ε(u, x)` depends only on the labels and `x`; and its target is the full
  RV-disc bundle over its contracted set, with leading label `rv(y - ε(u, x))`,
  because `d + ε(u, x) ∈ X_u` whenever `rv(d) = t(u)` (`translation_bundle`).
  Section 6 `shear_contraction_stage_of_bundle` turns it into a standard
  contraction stage (`translationStage`).
* The lift sends `(x, y, u)` to `(x, y - ε(u, x))` with labels
  `(rv(x), t(u), branchTag false, u)`; the old labels are the last `q` and the
  leading label is the second (`translationStage_lift_value`). The contracted
  set consists of the points `(x, rv(x), t(u), branchTag false, u)` with
  `(x, y, u) ∈ X` for some `y` (`mem_translationStage_contracted`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BalancedShearStages
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.TwoCells DiamondIntegral.Section7.TwoCellGeometry

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Valuation helpers -/

omit [M ⊨ Axioms.ACVF] in
theorem vec_two {α : Type} (a : Fin 2 → α) : ![a 0, a 1] = a := by
  funext i
  fin_cases i <;> rfl

/-- Equal leading terms: the difference is strictly smaller than either term. -/
theorem value_lt_sub_of_rv_eq {a b : VF M} (hb : b ≠ 0) (h : rv M a = rv M b) :
    vfValue b < vfValue (a - b) := by
  have h' : iRv a.val = iRv b.val := congrArg Subtype.val h
  rw [CanonicalRV.encoded_eq_iff_close a.property b.property (fun h => hb (Subtype.ext h))] at h'
  change ¬ VFValued.predV b (a - b) at h'
  rw [Values.vf_pred_iff_gamma_le] at h'
  exact lt_of_not_ge h'

/-- Multiplication by a finite value is strictly monotone. -/
theorem gammaTop_mul_lt_mul {c a b : GammaInfinity M} (hc : c ≠ 0) (h : a < b) : c * a < c * b := by
  refine lt_of_le_of_ne (mul_le_mul' le_rfl h.le) ?_
  intro he
  exact h.ne (mul_left_cancel₀ hc he)

/-- The finite value of a nonzero RV element. -/
def rvRadius (w : RV M) : Gamma M :=
  ⟨Values.vrv w.val, fun h => w.property (Subtype.ext ((Values.vrv_eq_infinity_iff w.val).mp h))⟩

theorem rvRadius_val (w : RV M) : (rvRadius w).val = Values.vrv w.val := rfl

theorem vfValue_of_rv_eq {a : VF M} {w : RVInfinity M} (h : rv M a = w) : vfValue a = Values.vrv w := by
  rw [vfValue, h]

/-- A nonzero RV element named over a base has a named value over that base. -/
theorem rvRadius_named {B : Set M} (w : RV M) (hw : B.Definable₁ LRV {w.val.val}) :
    B.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {rvRadius w}} := by
  let t := w.val.val
  have ht : GammaParameters.NonzeroRV t := ⟨w.val.property, fun he => w.property (Subtype.ext he)⟩
  have hval : GammaParameters.codeValue t = rvRadius w :=
    Subtype.ext (nonzero_rv_codeValue_val w.val w.property)
  rw [← hval]
  have hφ : B.DefinableMap LRV (fun z : Fin 1 → M => ![z 0, t]) := by
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact definable_named_constant t hw
  have h := (GammaParameters.same_scalar_definable B).preimage_map hφ
  convert h using 1
  ext z
  constructor
  · intro hz
    have hNZ : GammaParameters.NonzeroRV (z 0) := ⟨hz.1, hz.2.1⟩
    have he : GammaParameters.codeValue (z 0) = GammaParameters.codeValue t :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hNZ).mp hz
    exact ⟨hNZ, ht, (GammaParameters.original_le_codeValue_iff _ _ hNZ ht).mpr he.le,
      (GammaParameters.original_le_codeValue_iff _ _ ht hNZ).mpr he.ge⟩
  · rintro ⟨hz, _, hlt, htl⟩
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hz).mpr
      (le_antisymm ((GammaParameters.original_le_codeValue_iff _ _ hz ht).mp hlt)
        ((GammaParameters.original_le_codeValue_iff _ _ ht hz).mp htl))

variable {S : Set M} {q : ℕ}

/-! ### Cells and the input -/

/-- The cell of `X` over the label value `u`. Coordinate `0` is the base and
coordinate `1` the fibre. -/
def cell (X : DefSet (rawMixedSpace (M := M) 2 q) S) (u : Fin q → RVInfinity M) : Set (VF M × VF M) :=
  {p | (![p.1, p.2], u) ∈ X.carrier}

omit [M ⊨ Axioms.ACVF] in
theorem mem_cell_iff {X : DefSet (rawMixedSpace (M := M) 2 q) S} {u : Fin q → RVInfinity M}
    (a : Fin 2 → VF M) : (a 0, a 1) ∈ cell X u ↔ (a, u) ∈ X.carrier := by
  change (![a 0, a 1], u) ∈ X.carrier ↔ _
  rw [vec_two]

/-- **The input of the balanced translation.** `X ⊆ VF² × RV^q` is proper
invariant, VF-doubly bounded and tagged; the positioning functions `ε(u, ·)` and
the paradigms `t(u)` have definable graphs; every nonempty cell is balanced with
positioning function `ε(u, ·)` and paradigms `t₁(u)`, `t(u)`; and the shift is
genuine: `ε(u, x)` lies in the RV-disc of `y`. -/
structure BalancedShearInput (X : DefSet (rawMixedSpace (M := M) 2 q) S)
    (ε : (Fin q → RVInfinity M) → VF M → VF M) (t : (Fin q → RVInfinity M) → RV M)
    (t₁ : (Fin q → RVInfinity M) → RVInfinity M) : Prop where
  proper : ProperInvariant S X.carrier
  doublyBounded : VFDoublyBounded X.carrier
  tagged : ∀ p ∈ X.carrier, ∀ p' ∈ X.carrier, p.2 = p'.2 → tupleRV M p.1 = tupleRV M p'.1
  focusGraph : S.Definable LRV {z : Fin (2 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
    z = Fin.append ![x.val, (ε u x).val] (rvValues u)}
  paradigmGraph : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
    z = Fin.append ![(t u).val.val] (rvValues u)}
  balanced : ∀ u, (cell X u).Nonempty → Balanced (cell X u) (ε u) (t₁ u) (t u).val
  genuine : ∀ u, ∀ p ∈ cell X u, rv M (ε u p.1) = rv M p.2

namespace BalancedShearInput

variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- Membership in a nonempty label fibre (`TwoCellGeometry.balanced_mem_right`). -/
theorem mem_iff (H : BalancedShearInput X ε t t₁) {u : Fin q → RVInfinity M} {a : Fin 2 → VF M}
    (ha : (a, u) ∈ X.carrier) (b : Fin 2 → VF M) :
    (b, u) ∈ X.carrier ↔ b 0 ∈ first (cell X u) ∧ b 1 - ε u (b 0) ∈ sharpSet (t u).val := by
  have hne : (cell X u).Nonempty := ⟨(a 0, a 1), (mem_cell_iff a).mpr ha⟩
  rw [← mem_cell_iff b]
  exact balanced_mem_right (H.balanced u hne) (b 0) (b 1)

omit [M ⊨ Axioms.ACVF] in
theorem base_mem_first {u : Fin q → RVInfinity M} {a : Fin 2 → VF M} (ha : (a, u) ∈ X.carrier) :
    a 0 ∈ first (cell X u) :=
  ⟨(a 0, a 1), (mem_cell_iff a).mpr ha, rfl⟩

/-- The shifted fibre coordinate lies in `t(u)^♯`. -/
theorem shift_rv (H : BalancedShearInput X ε t t₁) {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    rv M (p.1 1 - ε p.2 (p.1 0)) = (t p.2).val :=
  ((H.mem_iff hp p.1).mp hp).2

theorem shift_value (H : BalancedShearInput X ε t t₁) {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    vfValue (p.1 1 - ε p.2 (p.1 0)) = (rvRadius (t p.2)).val :=
  vfValue_of_rv_eq (H.shift_rv hp)

theorem shift_ne_zero (H : BalancedShearInput X ε t t₁) {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    p.1 1 - ε p.2 (p.1 0) ≠ 0 := by
  intro he
  have h := H.shift_rv hp
  rw [he, rv_zero] at h
  exact (t p.2).property h.symm

/-- The genuine shift: `ε(u, x)` and `y` have the same leading term. -/
theorem focus_rv (H : BalancedShearInput X ε t t₁) {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    rv M (ε p.2 (p.1 0)) = rv M (p.1 1) :=
  H.genuine p.2 (p.1 0, p.1 1) ((mem_cell_iff p.1).mpr hp)

/-- A fibre that is `δ`-invariant has paradigm value at most `δ`. -/
theorem paradigm_value_le (H : BalancedShearInput X ε t t₁) {δ : Gamma M}
    (hδ : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre X.carrier u))
    {p : Mixed M 2 q} (hp : p ∈ X.carrier) : vfValue (p.1 1 - ε p.2 (p.1 0)) ≤ δ.val := by
  by_contra hn
  have hlt : δ.val < vfValue (p.1 1 - ε p.2 (p.1 0)) := lt_of_not_ge hn
  let b : Fin 2 → VF M := Function.update p.1 1 (ε p.2 (p.1 0))
  have hClose : Congruent (fun _ => δ) p.1 b := by
    intro i
    by_cases hi : i = 1
    · subst hi
      change δ.val < vfValue (p.1 1 - Function.update p.1 1 (ε p.2 (p.1 0)) 1)
      rw [Function.update_self]
      exact hlt
    · change δ.val < vfValue (p.1 i - Function.update p.1 1 (ε p.2 (p.1 0)) i)
      rw [Function.update_of_ne hi, sub_self]
      exact gamma_lt_value_zero δ
  have hb : (b, p.2) ∈ X.carrier := (hδ p.2 p.1 b hClose).mp hp
  have h := H.shift_rv (p := (b, p.2)) hb
  have hb0 : b 0 = p.1 0 := Function.update_of_ne (by decide) _ _
  have hb1 : b 1 = ε p.2 (p.1 0) := Function.update_self _ _ _
  change rv M (b 1 - ε p.2 (b 0)) = (t p.2).val at h
  rw [hb0, hb1, sub_self, rv_zero] at h
  exact (t p.2).property h.symm

/-- The values `ε(u, x)` on `X` form a definable subset of `VF`. -/
theorem focusValues_definable (H : BalancedShearInput X ε t t₁) :
    S.Definable₁ LRV (Subtype.val '' {w : VF M | ∃ p ∈ X.carrier, w = ε p.2 (p.1 0)}) := by
  change S.Definable LRV
    {z : Fin 1 → M | z 0 ∈ Subtype.val '' {w : VF M | ∃ p ∈ X.carrier, w = ε p.2 (p.1 0)}}
  convert H.focusGraph.image_comp (fun _ : Fin 1 => Fin.castAdd q (1 : Fin 2)) using 1
  ext z
  constructor
  · rintro ⟨w, ⟨p, hp, rfl⟩, hz⟩
    refine ⟨Fin.append ![(p.1 0).val, (ε p.2 (p.1 0)).val] (rvValues p.2),
      ⟨p.2, p.1 0, ⟨p.1 1, by rw [vec_two]; exact hp⟩, rfl⟩, ?_⟩
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp only [Function.comp_apply, Fin.append_left]
    exact hz
  · rintro ⟨g, ⟨u, x, ⟨y, hxy⟩, rfl⟩, rfl⟩
    refine ⟨ε u x, ⟨(![x, y], u), hxy, rfl⟩, ?_⟩
    simp only [Function.comp_apply, Fin.append_left]
    rfl

/-- The paradigm value `vrv(t(u))` is named over the labels `u` of a nonempty
fibre (from the definable graph of `t`). -/
theorem paradigm_named (H : BalancedShearInput X ε t t₁) (u : Fin q → RVInfinity M)
    (hne : (vfFibre X.carrier u).Nonempty) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {rvRadius (t u)}} := by
  apply rvRadius_named
  obtain ⟨a, ha⟩ := hne
  let fix : (Fin 1 → M) → Fin (1 + q) → M := fun z => Fin.append (fun _ : Fin 1 => z 0) (rvValues u)
  have hfix : (S ∪ Set.range (rvValues u)).DefinableMap LRV fix := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [fix, Fin.append_left]
      exact Set.DefinableFun.proj LRV
    · simp only [fix, Fin.append_right]
      exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
  have h := (H.paradigmGraph.mono Set.subset_union_left).preimage_map hfix
  change (S ∪ Set.range (rvValues u)).Definable LRV {z : Fin 1 → M | z 0 ∈ ({(t u).val.val} : Set M)}
  convert h using 1
  ext z
  constructor
  · intro hz
    refine ⟨u, a 0, ⟨a 1, by rw [vec_two]; exact ha⟩, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.fin_one_eq_zero j]
      simp only [fix, Fin.append_left]
      exact hz
    · simp only [fix, Fin.append_right]
  · rintro ⟨u', x, _, hz⟩
    have hu : u' = u := by
      funext j
      apply Subtype.ext
      have h1 := congrFun hz (Fin.natAdd 1 j)
      simp only [fix, Fin.append_right] at h1
      exact h1.symm
    subst hu
    have h0 := congrFun hz (Fin.castAdd q 0)
    simp only [fix, Fin.append_left] at h0
    exact h0

end BalancedShearInput

/-! ### The radii -/

/-- **The radii of the translation.** A named uniform invariance radius `δ` of
the label fibres, and a named coefficient `c` with `δ < v(c · ε(u, x))` at every
point `(x, y, u)` of `X`. -/
structure TranslationRadii (X : DefSet (rawMixedSpace (M := M) 2 q) S)
    (ε : (Fin q → RVInfinity M) → VF M → VF M) where
  radius : Gamma M
  radius_named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {radius}}
  invariant : ∀ u, AlphaInvariant (fun _ => radius) (vfFibre X.carrier u)
  coefficient : VF M
  coefficient_nonzero : coefficient ≠ 0
  coefficient_nonnegative : (1 : GammaInfinity M) ≤ vfValue coefficient
  coefficient_definable : S.Definable₁ LRV {coefficient.val}
  dominates : ∀ p ∈ X.carrier, radius.val < vfValue (coefficient * ε p.2 (p.1 0))

section Radii

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- **Existence of the radii.** The radius is the uniform invariance radius of
`X` (Section 6 `properInvariant_uniform_named_radius`). The values `ε(u, x)` have
the leading terms of `y`, so they are bounded below by the double bound of `X`;
Section 6 `exists_named_aperture_coefficient_of_lowerBound` then names `c`. -/
theorem exists_translationRadii
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (H : BalancedShearInput X ε t t₁) : Nonempty (TranslationRadii X ε) := by
  obtain ⟨δ, hδ, -, hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H.proper
  obtain ⟨γ, hγ⟩ := H.doublyBounded
  have hLower : ∀ a ∈ {w : VF M | ∃ p ∈ X.carrier, w = ε p.2 (p.1 0)}, (γ⁻¹).val ≤ vfValue a := by
    rintro _ ⟨p, hp, rfl⟩
    rw [vfValue, H.focus_rv hp]
    exact (hγ p hp 1).1
  obtain ⟨c, hc0, hc1, hcdef, hcbig⟩ := exists_named_aperture_coefficient_of_lowerBound Valued.v hv hc h00
    V S hV hVS hSV hnt _ H.focusValues_definable γ⁻¹ hLower δ hδ
  exact ⟨{
    radius := δ
    radius_named := hδ
    invariant := hInv
    coefficient := c
    coefficient_nonzero := hc0
    coefficient_nonnegative := hc1
    coefficient_definable := hcdef
    dominates := fun p hp => hcbig _ ⟨p, hp, rfl⟩ }⟩

/-- Radii chosen from the support data (`exists_translationRadii`). -/
def chosenRadii
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (H : BalancedShearInput X ε t t₁) : TranslationRadii X ε :=
  Classical.choice (exists_translationRadii (G := G) h00 hc linear hκ hs hv hsmall hΓ V hV hVS hSV hnt H)

end Radii

/-! ### The focus map -/

omit [M ⊨ Axioms.ACVF] in
theorem update_one_zero {α : Type} (x : Fin 2 → α) (c : α) : Function.update x 1 c 0 = x 0 :=
  Function.update_of_ne (by decide) _ _

/-- The focus `(x, y, u) ↦ ε(u, x)` as a definable map on `X` (all labels active). -/
def focusMap (X : DefSet (rawMixedSpace (M := M) 2 q) S) (ε : (Fin q → RVInfinity M) → VF M → VF M)
    (hG : S.Definable LRV {z : Fin (2 + q) → M | ∃ u x, (∃ y, (![x, y], u) ∈ X.carrier) ∧
      z = Fin.append ![x.val, (ε u x).val] (rvValues u)}) :
    Map (focusActive X (DefSet.univ (rawRVSpace (M := M) q) S)) (DefSet.univ (rawVFSpace (M := M) 1) S) where
  toFun p := ⟨fun _ => ε p.val.2 (p.val.1 0), Set.mem_univ _⟩
  graph_definable := by
    let P := rawMixedSpace (M := M) 2 q
    let Q := rawVFSpace (M := M) 1
    let ρ : Fin (2 + q) → P.Index ⊕ Q.Index :=
      Fin.append ![Sum.inl (Sum.inl (0 : Fin 2)), Sum.inr (0 : Fin 1)] (fun j => Sum.inl (Sum.inr j))
    have hX : S.Definable LRV (P.preimage X.carrier) := X.definable
    have h := (hX.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)).inter
      (hG.preimage_comp ρ)
    change S.Definable LRV (P.relation Q _)
    convert h using 1
    ext z
    constructor
    · rintro ⟨hx, hy, a, ha, hay⟩
      have hbX : P.decode ⟨z ∘ Sum.inl, hx⟩ ∈ X.carrier := ha ▸ a.property.1
      have hay' : (fun _ : Fin 1 => ε (P.decode ⟨z ∘ Sum.inl, hx⟩).2 ((P.decode ⟨z ∘ Sum.inl, hx⟩).1 0)) =
          Q.decode ⟨z ∘ Sum.inr, hy⟩ := by
        rw [← ha]
        exact hay
      have hcx : mixedValues (P.decode ⟨z ∘ Sum.inl, hx⟩) = z ∘ Sum.inl := mixedValues_decode ⟨_, hx⟩
      have hcy : vfValues (Q.decode ⟨z ∘ Sum.inr, hy⟩) = z ∘ Sum.inr :=
        Space.ofEmbedding_decode vfValues vfValues_injective (rawVFSpace (M := M) 1).domain_definable ⟨_, hy⟩
      have hy0 : z (Sum.inr (0 : Fin 1)) = (ε (P.decode ⟨z ∘ Sum.inl, hx⟩).2 ((P.decode ⟨z ∘ Sum.inl, hx⟩).1 0)).val := by
        have h1 := congrFun hcy (0 : Fin 1)
        rw [← hay'] at h1
        exact h1.symm
      refine ⟨⟨hx, hbX⟩, (P.decode ⟨z ∘ Sum.inl, hx⟩).2, (P.decode ⟨z ∘ Sum.inl, hx⟩).1 0,
        ⟨(P.decode ⟨z ∘ Sum.inl, hx⟩).1 1, by rw [vec_two]; exact hbX⟩, ?_⟩
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · fin_cases j
        · simp only [ρ, Function.comp_apply, Fin.append_left]
          exact (congrFun hcx (Sum.inl 0)).symm
        · simp only [ρ, Function.comp_apply, Fin.append_left]
          exact hy0
      · simp only [ρ, Function.comp_apply, Fin.append_right]
        exact (congrFun hcx (Sum.inr j)).symm
    · rintro ⟨⟨hx, hxX⟩, u, x₀, ⟨y₀, _⟩, hz⟩
      have hcx : mixedValues (P.decode ⟨z ∘ Sum.inl, hx⟩) = z ∘ Sum.inl := mixedValues_decode ⟨_, hx⟩
      have hz0 := congrFun hz (Fin.castAdd q 0)
      have hz1 := congrFun hz (Fin.castAdd q 1)
      simp only [ρ, Function.comp_apply, Fin.append_left, Matrix.cons_val_zero, Matrix.cons_val_one] at hz0 hz1
      have hb0 : (P.decode ⟨z ∘ Sum.inl, hx⟩).1 0 = x₀ :=
        Subtype.ext ((congrFun hcx (Sum.inl 0)).trans hz0)
      have hbu : (P.decode ⟨z ∘ Sum.inl, hx⟩).2 = u := by
        funext j
        apply Subtype.ext
        have hzj := congrFun hz (Fin.natAdd 2 j)
        simp only [ρ, Function.comp_apply, Fin.append_right] at hzj
        exact (congrFun hcx (Sum.inr j)).trans hzj
      have hy : z ∘ Sum.inr ∈ Q.domain := ⟨fun _ => ε u x₀, by
        funext i
        rw [Fin.fin_one_eq_zero i]
        exact hz1.symm⟩
      have hcy : vfValues (Q.decode ⟨z ∘ Sum.inr, hy⟩) = z ∘ Sum.inr :=
        Space.ofEmbedding_decode vfValues vfValues_injective (rawVFSpace (M := M) 1).domain_definable ⟨_, hy⟩
      refine ⟨hx, hy, ⟨P.decode ⟨z ∘ Sum.inl, hx⟩, hxX, Set.mem_univ _⟩, rfl, ?_⟩
      apply vfValues_injective
      rw [hcy]
      funext i
      rw [Fin.fin_one_eq_zero i]
      change (ε (P.decode ⟨z ∘ Sum.inl, hx⟩).2 ((P.decode ⟨z ∘ Sum.inl, hx⟩).1 0)).val = z (Sum.inr (0 : Fin 1))
      rw [hb0, hbu]
      exact hz1.symm

/-! ### The centripetal data -/

section Data

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

theorem vfValue_sub_comm' (a b : VF M) : vfValue (a - b) = vfValue (b - a) := vfValue_sub_comm a b

/-- The focus is continuous on each label fibre: `ε(u, ·)` is `rv`-affine on
the first projection of the cell (Definition 7.17), so it multiplies
valuative distances by the value of its slope. -/
theorem focus_continuousOn (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (H : BalancedShearInput X ε t t₁) (u : Fin q → RVInfinity M) :
    ContinuousOn (fun x : Fin 2 → VF M => ε u (Function.update x 1 0 0)) (vfFibre X.carrier u) := by
  have hfun : (fun x : Fin 2 → VF M => ε u (Function.update x 1 0 0)) = fun x => ε u (x 0) := by
    funext x
    rw [update_one_zero]
  rw [hfun]
  by_cases hne : (vfFibre X.carrier u).Nonempty
  · obtain ⟨a₀, ha₀⟩ := hne
    have hcell : (cell X u).Nonempty := ⟨(a₀ 0, a₀ 1), (mem_cell_iff a₀).mpr ha₀⟩
    obtain ⟨_, _, s, hs⟩ := (H.balanced u hcell).rvAffine
    let σ := rvRadius s
    have hσ : σ.val ≠ 0 := fun h => σ.property (h.trans Values.infinity_eq_zero.symm)
    have hpair : ContinuousOn (fun x : Fin 2 → VF M => fun _ : Fin 1 => ε u (x 0)) (vfFibre X.carrier u) := by
      intro a ha
      apply (continuousWithinAt_iff_vfBalls hv _ _ a).mpr
      intro η
      refine ⟨η * σ⁻¹, fun x hx hxa _ => ?_⟩
      have h0 : (η * σ⁻¹).val < vfValue (x 0 - a 0) := hxa 0
      change η.val < vfValue (ε u (x 0) - ε u (a 0))
      rw [vfValue_of_rv_eq (hs (x 0) (BalancedShearInput.base_mem_first hx) (a 0)
        (BalancedShearInput.base_mem_first ha)), RVOperations.vrv_mul]
      have he : η.val = σ.val * (η * σ⁻¹).val := by
        rw [show (η * σ⁻¹).val = η.val * σ.val⁻¹ from rfl, mul_comm η.val, ← mul_assoc,
          mul_inv_cancel₀ hσ, one_mul]
      rw [he]
      exact gammaTop_mul_lt_mul hσ h0
    exact (continuous_apply 0).comp_continuousOn hpair
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact continuousOn_empty _

/-- The covariance clause of Definition 6.11 for the translation. The active
radius is the paradigm value `vrv(t(u))` and the complementary radius is `δ`:
moving the base by more than `δ` keeps the point in the fibre, so the two
shifted values lie in `t(u)^♯` and the focus moves by less than `vrv(t(u))`.
The aperture clause holds since `vrv(t(u)) ≤ δ < v(c · ε)`. -/
theorem covariance_at (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε)
    (u : Fin q → RVInfinity M) : ∃ α : Gamma M, ∃ β : Fin 2 → Gamma M,
      (S ∪ Set.range (rvValues u)).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}} ∧
      NamedGammaTuple (S ∪ Set.range (rvValues u)) β ∧
      AlphaInvariant (fun i => if i = 1 then α else β i) (vfFibre X.carrier u) ∧
      (∀ a ∈ vfFibre X.carrier u, ∀ b ∈ vfFibre X.carrier u,
        Congruent β (Function.update a 1 0) (Function.update b 1 0) →
          α.val < vfValue (ε u (Function.update a 1 0 0) - ε u (Function.update b 1 0 0))) ∧
      (∀ a ∈ vfFibre X.carrier u, α.val ≤ vfValue (R.coefficient * ε u (Function.update a 1 0 0))) := by
  by_cases hne : (vfFibre X.carrier u).Nonempty
  · refine ⟨rvRadius (t u), fun _ => R.radius, H.paradigm_named u hne,
      fun _ => R.radius_named.mono Set.subset_union_left, ?_, ?_, ?_⟩
    · apply AlphaInvariant.combine_coordinate_radius R.radius R.radius (rvRadius (t u)) 1
        (R.invariant u) le_rfl
      intro a ha x hx
      have hrv : rv M (a 1 - ε u (a 0)) = (t u).val := H.shift_rv (p := (a, u)) ha
      have hb0 : a 1 - ε u (a 0) ≠ 0 := H.shift_ne_zero (p := (a, u)) ha
      have hval : vfValue (a 1 - ε u (a 0)) = (rvRadius (t u)).val := H.shift_value (p := (a, u)) ha
      have hnew : rv M (x - ε u (a 0)) = (t u).val := by
        rw [← hrv]
        apply rv_eq_of_value_close hb0
        rw [hval, show x - ε u (a 0) - (a 1 - ε u (a 0)) = x - a 1 by abel, vfValue_sub_comm']
        exact hx
      apply (H.mem_iff ha (Function.update a 1 x)).mpr
      rw [Function.update_self, update_one_zero]
      exact ⟨BalancedShearInput.base_mem_first ha, hnew⟩
    · intro a ha b hb hab
      rw [update_one_zero, update_one_zero]
      have h0 : R.radius.val < vfValue (a 0 - b 0) := by
        have h := hab 0
        change R.radius.val < vfValue (Function.update a 1 0 0 - Function.update b 1 0 0) at h
        rwa [update_one_zero, update_one_zero] at h
      let a' : Fin 2 → VF M := Function.update a 0 (b 0)
      have hClose : Congruent (fun _ => R.radius) a a' := by
        intro i
        by_cases hi : i = 0
        · subst hi
          change R.radius.val < vfValue (a 0 - Function.update a 0 (b 0) 0)
          rw [Function.update_self]
          exact h0
        · change R.radius.val < vfValue (a i - Function.update a 0 (b 0) i)
          rw [Function.update_of_ne hi, sub_self]
          exact gamma_lt_value_zero _
      have ha' : (a', u) ∈ X.carrier := (R.invariant u a a' hClose).mp ha
      have h1 : rv M (a' 1 - ε u (a' 0)) = (t u).val := H.shift_rv (p := (a', u)) ha'
      have ha'0 : a' 0 = b 0 := Function.update_self _ _ _
      have ha'1 : a' 1 = a 1 := Function.update_of_ne (by decide) _ _
      rw [ha'0, ha'1] at h1
      have h2 : rv M (a 1 - ε u (a 0)) = (t u).val := H.shift_rv (p := (a, u)) ha
      have hlt := value_lt_sub_of_rv_eq (H.shift_ne_zero (p := (a, u)) ha) (h1.trans h2.symm)
      have hval : vfValue (a 1 - ε u (a 0)) = (rvRadius (t u)).val := H.shift_value (p := (a, u)) ha
      rw [hval, show a 1 - ε u (b 0) - (a 1 - ε u (a 0)) = ε u (a 0) - ε u (b 0) by abel] at hlt
      exact hlt
    · intro a ha
      rw [update_one_zero]
      have hval : vfValue (a 1 - ε u (a 0)) = (rvRadius (t u)).val := H.shift_value (p := (a, u)) ha
      rw [← hval]
      exact (H.paradigm_value_le R.invariant (p := (a, u)) ha).trans (R.dominates (a, u) ha).le
  · have hempty : ∀ a, a ∉ vfFibre X.carrier u := fun a ha => hne ⟨a, ha⟩
    refine ⟨R.radius, fun _ => R.radius, R.radius_named.mono Set.subset_union_left,
      fun _ => R.radius_named.mono Set.subset_union_left, ?_, ?_, ?_⟩
    · intro a b _
      exact ⟨fun h => (hempty a h).elim, fun h => (hempty b h).elim⟩
    · intro a ha
      exact (hempty a ha).elim
    · intro a ha
      exact (hempty a ha).elim

/-- **The translation as centripetal data** (Definition 6.11). The changed
coordinate is the fibre coordinate `1`, every label is active, the focus is
`ε(u, x)`, and the coefficient is that of the radii `R`. -/
def translationData (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε) : CentripetalData (G := G) X where
  coordinate := 1
  activeTags := DefSet.univ (rawRVSpace (M := M) q) S
  focus x u := ε u (x 0)
  focusMap := focusMap X ε H.focusGraph
  focusMap_eq p := by
    change ε p.val.2 (p.val.1 0) = ε p.val.2 (Function.update p.val.1 1 0 0)
    rw [update_one_zero]
  sourceProper := H.proper
  sourceDoublyBounded := H.doublyBounded
  tagged := H.tagged
  continuous u _ := focus_continuousOn hv H u
  focusRV p hp _ := by
    change rv M (ε p.2 (Function.update p.1 1 0 0)) = rv M (p.1 1)
    rw [update_one_zero]
    exact H.focus_rv hp
  coefficient := R.coefficient
  coefficient_nonzero := R.coefficient_nonzero
  coefficient_nonnegative := R.coefficient_nonnegative
  coefficient_definable := R.coefficient_definable
  covariance u _ := covariance_at H R u

variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε)

theorem translationData_coordinate : (translationData (G := G) hv H R).coordinate = 1 := rfl

theorem translationData_coefficient : (translationData (G := G) hv H R).coefficient = R.coefficient := rfl

theorem translationData_extendedFocus {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    (translationData (G := G) hv H R).extendedFocus p = ε p.2 (p.1 0) := by
  rw [CentripetalData.extendedFocus_active _ hp (Set.mem_univ _)]
  change ε p.2 (Function.update p.1 1 0 0) = _
  rw [update_one_zero]

/-- **The core clause never occurs**: `v(y - ε) = vrv(t) ≤ δ < v(c · ε)`. -/
theorem translation_core_false {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    (translationData (G := G) hv H R).core p = false := by
  unfold CentripetalData.core
  rw [translationData_extendedFocus hv H R hp]
  apply decide_eq_false
  change ¬ (vfValue (R.coefficient * ε p.2 (p.1 0)) < vfValue (p.1 1 - ε p.2 (p.1 0)))
  exact not_lt.mpr ((H.paradigm_value_le R.invariant hp).trans (R.dominates p hp).le)

/-- The translated VF point `(x, y - ε(u, x))`. -/
def translate (ε : (Fin q → RVInfinity M) → VF M → VF M) (p : Mixed M 2 q) : Fin 2 → VF M :=
  ![p.1 0, p.1 1 - ε p.2 (p.1 0)]

/-- **The point map is the translation** `(x, y, u) ↦ (x, y - ε(u, x), 1, u)`, with
the centripetal tag `branchTag false` in front of the old labels. -/
theorem translation_point {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    (translationData (G := G) hv H R).point p =
      (translate ε p, Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2) := by
  unfold CentripetalData.point
  rw [translation_core_false hv H R hp, translationData_extendedFocus hv H R hp]
  apply Prod.ext
  · funext i
    fin_cases i
    · rfl
    · change Function.update p.1 1 (p.1 1 - ε p.2 (p.1 0) + if false = true then _ else 0) 1 = _
      rw [Function.update_self]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      rfl
  · rfl

theorem translation_point_fst {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    ((translationData (G := G) hv H R).point p).1 = ![p.1 0, p.1 1 - ε p.2 (p.1 0)] := by
  rw [translation_point hv H R hp]
  rfl

end Data

/-! ### The lift: translation followed by regularization -/

section Lift

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε)

/-- The target of the translation stage: the regularized image of the translation. -/
def translationTarget : DefSet (rawMixedSpace (M := M) 2 (2 + (1 + q))) S :=
  (regularizeMap (translationData (G := G) hv H R).map.image).image

/-- The labels of the translation stage at `p`: the leading terms of the
translated point (regularization), the centripetal tag, the old labels. -/
def translationLabels (ε : (Fin q → RVInfinity M) → VF M → VF M) (p : Mixed M 2 q) :
    Fin (2 + (1 + q)) → RVInfinity M :=
  Fin.append (tupleRV M (translate ε p)) (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2)

/-- On `X` the labels are `(rv(x), t(u), branchTag false, u)`. -/
theorem translationLabels_eq (H : BalancedShearInput X ε t t₁) {p : Mixed M 2 q} (hp : p ∈ X.carrier) :
    translationLabels ε p =
      Fin.append ![rv M (p.1 0), (t p.2).val] (Fin.append ![branchTag (M := M) false] p.2) := by
  unfold translationLabels
  congr 1
  · funext i
    fin_cases i
    · rfl
    · exact H.shift_rv hp
  · congr 1
    funext i
    fin_cases i
    rfl

/-- The centripetal translation followed by regularization. -/
def translationLift : Map X (translationTarget (G := G) hv H R) :=
  (regularization (translationData (G := G) hv H R).map.image).comp (translationData hv H R).bijection

theorem translationLift_apply (p : X) :
    (translationLift (G := G) hv H R p).val = (translate ε p.val, translationLabels ε p.val) := by
  change regularize ((translationData (G := G) hv H R).point p.val) = _
  rw [translation_point hv H R p.property]
  rfl

theorem mem_translationTarget_iff (z : Mixed M 2 (2 + (1 + q))) :
    z ∈ (translationTarget (G := G) hv H R).carrier ↔
      ∃ p ∈ X.carrier, z = (translate ε p, translationLabels ε p) := by
  change z ∈ (regularizeMap _).image.carrier ↔ _
  rw [regularization_carrier, CentripetalData.image_carrier]
  constructor
  · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [translation_point hv H R hp]; rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, by rw [translation_point hv H R hp]; rfl⟩

/-- The lift is a special covariant chain: the centripetal transformation
followed by regularization (Section 6 `SpecialCovariantChain`). -/
theorem translationLift_chain (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) :
    SpecialCovariantChain (G := G) X (translationTarget hv H R) (translationLift hv H R) :=
  .comp (.centripetal X (translationData hv H R))
    (.regularize _ ((translationData hv H R).image_properInvariant h00 hc hκ hs hv)
      (translationData hv H R).image_vfDoublyBounded)

theorem translationLift_home (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M)) :
    ProperCovariantHomeomorphism (translationLift (G := G) hv H R) :=
  (translationLift_chain hv H R h00 hc hκ hs).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ

/-- The base coordinate is fixed. -/
theorem translationLift_relative (p : X) (i : Fin 1) :
    (translationLift (G := G) hv H R p).val.1 i.castSucc = p.val.1 i.castSucc := by
  rw [translationLift_apply, Fin.fin_one_eq_zero i]
  rfl

/-- The displacement `-ε(u, x)` depends only on the labels and the base. -/
theorem translationLift_displacement :
    SameLabelShearDisplacement (translationLift (G := G) hv H R) (Fin.last 1) := by
  intro p p' hlab _ hother
  rw [translationLift_apply, translationLift_apply]
  have h0 : p.val.1 0 = p'.val.1 0 := hother 0 (by decide)
  change (p.val.1 1 - ε p.val.2 (p.val.1 0)) - p.val.1 1 =
    (p'.val.1 1 - ε p'.val.2 (p'.val.1 0)) - p'.val.1 1
  rw [hlab, h0]
  abel

theorem translationLift_retained (p : X) (i : Fin q) :
    (translationLift (G := G) hv H R p).val.2 (Fin.natAdd 2 (Fin.natAdd 1 i)) = p.val.2 i := by
  rw [translationLift_apply]
  simp only [translationLabels, Fin.append_right]

/-- The target is the full RV-disc bundle over its contracted set, with leading
label `rv(y - ε)`: replacing `y - ε` by any `d` with the same leading term stays
in the target, because `d ∈ t(u)^♯` (`TwoCellGeometry.balanced_mem_right`). -/
theorem translation_bundle :
    (translationTarget (G := G) hv H R).carrier =
      (rvCoordinateBundle (vfDropLast (translationTarget (G := G) hv H R)).image
        (Fin.castAdd (1 + q) 1)).carrier := by
  apply coordinate_bundle_of_replacement
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := (mem_translationTarget_iff hv H R z).mp hz
    change rv M (translate ε p (Fin.last 1)) =
      Fin.append (tupleRV M (translate ε p)) (Fin.append (fun _ : Fin 1 => branchTag (M := M) false) p.2)
        (Fin.castAdd (1 + q) 1)
    rw [Fin.append_left]
    rfl
  · intro z hz d hd
    obtain ⟨p, hp, rfl⟩ := (mem_translationTarget_iff hv H R z).mp hz
    have hd' : rv M d = rv M (p.1 1 - ε p.2 (p.1 0)) := hd
    let p' : Mixed M 2 q := (Function.update p.1 1 (d + ε p.2 (p.1 0)), p.2)
    have h0 : p'.1 0 = p.1 0 := update_one_zero p.1 (d + ε p.2 (p.1 0))
    have h1 : p'.1 1 = d + ε p.2 (p.1 0) := Function.update_self (1 : Fin 2) (d + ε p.2 (p.1 0)) p.1
    have hp' : p' ∈ X.carrier := by
      apply (H.mem_iff hp p'.1).mpr
      change p'.1 0 ∈ first (cell X p.2) ∧ p'.1 1 - ε p.2 (p'.1 0) ∈ sharpSet (t p.2).val
      rw [h0, h1, add_sub_cancel_right]
      exact ⟨BalancedShearInput.base_mem_first hp, hd'.trans (H.shift_rv hp)⟩
    apply (mem_translationTarget_iff hv H R _).mpr
    refine ⟨p', hp', ?_⟩
    have htr : translate ε p' = Function.update (translate ε p) (Fin.last 1) d := by
      funext i
      fin_cases i
      · change p'.1 0 = Function.update (translate ε p) (Fin.last 1) d 0
        rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ Fin.last 1), h0]
        rfl
      · change p'.1 1 - ε p.2 (p'.1 0) = Function.update (translate ε p) (Fin.last 1) d (Fin.last 1)
        rw [Function.update_self, h0, h1, add_sub_cancel_right]
    apply Prod.ext htr.symm
    change Fin.append (tupleRV M (translate ε p)) _ = Fin.append (tupleRV M (translate ε p')) _
    congr 1
    funext i
    fin_cases i
    · change rv M (p.1 0) = rv M (p'.1 0)
      rw [h0]
    · change rv M (p.1 1 - ε p.2 (p.1 0)) = rv M (p'.1 1 - ε p.2 (p'.1 0))
      rw [h0, h1, add_sub_cancel_right]
      exact hd'.symm

end Lift

/-! ### The translation stage -/

section Stage

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- **The translation stage** `(x, y, u) ↦ (x, y - ε(u, x))` of a standard
contraction of `X` contracting the fibre coordinate (Section 6
`shear_contraction_stage_of_bundle`). Its labels are
`(rv(x), rv(y - ε(u, x)), branchTag false, u)`; the old labels are the last `q`
and the leading label is `rv(y - ε(u, x)) = t(u)`. -/
def translationStage (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε) : StandardContractionStage (G := G) X :=
  (shear_contraction_stage_of_bundle (n := 1) h00 hc linear hκ hs hv hsmall hΓ (translationLift hv H R)
    (translationLift_home hv H R h00 hc linear hκ hs hsmall hΓ)
    (regularized_vfDoublyBounded (translationData hv H R).image_vfDoublyBounded)
    (translationLift_relative hv H R) (translationLift_displacement hv H R)
    (fun i => Fin.natAdd 2 (Fin.natAdd 1 i))
    ((Fin.natAdd_injective (1 + q) 2).comp (Fin.natAdd_injective q 1))
    (translationLift_retained hv H R) (Fin.castAdd (1 + q) 1) (translation_bundle hv H R)).stage

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  (linear : GammaPiecewiseRationalAffineInput (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
  (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε)

theorem translationStage_arity :
    (translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).arity = 2 + (1 + q) := rfl

theorem translationStage_target :
    (translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).target = translationTarget hv H R := rfl

theorem translationStage_lift :
    (translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).lift = translationLift hv H R := rfl

theorem translationStage_oldLabels :
    (translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).oldLabels =
      fun i => Fin.natAdd 2 (Fin.natAdd 1 i) := rfl

theorem translationStage_leading :
    (translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).leading = Fin.castAdd (1 + q) 1 := rfl

/-- **The value of the lift.** The VF part is `(x, y - ε(u, x))`; the labels are
the regularization tags `rv(x)`, `rv(y - ε(u, x)) = t(u)`, then the centripetal
tag `branchTag false`, then the old labels `u`. -/
theorem translationStage_lift_value (p : X) :
    ((translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).lift p).val =
      (![p.val.1 0, p.val.1 1 - ε p.val.2 (p.val.1 0)],
        Fin.append ![rv M (p.val.1 0), (t p.val.2).val] (Fin.append ![branchTag (M := M) false] p.val.2)) := by
  change (translationLift (G := G) hv H R p).val = _
  rw [translationLift_apply, translationLabels_eq H p.property]
  rfl

/-- **The contracted set**: `(x, w)` is contracted iff some `(x, y, u) ∈ X` has
`w = (rv(x), t(u), branchTag false, u)`. -/
theorem mem_translationStage_contracted (x : Fin 1 → VF M) (w : Fin (2 + (1 + q)) → RVInfinity M) :
    ((x, w) : Mixed M 1 (2 + (1 + q))) ∈
        (translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).contracted.carrier ↔
      ∃ u y, (![x 0, y], u) ∈ X.carrier ∧
        w = Fin.append ![rv M (x 0), (t u).val] (Fin.append ![branchTag (M := M) false] u) := by
  change (x, w) ∈ (vfDropLast (translationTarget (G := G) hv H R)).image.carrier ↔ _
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨p, hp, hzp⟩ := (mem_translationTarget_iff hv H R z.val).mp z.property
    have hx : Fin.init z.val.1 = x := congrArg Prod.fst hz
    have hw : z.val.2 = w := congrArg Prod.snd hz
    rw [hzp] at hx hw
    have hx0 : x 0 = p.1 0 := (congrFun hx 0).symm
    refine ⟨p.2, p.1 1, ?_, ?_⟩
    · rw [hx0, vec_two]
      exact hp
    · rw [← hw, hx0]
      exact translationLabels_eq H hp
  · rintro ⟨u, y, hxy, rfl⟩
    refine ⟨⟨(translate ε (![x 0, y], u), translationLabels ε (![x 0, y], u)),
      (mem_translationTarget_iff hv H R _).mpr ⟨_, hxy, rfl⟩⟩, ?_⟩
    change (Fin.init (translate ε (![x 0, y], u)), translationLabels ε (![x 0, y], u)) = _
    apply Prod.ext
    · funext i
      rw [Fin.fin_one_eq_zero i]
      rfl
    · exact translationLabels_eq H hxy

end Stage

/-! ### The opposite orientation

For the coordinate order `e = swap` of Section 6, the stages act on the
reindexed set `X ∘ swap` (`reindexedVFSet`). Its cells are the cells of `X` read
with base coordinate `1` and fibre coordinate `0` (`swapCell`), so the input can
be stated for `X` in that orientation (`BalancedShearInput.ofSwap`), and the
stages above apply to `reindexedVFSet X swap`. -/

section Swap

variable {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}

/-- The cell of `X` over `u` in the opposite orientation: base coordinate `1`,
fibre coordinate `0`. -/
def swapCell (X : DefSet (rawMixedSpace (M := M) 2 q) S) (u : Fin q → RVInfinity M) : Set (VF M × VF M) :=
  {p | (![p.2, p.1], u) ∈ X.carrier}

theorem mem_reindexed_swap (x y : VF M) (u : Fin q → RVInfinity M) :
    (![x, y], u) ∈ (reindexedVFSet X (Equiv.swap 0 1)).carrier ↔ (![y, x], u) ∈ X.carrier := by
  rw [mem_reindexedVFSet]
  have he : ![x, y] ∘ (Equiv.swap (0 : Fin 2) 1).symm = ![y, x] := by
    funext i
    fin_cases i
    · rfl
    · rfl
  change (![x, y] ∘ (Equiv.swap (0 : Fin 2) 1).symm, u) ∈ X.carrier ↔ _
  rw [he]

theorem cell_reindexed_swap (u : Fin q → RVInfinity M) :
    cell (reindexedVFSet X (Equiv.swap 0 1)) u = swapCell X u := by
  ext p
  exact mem_reindexed_swap p.1 p.2 u

/-- **The input in the opposite orientation.** Hypotheses on `X` with cells read
as `swapCell` give the input for the reindexed set `X ∘ swap`. -/
theorem BalancedShearInput.ofSwap (hX : ProperInvariant S X.carrier) (hD : VFDoublyBounded X.carrier)
    (hT : ∀ p ∈ X.carrier, ∀ p' ∈ X.carrier, p.2 = p'.2 → tupleRV M p.1 = tupleRV M p'.1)
    (hG : S.Definable LRV {z : Fin (2 + q) → M | ∃ u x, (∃ y, (![y, x], u) ∈ X.carrier) ∧
      z = Fin.append ![x.val, (ε u x).val] (rvValues u)})
    (hGt : S.Definable LRV {z : Fin (1 + q) → M | ∃ u x, (∃ y, (![y, x], u) ∈ X.carrier) ∧
      z = Fin.append ![(t u).val.val] (rvValues u)})
    (hbal : ∀ u, (swapCell X u).Nonempty → Balanced (swapCell X u) (ε u) (t₁ u) (t u).val)
    (hgen : ∀ u, ∀ p ∈ swapCell X u, rv M (ε u p.1) = rv M p.2) :
    BalancedShearInput (reindexedVFSet X (Equiv.swap 0 1)) ε t t₁ where
  proper := reindexedVFSet_properInvariant X _ hX
  doublyBounded := reindexedVFSet_doublyBounded X _ hD
  tagged := reindexedVFSet_tagged X _ hT
  focusGraph := by
    convert hG using 1
    ext z
    constructor
    · rintro ⟨u, x, ⟨y, hy⟩, hz⟩
      exact ⟨u, x, ⟨y, (mem_reindexed_swap x y u).mp hy⟩, hz⟩
    · rintro ⟨u, x, ⟨y, hy⟩, hz⟩
      exact ⟨u, x, ⟨y, (mem_reindexed_swap x y u).mpr hy⟩, hz⟩
  paradigmGraph := by
    convert hGt using 1
    ext z
    constructor
    · rintro ⟨u, x, ⟨y, hy⟩, hz⟩
      exact ⟨u, x, ⟨y, (mem_reindexed_swap x y u).mp hy⟩, hz⟩
    · rintro ⟨u, x, ⟨y, hy⟩, hz⟩
      exact ⟨u, x, ⟨y, (mem_reindexed_swap x y u).mpr hy⟩, hz⟩
  balanced u hne := by
    rw [cell_reindexed_swap] at hne ⊢
    exact hbal u hne
  genuine u p hp := by
    rw [cell_reindexed_swap] at hp
    exact hgen u p hp

end Swap

end DiamondIntegral.Section7.BalancedShearStages
