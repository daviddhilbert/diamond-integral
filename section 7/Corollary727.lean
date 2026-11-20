import «section 7».Remark728
import «section 7».PieceCombination
import «section 7».Proposition724Zero
import «section 7».RingClasses
import «section 3».GammaGroundMeasuredRVGenerators
import «section 3».GammaGroundGradedMeasuredIntegral
import FubiniTheorems.Fubini.Completed18GroundLiftInput

/-! Corollary 7.27 (`db:to:novol`): the diagram (diag-diamond-interpol) commutes.

```
K VF_*              ←  K μVF^◇[*]            →  K μVF[*]
  ↓ ∫                    ↓ ∫^◇                    ↓ ∫^μ
K RV[*]/(P - 1)     ←  K μRV^db[*]/J_var     →  K μRV[*]/(P)
```

The paper's proof: the image of `[A]` under any of the three integrals is
represented by a standard contraction of `A`. This file proves **both
squares** on the classes of objects, over the real part `T` of a Section 3
ground context `C` (as in Remark 7.28), with no intermediate-forms input.

`∫^◇[A]` is taken through a standard contraction: for an object `A` of
`μVF^◇[n+1]` and **any** standard contraction `F` of `A`, the class of `F`
(`PieceCombination.clsOf`) modulo `J_var` represents `∫^◇[A]`; in degree `0`,
`∫^◇` is the input-free `Proposition724Zero.integralZero`. The proofs use
Remark 6.28: `A ≅ μ𝕃 W` with `clsOf A F = [W]`.

**Bottom row** (Lemma 4.18, `relative:annular:compatibility`).
* `bottomLeft : K μRV^db[*]/J_var → K RV[*]/(P - 1)`: forget volume forms
  (`RVOrdinaryMaps.boundedForget`), extend the base from `⟨T, ∅⟩` to `⟨T, Γ⟩`
  (`ordinaryExt`), and divide by `P - 1`. It kills `J_var` by
  `manuscriptIdeal_le_forget_kernel`. The target
  `RVOrdinaryPNormalization.Ring C.base` is where Section 3's integral
  `nativeVFChartIntegral` lands.
* `bottomRight : K μRV^db[*]/J_var → K μRV[*]/(P)`: the inclusion into the full
  measured ring (`RVBoundedMaps.forget`), base extension (`measuredExt`), and
  the quotient by `(P)`; it kills `J_var` by `manuscriptIdeal_maps_into_p`. It
  is stated in Section 3's presentation, the target of `∫^μ`, through
  `pQuotientEquiv`, which rests on `measured_pClass`: the ring isomorphism
  `Section3RVRingEquivalences.measured` sends Section 4's `P` to Section 3's
  principal element.

**Left square** (`corollary_7_27_left`, `corollary_7_27_left_zero`). The top
arrow is `Remark728.forgetVF`. Forgetting forms sends `A ≅ μ𝕃 W` to an
isomorphism of Section 3 VF objects and `μ𝕃 W` to Section 3's lift of the RV
object of `W`, so `∫(forget A)` is the class of the chart of `W`, the
bottom-left image of `[W]`. This holds for every accepted Section 3 lift
input, in particular the proved `completed18GroundLiftInput`.

**Right square** (`corollary_7_27_right`, `corollary_7_27_right_zero`). The
top arrow is `forgetMVF` (the subcategory inclusion `μVF^◇ ⊆ μVF`, with the
Section 6 form read as a Section 3 volume form, `toGroundForm`). A morphism of
`μVF^◇` is a Section 3 measured morphism (`forgetMVF_class_iso`): in degree
`0` it is a form-preserving bijection; in positive degree it is an essential
map defined everywhere (`essentialOf`) that satisfies the Jacobian condition at
every VF-generic point, since generic points avoid its exceptional set
(`not_mem_bad`), and Section 3's `exists_pointwise_preserving` gives a
pointwise representative. The lift `μ𝕃 W` is sent to Section 3's measured
lift (`forgetMVF_lift`), so `∫^μ` (`theorem_3_22_measured_graded`, from the
proved measured lift records) of the image of `A` is the class of the chart of
`W` (`chart_measured_class`), the bottom-right image of `[W]`. The instance
`CharZero (VF M)` used by Section 3's measured integral is supplied by
`vf_charZero_of_model00 C.model00`.

The top arrows are given on objects and the squares are stated on classes of
objects, which generate the rings. The bottom arrows are ring maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Corollary727
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section5
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondGrothendieck
open DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.RelativeAnnularGenerators
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.BaseExtension DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.RingClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Base extension of the ordinary RV ring -/

section OrdinaryExt
variable {B D : Base (M := M)} (ht : Transfer B D)

/-- Base extension, as an invariant of the ordinary RV ring presentation. -/
def ordinaryExtInvariant : RVOrdinaryRing.Invariant B (RVOrdinaryRing.Ring D) where
  value _ a := RVOrdinaryRing.objectClass (chartExt ht a)
  unit := RVOrdinaryRing.objectClass_unit D
  product _ _ a b := RVOrdinaryRing.objectClass_product (chartExt ht a) (chartExt ht b)
  iso _ a b F := RVOrdinaryRing.objectClass_iso (a := chartExt ht a) (b := chartExt ht b)
    ⟨F.equiv, ht F.graph_definable⟩
  empty _ a ha := RVOrdinaryRing.objectClass_empty (chartExt ht a) ha
  scissor _ a b c d h := RVOrdinaryRing.objectClass_scissor (chartExt ht a) (chartExt ht b)
    (chartExt ht c) (chartExt ht d) h

/-- **Base extension `K RV[*]` over `B` → `K RV[*]` over `D`.** -/
def ordinaryExt : RVOrdinaryRing.Ring B →+* RVOrdinaryRing.Ring D :=
  RVOrdinaryRing.lift B (ordinaryExtInvariant ht)

theorem ordinaryExt_class {k : ℕ} (a : Chart B k) :
    ordinaryExt ht (RVOrdinaryRing.objectClass a) = RVOrdinaryRing.objectClass (chartExt ht a) :=
  RVOrdinaryRing.lift_objectClass B _ a

end OrdinaryExt

/-! ### The bottom-left arrow -/

/-- **`K μRV^db[*] / J_var`** over the raw base `⟨T, ∅⟩` (the target of `∫^◇`). -/
abbrev QRV (T : LRV.Substructure M) := RVBoundedRing.Ring (BT T) ⧸ manuscriptIdeal (BT T)

/-- The class of a `μRV^db[k]` class modulo `J_var`. -/
abbrev toQ {T : LRV.Substructure M} {k : ℕ} (x : Cls (BT T) k) : QRV T :=
  Ideal.Quotient.mk (manuscriptIdeal (BT T)) (clsRing x)

/-! ### Base extension of the measured RV ring -/

section MeasuredExt
variable {B D : Base (M := M)} (ht : Transfer B D)

/-- Base extension, as an invariant of the measured RV ring presentation. -/
def measuredExtInvariant : RVChartRing.Invariant B (RVChartRing.Ring D) where
  value _ a := RVChartRing.objectClass (chartExt ht a)
  unit := RVChartRing.objectClass_unit D
  product _ _ a b := RVChartRing.objectClass_product (chartExt ht a) (chartExt ht b)
  iso _ _ _ F := RVChartRing.objectClass_iso (isoExt ht F)
  empty _ a ha := RVChartRing.objectClass_empty (chartExt ht a) ha
  scissor _ a b c d h := RVChartRing.objectClass_scissor (chartExt ht a) (chartExt ht b)
    (chartExt ht c) (chartExt ht d) h

/-- **Base extension `K μRV[*]` over `B` → `K μRV[*]` over `D`.** -/
def measuredExt : RVChartRing.Ring B →+* RVChartRing.Ring D :=
  RVChartRing.lift B (measuredExtInvariant ht)

theorem measuredExt_class {k : ℕ} (a : Chart B k) :
    measuredExt ht (RVChartRing.objectClass a) = RVChartRing.objectClass (chartExt ht a) :=
  RVChartRing.lift_objectClass B _ a

/-- Base extension preserves `P`. -/
theorem measuredExt_pClass :
    measuredExt ht (RVMeasuredSpecialClasses.pClass B) = RVMeasuredSpecialClasses.pClass D := by
  unfold RVMeasuredSpecialClasses.pClass
  rw [map_sub, measuredExt_class, measuredExt_class]
  rfl

/-- Base extension maps `(P)` into `(P)`. -/
theorem measuredExt_pIdeal :
    (Ideal.span {RVMeasuredSpecialClasses.pClass B}).map (measuredExt ht) ≤ RVMeasuredPQuotient.pIdeal D := by
  rw [Ideal.map_span, Set.image_singleton, measuredExt_pClass]
  rfl

end MeasuredExt

/-! ### `P` in Section 3's measured presentation -/

section Principal
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))

/-- The measured chart of Section 3's measured `[1]` is the point. -/
def measuredPointIso : Iso (Section3MeasuredRVChartBridge.chart (gammaGroundMeasuredRVOne hc B))
    (RESFibreObjects.point B).toChart where
  equiv := (nativePointChartIso hc B).equiv
  graph_definable := (nativePointChartIso hc B).graph_definable
  weight_eq u := by
    obtain ⟨a, ha, hu⟩ := u.property
    change Section3RVFormBridge.rawForm _ u.val * ∏ i, codeValue (Section3RVCodeBridge.rawMap _ u.val i) =
      1 * ∏ i, codeValue (u.val i)
    rw [← hu, Section3RVFormBridge.rawForm_apply _ ⟨a, ha⟩, Section3RVCodeBridge.rawMap_apply _ ⟨a, ha⟩]
    have h1 : ((gammaGroundMeasuredRVOne hc B).form.toFun ⟨a, ha⟩).val = (1 : Values.Gamma (M := M)) :=
      gammaGroundOneForm_value (gammaGroundMeasuredRVOne hc B).underlying.domain ⟨a, ha⟩
    have h2 : ((gammaGroundMeasuredRVOne hc B).underlying.volume.toFun ⟨a, ha⟩).val = a := rfl
    rw [h1, h2]
    rfl

/-- The measured chart of Section 3's measured `[RV°°]` is the sharp positive
ray. -/
def measuredPositiveIso : Iso (Section3MeasuredRVChartBridge.chart (gammaGroundMeasuredRVPositive hc B))
    (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B)) where
  equiv := (nativePositiveChartIso hc B).equiv
  graph_definable := (nativePositiveChartIso hc B).graph_definable
  weight_eq u := by
    obtain ⟨a, ha, hu⟩ := u.property
    change Section3RVFormBridge.rawForm _ u.val * ∏ i, codeValue (Section3RVCodeBridge.rawMap _ u.val i) =
      1 * ∏ i, codeValue (u.val i)
    rw [← hu, Section3RVFormBridge.rawForm_apply _ ⟨a, ha⟩, Section3RVCodeBridge.rawMap_apply _ ⟨a, ha⟩]
    have h1 : ((gammaGroundMeasuredRVPositive hc B).form.toFun ⟨a, ha⟩).val = (1 : Values.Gamma (M := M)) :=
      gammaGroundOneForm_value (gammaGroundMeasuredRVPositive hc B).underlying.domain ⟨a, ha⟩
    have h2 : ((gammaGroundMeasuredRVPositive hc B).underlying.volume.toFun ⟨a, ha⟩).val = a := rfl
    rw [h1, h2]
    rfl

/-- **`P` in Section 3's measured presentation.** The ring isomorphism
`Section3RVRingEquivalences.measured` sends Section 4's `P = [pt] - [RV°°]` to
Section 3's principal element `[1] - [RV°°]`. -/
theorem measured_pClass :
    Section3RVRingEquivalences.measured hc B (RVMeasuredSpecialClasses.pClass B) =
      gammaGroundMeasuredRVPrincipalElement hc B := by
  apply (Section3RVRingEquivalences.measured hc B).symm.injective
  rw [RingEquiv.symm_apply_apply]
  change _ = (Section3RVRingEquivalences.measured hc B).symm
    (Section3RVClassCuts.measuredClass (gammaGroundMeasuredRVOne hc B) -
      Section3RVClassCuts.measuredClass (gammaGroundMeasuredRVPositive hc B))
  rw [map_sub, Section3RVRingEquivalences.measured_symm_class, Section3RVRingEquivalences.measured_symm_class,
    RVChartRing.objectClass_iso (measuredPointIso hc B), RVChartRing.objectClass_iso (measuredPositiveIso hc B)]
  rfl

/-- `K μRV[*]/(P)` in Section 4's chart presentation and in Section 3's
presentation (the target of `∫^μ`) are isomorphic. -/
def pQuotientEquiv : RVMeasuredPQuotient.Ring B ≃+*
    GammaGroundMeasuredRVGrothendieckRing hc B ⧸
      Ideal.span ({gammaGroundMeasuredRVPrincipalElement hc B} : Set (GammaGroundMeasuredRVGrothendieckRing hc B)) :=
  Ideal.quotientEquiv _ _ (Section3RVRingEquivalences.measured hc B) (by
    rw [RVMeasuredPQuotient.pIdeal, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x => Ideal.span {x}) (measured_pClass hc B).symm)

theorem pQuotientEquiv_quotient (x : RVChartRing.Ring B) :
    pQuotientEquiv hc B (RVMeasuredPQuotient.quotient B x) =
      Ideal.Quotient.mk _ (Section3RVRingEquivalences.measured hc B x) := rfl

end Principal

/-! ### Section 6 Gamma forms as Section 3 volume forms -/

section Forms
variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- The two presentations of `Γ` by nonzero RV codes decode alike. -/
theorem gamma_decode (z : Fin 1 → M) (hz : NonzeroRV (z 0)) :
    (volumeGammaSpace hc).decode ⟨z, hz⟩ = (rawGammaPresentation (M := M)).decode ⟨z, hz⟩ := by
  change Values.gammaOf ⟨z 0, hz.1⟩ hz.2 = codeValue (z 0)
  exact (DiamondIntegral.Section7.MeasuredRVBridge.codeValue_gammaOf ⟨z 0, hz.1⟩ hz.2).symm

/-- A Section 6 Gamma form (presentation `rawGammaPresentation`) as a Section 3
volume form (presentation `volumeGammaSpace`), over any ground with the same
real part. -/
def toGroundForm {B : GammaParameters.Base (M := M)} {Q : Space LRV M} {A : DefSet Q B.real}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) B.real)) :
    GammaGroundVolumeForm hc B (GammaGroundDefSet.ofReal A) where
  toFun a := ⟨(ω a).val, Set.mem_univ _⟩
  graph_definable := by
    apply GammaGroundDefinable.of_real
    have h := ω.graph_definable
    change B.real.Definable LRV (Q.relation rawGammaPresentation _) at h
    change B.real.Definable LRV ((Q.prod (volumeGammaSpace hc)).preimage _)
    have he : (Q.prod (volumeGammaSpace hc)).preimage
        {z | ∃ a : (GammaGroundDefSet.ofReal (hc := hc) (ground := B) A), a.val = z.1 ∧
          ((⟨(ω a).val, Set.mem_univ _⟩ : GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :
            (volumeGammaSpace hc).Carrier) = z.2} =
        Q.relation rawGammaPresentation (fun x y => ∃ a : A, a.val = x ∧ (ω a).val = y) := by
      ext z
      constructor
      · rintro ⟨⟨hx, hy⟩, a, ha1, ha2⟩
        refine ⟨hx, hy, a, ha1, ?_⟩
        exact ha2.trans (gamma_decode hc _ hy)
      · rintro ⟨hx, hy, a, ha1, ha2⟩
        refine ⟨⟨hx, hy⟩, a, ha1, ?_⟩
        exact ha2.trans (gamma_decode hc _ hy).symm
    rw [he]
    exact h

theorem toGroundForm_value {B : GammaParameters.Base (M := M)} {Q : Space LRV M} {A : DefSet Q B.real}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) B.real)) (a : A) :
    gammaGroundFormValue (toGroundForm hc ω) a = gammaMapValue ω a := rfl

end Forms

section Context
variable (C : GammaGroundContext M)

/-- Names of the raw base `⟨T, ∅⟩` are names of the context base `⟨T, Γ⟩`. -/
theorem transfer : Transfer (BT C.real) C.base :=
  Transfer.ofSubset (B := BT C.real) (C := C.base) (fun _ h => h) (Set.empty_subset _)

/-- The volume-forgetting map `K μRV^db[*] → K RV[*]/(P - 1)`, with the base
extended from `⟨T, ∅⟩` to `⟨T, Γ⟩`. -/
def forgetNormalized : RVBoundedRing.Ring (BT C.real) →+* RVOrdinaryPNormalization.Ring C.base :=
  (RVOrdinaryPNormalization.quotient C.base).comp
    ((ordinaryExt (transfer C)).comp (RVOrdinaryMaps.boundedForget (BT C.real)))

/-- Forgetting volume forms kills `J_var` (Lemma 4.18). -/
theorem manuscriptIdeal_le_ker : manuscriptIdeal (BT C.real) ≤ RingHom.ker (forgetNormalized C) := by
  intro x hx
  have h := manuscriptIdeal_le_forget_kernel hx
  rw [RingHom.mem_ker] at h ⊢
  change RVOrdinaryPNormalization.quotient C.base
    (ordinaryExt (transfer C) (RVOrdinaryMaps.boundedForget (BT C.real) x)) = 0
  rw [h, map_zero, map_zero]

/-- **The bottom-left arrow `K μRV^db[*]/J_var → K RV[*]/(P - 1)`** of
(diag-diamond-interpol), induced by forgetting volume forms
(Lemma 4.18, `relative:annular:compatibility`). -/
def bottomLeft : QRV C.real →+* RVOrdinaryPNormalization.Ring C.base :=
  Ideal.Quotient.lift _ (forgetNormalized C) (fun _ hx => manuscriptIdeal_le_ker C hx)

theorem bottomLeft_mk {k : ℕ} (a : Obj (BT C.real) k) :
    bottomLeft C (Ideal.Quotient.mk _ (RVBoundedRing.objectClass a)) =
      RVOrdinaryPNormalization.quotient C.base (RVOrdinaryRing.objectClass (chartExt (transfer C) a.toChart)) := by
  change RVOrdinaryPNormalization.quotient C.base
    (ordinaryExt (transfer C) (RVOrdinaryMaps.boundedForget (BT C.real) (RVBoundedRing.objectClass a))) = _
  rw [RVOrdinaryMaps.boundedForget_class, ordinaryExt_class]

/-! ### The bottom-right arrow -/

/-- The volume-preserving forgetful map `K μRV^db[*] → K μRV[*]/(P)`, with the
base extended from `⟨T, ∅⟩` to `⟨T, Γ⟩` (Section 4's chart presentation). -/
def measuredForget : RVBoundedRing.Ring (BT C.real) →+* RVMeasuredPQuotient.Ring C.base :=
  (RVMeasuredPQuotient.quotient C.base).comp
    ((measuredExt (transfer C)).comp (RVBoundedMaps.forget (BT C.real)))

/-- The image of `J_var` in the full measured RV ring lies in `(P)` (Lemma 4.18). -/
theorem manuscriptIdeal_le_measured_ker :
    manuscriptIdeal (BT C.real) ≤ RingHom.ker (measuredForget C) := by
  intro x hx
  have h : RVBoundedMaps.forget (BT C.real) x ∈ Ideal.span {RVMeasuredSpecialClasses.pClass (BT C.real)} :=
    manuscriptIdeal_maps_into_p hx
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (measuredExt_pIdeal (transfer C) (Ideal.mem_map_of_mem _ h))

/-- The bottom-right arrow `K μRV^db[*]/J_var → K μRV[*]/(P)` in Section 4's
chart presentation (Lemma 4.18, `relative:annular:compatibility`). -/
def bottomRightChart : QRV C.real →+* RVMeasuredPQuotient.Ring C.base :=
  Ideal.Quotient.lift _ (measuredForget C) (fun _ hx => manuscriptIdeal_le_measured_ker C hx)

theorem bottomRightChart_mk {k : ℕ} (a : Obj (BT C.real) k) :
    bottomRightChart C (Ideal.Quotient.mk _ (RVBoundedRing.objectClass a)) =
      RVMeasuredPQuotient.quotient C.base (RVChartRing.objectClass (chartExt (transfer C) a.toChart)) := by
  change RVMeasuredPQuotient.quotient C.base
    (measuredExt (transfer C) (RVBoundedMaps.forget (BT C.real) (RVBoundedRing.objectClass a))) = _
  rw [RVBoundedMaps.forget_class, measuredExt_class]

/-- **The bottom-right arrow `K μRV^db[*]/J_var → K μRV[*]/(P)`** of
(diag-diamond-interpol), with target Section 3's presentation of
`K μRV[*]/(P)`, the target of `∫^μ` (`theorem_3_22_measured_graded`). -/
def bottomRight (hc : CanonicalStructure.IsCanonical (M := M)) :
    QRV C.real →+* GammaGroundMeasuredRVGrothendieckRing hc C.base ⧸
      Ideal.span ({gammaGroundMeasuredRVPrincipalElement hc C.base} :
        Set (GammaGroundMeasuredRVGrothendieckRing hc C.base)) :=
  (pQuotientEquiv hc C.base).toRingHom.comp (bottomRightChart C)

theorem bottomRight_mk (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : Obj (BT C.real) k) :
    bottomRight C hc (Ideal.Quotient.mk _ (RVBoundedRing.objectClass a)) =
      Ideal.Quotient.mk _ (Section3RVClassCuts.measuredClass
        (Section3MeasuredRVChartBridge.native hc (chartExt (transfer C) a.toChart))) := by
  rw [bottomRight, RingHom.comp_apply]
  exact (congrArg (pQuotientEquiv hc C.base) (bottomRightChart_mk C a)).trans
    (by rw [pQuotientEquiv_quotient, Section3RVRingEquivalences.measured_class])

/-! ### The left square -/

section Left
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- Section 3's integral of the underlying VF object of the lift of a measured
RV object is the class of the base-extended chart of the object. -/
theorem integral_forgetVF_lift (H : YinGammaGroundUnmeasuredLiftInput C hc) {k : ℕ}
    (A : DiamondCategory.VFObject (M := M) (C.real : Set M) k)
    (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) k)
    (hP : ProperInvariant (C.real : Set M) (rvLift U.object).carrier) (hiso : Isomorphic G A (liftObject U hP)) :
    nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))) =
      RVOrdinaryPNormalization.quotient C.base
        (RVOrdinaryRing.objectClass (chartExt (transfer C) (chartOf hc U))) := by
  rw [Remark728.forgetVF_iso hc C hiso, Remark728.forgetVF_lift, nativeVFChartIntegral_lift_class,
    Remark728.chart_ordinary_class]

variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hΓ : NontrivialDefinableGamma (⟨(C.real : Set M), ∅⟩ : ParameterBase M))

/-- **Corollary 7.27, left square, positive degree.** Let `A` be an object of
`μVF^◇[n+1]` over the real part of a Section 3 ground context and `F` any
standard contraction of `A`, so that `∫^◇[A]` is the class of `F` modulo
`J_var` (Proposition 7.24, Theorem 7.26). Section 3's integral of the
underlying VF object of `A` (forms forgotten) is the image of that class under
the bottom-left arrow `K μRV^db[*]/J_var → K RV[*]/(P - 1)`. This holds for
every accepted Section 3 lift input, and uses no further input. -/
theorem corollary_7_27_left (H : YinGammaGroundUnmeasuredLiftInput C hc) {n : ℕ}
    (A : DiamondCategory.VFObject (M := M) (C.real : Set M) (n + 1)) {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))) =
      bottomLeft C (toQ (PieceCombination.clsOf C.model00 hc C.uncountable C.saturated hv C.small_real hΓ A F)) := by
  obtain ⟨hP, iA⟩ := remark_6_28 C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ A F 0 Fin.elim0
  rw [integral_forgetVF_lift C hc H A _ hP iA]
  exact (bottomLeft_mk C (objOf hc C.real
    (F.headStartMeasuredObject C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ 0 Fin.elim0
      (object_hFin A Fin.elim0)) (F.headStartObject_doublyBounded 0 Fin.elim0))).symm

include hv hΓ in
/-- **Corollary 7.27, left square, degree `0`**, with the input-free degree-zero
integral `∫^◇ : K₊ μVF^◇[0] → K₊ μRV^db[0]` (`Proposition724Zero.integralZero`). -/
theorem corollary_7_27_left_zero (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) :
    nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))) =
      bottomLeft C (toQ (Proposition724Zero.integralZero G C.model00 hc (vfClass G hc A))) := by
  obtain ⟨U, hU, hiso⟩ := DiamondSurjectivity.exists_isomorphic_lift_zero (G := G) C.model00 hc lin C.uncountable
    C.saturated hv C.small_real hΓ A
  rw [integral_forgetVF_lift C hc H A U _ hiso, Proposition724Zero.integralZero_vfClass,
    Proposition724Zero.zeroClass_iso C.model00 hc hiso, Proposition724Zero.zeroClass_lift C.model00 hc U hU]
  exact (bottomLeft_mk C (objOf hc C.real U hU)).symm

/-! ### With the proved Section 3 lift input -/

/-- **Corollary 7.27, left square**, for Section 3's integral with the proved
lift record `completed18GroundLiftInput`. -/
theorem corollary_7_27_left_completed {n : ℕ}
    (A : DiamondCategory.VFObject (M := M) (C.real : Set M) (n + 1)) {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    nativeVFChartIntegral (completed18GroundLiftInput C hc)
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))) =
      bottomLeft C (toQ (PieceCombination.clsOf C.model00 hc C.uncountable C.saturated hv C.small_real hΓ A F)) :=
  corollary_7_27_left C hc hv hΓ _ A F

include hv hΓ in
/-- **Corollary 7.27, left square, degree `0`**, with the proved lift record. -/
theorem corollary_7_27_left_zero_completed (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) :
    nativeVFChartIntegral (completed18GroundLiftInput C hc)
        (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))) =
      bottomLeft C (toQ (Proposition724Zero.integralZero G C.model00 hc (vfClass G hc A))) :=
  corollary_7_27_left_zero C hc hv hΓ _ A

end Left

/-! ### The right square -/

section Right
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- **The top-right arrow on objects**: an object of `μVF^◇[n]` over the real
part of the context, as a Section 3 measured VF object (the subcategory
inclusion `μVF^◇ ⊆ μVF`). -/
def forgetMVF {n : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) n) :
    GammaGroundMeasuredVFData hc C.base n where
  arity := A.labels
  domain := GammaGroundDefSet.ofReal A.carrier
  finite := A.finiteRV
  form := toGroundForm hc A.form

/-- A Section 6 measured RV object as a Section 3 measured RV object. -/
def forgetMRV {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n) :
    GammaGroundMeasuredRVObject hc C.base n :=
  ⟨Remark728.forgetRV hc C U, toGroundForm hc U.form⟩

/-- The lift of a measured RV object is sent to Section 3's measured lift. -/
theorem forgetMVF_lift {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n)
    (hP : ProperInvariant (C.real : Set M) (rvLift U.object).carrier) :
    forgetMVF C hc (liftObject U hP) = gammaGroundMeasuredObjectLift (forgetMRV C hc U) := rfl

/-- Section 3's measured chart of the image of `U` and Section 7's chart of
`U`, base-extended, have the same measured class. -/
theorem chart_measured_class {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n) :
    RVChartRing.objectClass (Section3MeasuredRVChartBridge.chart (forgetMRV C hc U)) =
      RVChartRing.objectClass (chartExt (transfer C) (chartOf hc U)) := by
  apply RVChartRing.objectClass_iso
  let F := RVForgetScissors.ofMap (Section3MeasuredRVChartBridge.chart (forgetMRV C hc U))
    (chartExt (transfer C) (chartOf hc U)) id
    (RVSharpCharts.identity_graph_definable C.base _ (Section3RVCodeBridge.rawDomain_definable _))
    (Set.bijOn_id _)
  refine ⟨F.equiv, F.graph_definable, fun u => ?_⟩
  obtain ⟨t, ht, hu⟩ := u.property
  change Section3RVFormBridge.rawForm _ u.val * ∏ i, codeValue (Section3RVCodeBridge.rawMap _ u.val i) =
    rawVol U u.val * ∏ i, codeValue (rawCoord U u.val i)
  rw [← hu, Section3RVFormBridge.rawForm_apply _ ⟨t, ht⟩, Section3RVCodeBridge.rawMap_apply _ ⟨t, ht⟩,
    rawVol_of U ⟨t, ht⟩, rawCoord_of U ⟨t, ht⟩]
  rfl

/-- The Section 3 measured class of the image of `U` is the image of its
base-extended chart. -/
theorem measuredClass_forgetMRV {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n) :
    Section3RVClassCuts.measuredClass (forgetMRV C hc U) =
      Section3RVClassCuts.measuredClass
        (Section3MeasuredRVChartBridge.native hc (chartExt (transfer C) (chartOf hc U))) := by
  rw [← Section3RVRingEquivalences.measured_class, ← chart_measured_class,
    ← Section3RVRingEquivalences.measured_symm_class, RingEquiv.apply_symm_apply]

include hc in
/-- A VF-generic point avoids the exceptional set of a morphism of `μVF^◇`. -/
theorem not_mem_bad {n : ℕ} {A B : DiamondCategory.VFObject (M := M) (C.real : Set M) n} (Φ : Morphism G A B)
    (p : A.carrier) (hp : AlgebraicIndependent (vfParameterField (C.real : Set M)) p.val.1) :
    p.val ∉ Φ.bad.carrier := by
  intro hb
  rcases Φ.bad_small with h | h
  · let q : Φ.bad := ⟨p.val, hb⟩
    have hle := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) Φ.bad q
    have hqd : vfTupleTrdeg (C.real : Set M) q.val.1 = (n : Cardinal) :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField _) q.val.1).mpr hp
    rw [hqd] at hle
    exact (not_le_of_gt h) (by exact_mod_cast hle)
  · rw [h] at hb
    exact hb

/-- A morphism of `μVF^◇` as a Section 3 essential VF map (defined everywhere). -/
def essentialOf {n : ℕ} {A B : DiamondCategory.VFObject (M := M) (C.real : Set M) n} (Φ : Morphism G A B) :
    GammaGroundEssentialVFMap (GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) A.carrier)
      (GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) B.carrier) := by
  have hA : DiamondIntegral.Section2.vfDimension ((GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) A.carrier).sdiff
      (GammaGroundDefSet.ofReal A.carrier)).carrier < (n : WithBot ℕ) := by
    have h : ((GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) A.carrier).sdiff
        (GammaGroundDefSet.ofReal A.carrier)).carrier = ∅ := Set.sdiff_self
    rw [h, DiamondIntegral.Section2.vfDimension_empty]
    exact WithBot.bot_lt_coe n
  have hB : DiamondIntegral.Section2.vfDimension ((GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) B.carrier).sdiff
      (GammaGroundDefSet.ofReal B.carrier)).carrier < (n : WithBot ℕ) := by
    have h : ((GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) B.carrier).sdiff
        (GammaGroundDefSet.ofReal B.carrier)).carrier = ∅ := Set.sdiff_self
    rw [h, DiamondIntegral.Section2.vfDimension_empty]
    exact WithBot.bot_lt_coe n
  exact ⟨_, _, fun _ h => h, fun _ h => h, hA, hB, GammaGroundMap.ofReal Φ.map, Φ.bijective⟩

/-- It preserves the measured weights at generic points: the Jacobian
condition of `μVF^◇`. -/
theorem essentialOf_preserves {n : ℕ} {A B : DiamondCategory.VFObject (M := M) (C.real : Set M) n}
    (Φ : Morphism G A B) :
    (essentialOf C hc Φ).PreservesGeneric Values.vfValueHom (gammaGroundMeasuredVFWeight (forgetMVF C hc A))
      (gammaGroundMeasuredVFWeight (forgetMVF C hc B)) := by
  intro p hp
  have hbad := not_mem_bad C hc Φ p hp
  obtain ⟨L, ⟨F, hF, hd⟩, hdet⟩ := Φ.measure p hbad
  refine ⟨(LinearMap.toMatrix' L).det, ⟨F, hF, hd.hasJacobianAt⟩, ?_⟩
  have h1 : gammaMapValue A.form p = gammaMapValue B.form (Φ.map p) *
      (gammaMapValue A.form p / gammaMapValue B.form (Φ.map p)) := (mul_div_cancel _ _).symm
  change (gammaMapValue A.form p).val =
    (gammaMapValue B.form (Φ.map p)).val * vfValue (LinearMap.toMatrix' L).det
  conv_lhs => rw [h1]
  rw [hdet]
  exact Values.gammaValHom.map_mul _ _

variable [CharZero (VF M)] (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-- Isomorphic objects of `μVF^◇` have equal Section 3 measured classes. -/
theorem forgetMVF_class_iso {n : ℕ} {A B : DiamondCategory.VFObject (M := M) (C.real : Set M) n}
    (h : Isomorphic G A B) :
    gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (forgetMVF C hc A) =
      gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv (forgetMVF C hc B) := by
  obtain ⟨Φ⟩ := h
  rcases n with _ | k
  · apply gammaGroundMeasuredVFClass_iso
    exact (⟨⟨GammaGroundMap.ofReal (hc := hc) (ground := C.base) Φ.map, Φ.bijective⟩,
      fun a => DiamondIntegral.Section7.Proposition724Zero.morphism_form Φ a⟩ :
        GammaGroundZeroMeasuredVFHom (forgetMVF C hc A) (forgetMVF C hc B))
  · have hn : 0 < k + 1 := Nat.zero_lt_succ k
    obtain ⟨g, hg, -⟩ := (essentialOf C hc Φ).exists_pointwise_preserving C.uncountable.le C.saturated
      C.small_real hv hn (forgetMVF C hc A).form (forgetMVF C hc B).form (essentialOf_preserves C hc Φ)
    apply gammaGroundMeasuredVFClass_iso
    exact gammaGroundMeasuredOfRepresentative C.uncountable.le C.saturated C.small_real hv hn ⟨g, hg⟩

/-- `∫^μ` of the image of an object isomorphic to a lift `μ𝕃 U` is the class of
the base-extended chart of `U`. -/
theorem measuredIntegral_forgetMVF_lift {n : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) n)
    (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n)
    (hP : ProperInvariant (C.real : Set M) (rvLift U.object).carrier) (hiso : Isomorphic G A (liftObject U hP)) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    theorem_3_22_measured_graded C hc hv
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A))) =
      Ideal.Quotient.mk _ (Section3RVClassCuts.measuredClass
        (Section3MeasuredRVChartBridge.native hc (chartExt (transfer C) (chartOf hc U)))) := by
  have hcls : gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A) =
      gammaGroundMeasuredVFDirectSumClass (hv := hv) (gammaGroundMeasuredObjectLift (forgetMRV C hc U)) := by
    unfold gammaGroundMeasuredVFDirectSumClass
    rw [forgetMVF_class_iso C hc hv hiso, forgetMVF_lift]
  rw [hcls, theorem_3_22_measured_graded_lift_class, ← measuredClass_forgetMRV]
  rfl

variable (hΓ : NontrivialDefinableGamma (⟨(C.real : Set M), ∅⟩ : ParameterBase M))

/-- **Corollary 7.27, right square, positive degree.** Let `A` be an object of
`μVF^◇[n+1]` over the real part of a Section 3 ground context and `F` any
standard contraction of `A`. Section 3's measured integral `∫^μ`
(`theorem_3_22_measured_graded`, from the proved measured lift records) of the
image of `A` in `K μVF[*]` is the image of the class of `F` modulo `J_var`
under the bottom-right arrow `K μRV^db[*]/J_var → K μRV[*]/(P)`. -/
theorem corollary_7_27_right {n : ℕ}
    (A : DiamondCategory.VFObject (M := M) (C.real : Set M) (n + 1)) {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    theorem_3_22_measured_graded C hc hv
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A))) =
      bottomRight C hc (toQ (PieceCombination.clsOf C.model00 hc C.uncountable C.saturated hv C.small_real hΓ A F)) := by
  obtain ⟨hP, iA⟩ := remark_6_28 C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ A F 0 Fin.elim0
  rw [measuredIntegral_forgetMVF_lift C hc hv A _ hP iA]
  exact (bottomRight_mk C hc (objOf hc C.real
    (F.headStartMeasuredObject C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ 0 Fin.elim0
      (object_hFin A Fin.elim0)) (F.headStartObject_doublyBounded 0 Fin.elim0))).symm

include hΓ in
/-- **Corollary 7.27, right square, degree `0`**, with the input-free
`Proposition724Zero.integralZero`. -/
theorem corollary_7_27_right_zero (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    theorem_3_22_measured_graded C hc hv
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A))) =
      bottomRight C hc (toQ (Proposition724Zero.integralZero G C.model00 hc (vfClass G hc A))) := by
  obtain ⟨U, hU, hiso⟩ := DiamondSurjectivity.exists_isomorphic_lift_zero (G := G) C.model00 hc lin C.uncountable
    C.saturated hv C.small_real hΓ A
  rw [measuredIntegral_forgetMVF_lift C hc hv A U _ hiso, Proposition724Zero.integralZero_vfClass,
    Proposition724Zero.zeroClass_iso C.model00 hc hiso, Proposition724Zero.zeroClass_lift C.model00 hc U hU]
  exact (bottomRight_mk C hc (objOf hc C.real U hU)).symm

end Right

end Context

end DiamondIntegral.Section7.Corollary727
