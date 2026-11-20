import «section 7».BlowupLiftGeneral
import «section 7».IsoOfMeasured
import «section 7».Theorem726

/-! Lemma 7.12 (`blowup:same:RV:coa`) at object level, for an elementary blowup.

**Statement.** For every aperture datum `D` (Notation 4.17, a doubly bounded
chart `U`, a coordinate `j` and an aperture `τ`), the lift of the relative
annular object `U^{τ,j}` is isomorphic in `μVF^◇[1+k]` to the lift of `U`
(`lemma_7_12_objects`).

**Route.** `BlowupLiftGeneral.lemma_7_12` proves the class form. Here the same
pipeline gives an actual isomorphism.

1. For the strict (`∞`-free) datum `D'` of `D`, Section 6's relative aperture
   data, the regularization and the contraction give a doubly bounded measured
   RV object `W` with `𝕃 U ≅ 𝕃 W` (`BlowupLiftContraction.lift_isomorphic`).
2. `W` splits by tag into its endpoint and shell pieces, isomorphic to the
   endpoint and shell charts of `D'` (`BlowupLiftClasses.isoE`, `isoS`). Read
   through `ChartOfMeasured.chartOf`, the two pieces are the restrictions of
   the chart of `W` to the endpoint labels and to their complement
   (`core_cls`, `shell_cls`). Gluing along this partition (`cls_partition`)
   gives a chart isomorphism `U'^{τ,j} ≅ chartOf W` (`annular_cls`).
3. The strict datum has the class of blowup of `D`
   (`BlowupLiftGeneral.strict_annular`), so `U^{τ,j} ≅ U'^{τ,j}` as charts.
   Composing with the strict encoding gives a measured RV isomorphism from the
   strict form of `U^{τ,j}` onto `W`, which Lemma 6.33 lifts to `μVF^◇`.
4. The strict form of `U` is the source chart of `D'`, so step 1 closes the
   chain `𝕃 U^{τ,j} ≅ 𝕃 W ≅ 𝕃 U`.

Also: isomorphic charts have isomorphic lifts (`lift_congr`, Lemma 6.33), so
`𝕃 U^{τ,j} ≅ 𝕃 V` whenever `U ≅ V` (`lemma_7_12_objects_of_iso`).

**Scope.** A blowup of length one with a proper locus is
`(V ∖ C) ⊎ ⊎ U_i^♭`. Its object form would need lifts of tagged coproducts to
be congruent in each summand, i.e. gluing `μVF^◇` morphisms along a disjoint
union with the identity on the other summand. Section 6 has no such gluing
lemma yet (a morphism is a chain of steps through objects whose label counts
vary), so the general form is stated on classes only
(`BlowupLiftGeneral.step_lift`, `steps_lift`). Since 2026-11-20 each step is
relatively unary in a single coordinate (Definition 6.24), for which the
identity is a step in every coordinate, so such a gluing lemma is possible. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 DiamondIntegral.Section2 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section9 (rvLabelImage_subset)

namespace DiamondIntegral.Section7.Lemma712Objects
open DiamondIntegral.Section4
open DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.BlowupLiftImage
open DiamondIntegral.Section7.BlowupLiftContraction DiamondIntegral.Section7.BlowupLiftClasses
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.IsoOfMeasured
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondLiftHomomorphism

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-! ### The contraction as a chart, and its tag split -/

section Glue
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (R : RelativeApertureData (G := G) (liftSet hc D))
variable (hj : R.coordinate = D.coordinate)
variable (hact : ∀ p ∈ (liftSet hc D).carrier, p.2 ∈ R.activeTags.carrier)
variable (hend : ∀ p ∈ (liftSet hc D).carrier,
  (rv M (R.extendedEndpoint p)).val = centrePair D (rvValues p.2) 1)
variable (h00 : M ⊨ Axioms.ACVF00)
include hj hact hend

local notation "𝓦" => W (G := G) hc D R hj hact hend h00

/-- The contraction `W`, read as a bounded chart. -/
abbrev wObj : Obj (⟨S, ∅⟩ : Base (M := M)) (1 + k) :=
  ⟨chartOf hc (𝓦), chartOf_bounded hc _ (W_doublyBounded hc D R hj hact hend h00)⟩

theorem chartIso_val (x : (toMeasured hc (chartOf hc (𝓦))).object.domain) :
    ((measuredIso_chartOf hc (𝓦)).iso.hom.map x).val = x.val := rfl

/-- The endpoint chart has the class of the endpoint piece of the chart of `W`. -/
theorem core_cls :
    cls (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded) =
      cls (piece (wObj hc D R hj hact hend h00) (Icore D) (Icore_definable D)) := by
  obtain ⟨e⟩ : Nonempty (MeasuredRVIso (Wcore hc D R hj hact hend h00)
      (toMeasured hc (piece (wObj hc D R hj hact hend h00) (Icore D) (Icore_definable D)).toChart)) := by
    let c := chartOf hc (𝓦)
    let A := rawDefSet hc (c.domain ∩ Icore D) (c.domain_definable.inter (Icore_definable D))
    have hA : A.carrier ⊆ (toMeasured hc c).object.domain.carrier := fun _ h => h.1
    let e1 := (measuredIso_chartOf hc (𝓦)).restrict A hA
    have himg : ((measuredIso_chartOf hc (𝓦)).iso.hom.map.restrict hA).image = Dcore hc D := by
      apply DefSet.eq_of_carrier_eq
      ext t
      constructor
      · rintro ⟨a, rfl⟩
        exact a.property.2
      · intro ht
        have htW := Dcore_sub hc D R hj hact hend h00 ht
        exact ⟨⟨t, mem_rawDom _ ⟨t, htW⟩, ht⟩, rfl⟩
    have heq := LiftClasses.restrict_congr (𝓦) himg
      (rvLabelImage_subset (measuredIso_chartOf hc (𝓦)).iso A hA) (Dcore_sub hc D R hj hact hend h00)
    have e2 := e1.symm
    rw [heq] at e2
    exact ⟨e2⟩
  exact cls_eq_iff.mpr ⟨isoOfMeasured hc ((isoE hc D R hj hact hend h00).comp e)⟩

/-- The shell chart has the class of the complementary piece of the chart of `W`. -/
theorem shell_cls :
    cls (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded) =
      cls (cpiece (wObj hc D R hj hact hend h00) (Icore D) (Icore_definable D)) := by
  obtain ⟨e⟩ : Nonempty (MeasuredRVIso (Wshell hc D R hj hact hend h00)
      (toMeasured hc (cpiece (wObj hc D R hj hact hend h00) (Icore D) (Icore_definable D)).toChart)) := by
    let c := chartOf hc (𝓦)
    change Nonempty (MeasuredRVIso _ (toMeasured hc (ElementaryBlowups.cresChart c (Icore D) (Icore_definable D))))
    rw [LiftClasses.toMeasured_cres hc c (Icore D) (Icore_definable D)]
    let A := rawDefSet hc (c.domain ∩ Icore D) (c.domain_definable.inter (Icore_definable D))
    let A' := (toMeasured hc c).object.domain.sdiff A
    have hA' : A'.carrier ⊆ (toMeasured hc c).object.domain.carrier := fun _ h => h.1
    let e1 := (measuredIso_chartOf hc (𝓦)).restrict A' hA'
    have himg : ((measuredIso_chartOf hc (𝓦)).iso.hom.map.restrict hA').image =
        (𝓦).object.domain.sdiff (Dcore hc D) := by
      apply DefSet.eq_of_carrier_eq
      ext t
      constructor
      · rintro ⟨a, rfl⟩
        refine ⟨((measuredIso_chartOf hc (𝓦)).iso.hom.map ⟨a.val, hA' a.property⟩).property, ?_⟩
        intro hcore
        exact a.property.2 ⟨a.property.1, hcore⟩
      · rintro ⟨htW, hnot⟩
        exact ⟨⟨t, mem_rawDom _ ⟨t, htW⟩, fun h => hnot h.2⟩, rfl⟩
    have heq := LiftClasses.restrict_congr (𝓦) himg
      (rvLabelImage_subset (measuredIso_chartOf hc (𝓦)).iso A' hA') (fun _ h => h.1)
    have e2 := e1.symm
    rw [heq] at e2
    exact ⟨e2⟩
  exact cls_eq_iff.mpr ⟨isoOfMeasured hc ((isoS hc D R hj hact hend h00).comp e)⟩

/-- **Gluing.** The relative annular object `U^{τ,j}` of an `∞`-free datum is
isomorphic, as a chart, to the chart of the contraction `W`. -/
theorem annular_cls : cls D.annularObject = cls (wObj hc D R hj hact hend h00) := by
  rw [ElementaryBlowups.cls_annular, shell_cls hc D R hj hact hend h00, core_cls hc D R hj hact hend h00,
    cls_partition (wObj hc D R hj hact hend h00) (Icore D) (Icore_definable D)]
  exact add_comm _ _

end Glue

/-! ### Lemma 7.12 at object level -/

section Final
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Theorem726
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  (B₀ : VFGeneratedFieldBase T) (hntB : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include B₀ hntB in
/-- **Lemma 7.12 (`blowup:same:RV:coa`), elementary blowups, object level.**
For every aperture datum `D`, the lift of the relative annular object
`U^{τ,j}` is isomorphic in `μVF^◇[1+k]` to the lift of `U`. -/
theorem lemma_7_12_objects (D : AnnularDatum (BT T) k) :
    Isomorphic G (liftOf G h00 hc hκ hs hv T hsmall hΓ D.annularObject)
      (liftOf G h00 hc hκ hs hv T hsmall hΓ D.source) := by
  have hE := DiamondGroupoid.isomorphic_equivalence (G := G) (S := (T : Set M)) (n := 1 + k) h00 hc hκ.le hs
    hsmall hv
  let D' := BlowupLiftGeneral.strictDatum h00 D
  have hn : MeasuredRVBounds.NoInfinity D'.chart := strictChart_infinityFree h00 D.chart
  obtain ⟨L⟩ := lemma_6_30_tuple_vfGenerated (G := G) hc h00 hκ.le hs hv T B₀ hntB hsmall hΓ (centreRelation D')
  obtain ⟨Δ, hΔ, hΔ1, hΔb⟩ := Remark74.remark_7_4_named hc h00 D'.chart D'.aperture
  have hU := (dbOf hc h00 hκ hs T hsmall hΓ D'.chart D'.bounded hn).2
  have hP := measuredRVLift_properInvariant h00 hc hκ hs hv _ hU
  let R := apertureData (G := G) hc D' L hv hU hP Δ hΔ hΔ1 hΔb
  have hj : R.coordinate = D'.coordinate := apertureData_coordinate hc D' L hv hU hP Δ hΔ hΔ1 hΔb
  have hact := apertureData_active hc D' L hv hU hP Δ hΔ hΔ1 hΔb
  have hend := apertureData_endpoint hc D' L hv hU hP Δ hΔ hΔ1 hΔb
  have hiso := lift_isomorphic hc D' R hj hact hend hv h00 hκ hs hsmall hΓ
  have hWdb := W_doublyBounded hc D' R hj hact hend h00
  obtain ⟨F1⟩ := cls_eq_iff.mp (BlowupLiftGeneral.strict_annular h00 D)
  obtain ⟨F2⟩ := cls_eq_iff.mp (annular_cls hc D' R hj hact hend h00)
  let F : Iso (strictChart h00 D.annularObject.toChart) (chartOf hc (W hc D' R hj hact hend h00)) :=
    RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm (strictIso h00 D.annularObject.toChart))
      (RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm F1) F2)
  let e : MeasuredRVIso (dbObj hc h00 hκ hs T hsmall hΓ D.annularObject).1 (W hc D' R hj hact hend h00) :=
    (measuredIso hc F).comp (measuredIso_chartOf hc _)
  obtain ⟨Φ, -⟩ := lemma_6_33_diamond (G := G) h00 hc lin hκ hs hv T B₀ hsmall hΓ hntB e
    (dbObj hc h00 hκ hs T hsmall hΓ D.annularObject).2 hWdb
    (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ D.annularObject).2)
    (measuredRVLift_properInvariant h00 hc hκ hs hv _ hWdb)
  exact hE.trans ⟨Φ⟩ (hE.symm hiso)

include B₀ hntB in
/-- Isomorphic charts have isomorphic lifts in `μVF^◇[k]` (Lemma 6.33 through
the strict forms). -/
theorem lift_congr {a b : Obj (BT T) k} (F : Iso a.toChart b.toChart) :
    Isomorphic G (liftOf G h00 hc hκ hs hv T hsmall hΓ a) (liftOf G h00 hc hκ hs hv T hsmall hΓ b) := by
  obtain ⟨e⟩ := dbObj_iso hc h00 hκ hs T hsmall hΓ F
  obtain ⟨Φ, -⟩ := lemma_6_33_diamond (G := G) h00 hc lin hκ hs hv T B₀ hsmall hΓ hntB e
    (dbObj hc h00 hκ hs T hsmall hΓ a).2 (dbObj hc h00 hκ hs T hsmall hΓ b).2
    (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2)
    (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ b).2)
  exact ⟨Φ⟩

include B₀ hntB in
/-- Lemma 7.12 for an elementary blowup of an object isomorphic to the source:
if `U ≅ V` in `μRV^db[1+k]`, then `𝕃 U^{τ,j} ≅ 𝕃 V` in `μVF^◇[1+k]`. -/
theorem lemma_7_12_objects_of_iso (D : AnnularDatum (BT T) k) {V : Obj (BT T) (1 + k)}
    (F : Iso D.source.toChart V.toChart) :
    Isomorphic G (liftOf G h00 hc hκ hs hv T hsmall hΓ D.annularObject)
      (liftOf G h00 hc hκ hs hv T hsmall hΓ V) :=
  (DiamondGroupoid.isomorphic_equivalence (G := G) (S := (T : Set M)) (n := 1 + k) h00 hc hκ.le hs
    hsmall hv).trans (lemma_7_12_objects h00 hc hκ hs hv T hsmall hΓ B₀ hntB D)
    (lift_congr h00 hc hκ hs hv T hsmall hΓ B₀ hntB F)

end Final

end DiamondIntegral.Section7.Lemma712Objects
