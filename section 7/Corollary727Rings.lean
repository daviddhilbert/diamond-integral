import «section 7».Corollary727
import «section 7».Theorem726
import «section 7».IsoOfMeasured

/-! Corollary 7.27 (`db:to:novol`) as equalities of ring maps.

```
K VF_*              ←  K μVF^◇[*]            →  K μVF[*]
  ↓ ∫                    ↓ ∫^◇                    ↓ ∫^μ
K RV[*]/(P - 1)     ←  K μRV^db[*]/J_var     →  K μRV[*]/(P)
```

`Corollary727` proves both squares on the classes of objects. Here the arrows
are ring maps out of the ring presentation `K μVF^◇[*] = DiamondRing.Ring`
(Theorem 7.26), and both squares commute as ring maps:

* `topLeft : K μVF^◇[*] → K VF_*` is induced by the forgetful functor
  (`Remark728.forgetVF`; the morphisms of `μVF^◇` are bijections, Remark 6.36).
  It is a ring map because forgetting forms commutes with products
  (`forgetVF_product`: the two product domains are the same set), with the
  scissor relations (`forgetVF_compl`), sends the empty object to `0`
  (`forgetVF_empty`) and the unit object, a single point with no labels
  (`one_carrier`), to `1`.
* `topRight : K μVF^◇[*] → K μVF[*]` is induced by the subcategory relation
  (`Corollary727.forgetMVF`). Its values are read through `∫^μ`, which is
  injective (Theorem 3.22 gives an inverse, `measuredIntegral_injective`): the
  object form of the right square (`right_object`) and the ring isomorphism
  `∫^◇` show that it respects products, sums, isomorphisms, the empty object
  and the unit. (The definition uses the standing base data `B₀ hntB` only in
  these proofs; its value on an object is the class of the object.)
* `∫^◇` is `Theorem726.theorem_7_26`; the bottom arrows are
  `Corollary727.bottomLeft` and `Corollary727.bottomRight`.

The object forms `left_object` and `right_object` hold for **every** object of
`μVF^◇[k]`, any `k`: the object is isomorphic to the lift of a chart object
(`Theorem726.exists_chart_lift`), whose integrals are computed by
`Corollary727.integral_forgetVF_lift` and `measuredIntegral_forgetMVF_lift`, and
the chart of the strict lift is isomorphic to the chart (`chartIso`). The ring
statements then follow from `DiamondRing.hom_ext`.

Headlines: `corollary_7_27_left_ring` (for every accepted Section 3 lift input,
in particular the proved `completed18GroundLiftInput`),
`corollary_7_27_right_ring`, and `corollary_7_27_rings` (both). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Corollary727Rings
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section5
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondGrothendieck
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.BaseExtension DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.DiamondRing DiamondIntegral.Section7.Corollary727

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hΓ : NontrivialDefinableGamma (⟨(C.real : Set M), ∅⟩ : ParameterBase M))
variable (B₀ : VFGeneratedFieldBase C.real) (hntB : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- `K μVF^◇[*]` over the real part of the context. -/
abbrev KVF := Theorem726.KVF G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ

/-- The unit object of `K μVF^◇[*]`. -/
abbrev one := Theorem726.unitObj G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ

/-- The lift of a chart object. -/
abbrev liftOf {k : ℕ} (a : Obj (BT C.real) k) :=
  Theorem726.liftOf G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ a

/-- `∫^◇` (Theorem 7.26). -/
abbrev intD := Theorem726.theorem_7_26 G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ B₀ hntB

theorem intD_liftOf {k : ℕ} (a : Obj (BT C.real) k) :
    intD G C hc hv hΓ B₀ hntB (ringClass G hc (one G C hc hv hΓ) (liftOf G C hc hv hΓ a)) =
      Ideal.Quotient.mk _ (RVBoundedRing.objectClass a) := by
  exact (Theorem726.integralRing_ringClass G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ B₀ hntB
    (Theorem726.productHyp G C.model00 hc C.uncountable C.saturated hv C.real C.small_real)
    (Theorem726.liftProductHyp G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ) _).trans
    (Theorem726.intQ_lift G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ B₀ hntB a)

/-- The chart of the strict lift of a chart object is isomorphic to it. -/
def chartIso {k : ℕ} (a : Obj (BT C.real) k) :
    Iso (chartOf hc (dbObj hc C.model00 C.uncountable C.saturated C.real C.small_real hΓ a).1) a.toChart :=
  IsoOfMeasured.isoOfMeasured hc ((measuredIso_chartOf hc _).comp
    (MeasuredRVBridge.measuredIso hc (RVMeasuredIsomorphisms.symm (StrictCharts.strictIso C.model00 a.toChart))))

theorem ordinary_chartIso {k : ℕ} {c d : Chart (BT C.real) k} (F : Iso c d) :
    RVOrdinaryRing.objectClass (chartExt (transfer C) c) = RVOrdinaryRing.objectClass (chartExt (transfer C) d) :=
  RVOrdinaryRing.objectClass_iso (a := chartExt (transfer C) c) (b := chartExt (transfer C) d)
    ⟨F.equiv, (transfer C) F.graph_definable⟩

theorem measured_chartIso {k : ℕ} {c d : Chart (BT C.real) k} (F : Iso c d) :
    Section3RVClassCuts.measuredClass (Section3MeasuredRVChartBridge.native hc (chartExt (transfer C) c)) =
      Section3RVClassCuts.measuredClass (Section3MeasuredRVChartBridge.native hc (chartExt (transfer C) d)) := by
  rw [← Section3RVRingEquivalences.measured_class, ← Section3RVRingEquivalences.measured_class,
    RVChartRing.objectClass_iso (isoExt (transfer C) F)]

theorem left_object (H : YinGammaGroundUnmeasuredLiftInput C hc) {k : ℕ}
    (A : DiamondCategory.VFObject (M := M) (C.real : Set M) k) :
    nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))) =
      bottomLeft C (intD G C hc hv hΓ B₀ hntB (ringClass G hc (one G C hc hv hΓ) A)) := by
  obtain ⟨a, ha⟩ := Theorem726.exists_chart_lift G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ
    B₀ hntB A
  rw [ringClass_iso G hc _ ha, intD_liftOf, bottomLeft_mk, integral_forgetVF_lift C hc H A _ _ ha,
    ordinary_chartIso C (chartIso C hc hΓ a)]

theorem right_object [CharZero (VF M)] {k : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) k) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    theorem_3_22_measured_graded C hc hv
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A))) =
      bottomRight C hc (intD G C hc hv hΓ B₀ hntB (ringClass G hc (one G C hc hv hΓ) A)) := by
  obtain ⟨a, ha⟩ := Theorem726.exists_chart_lift G C.model00 hc C.uncountable C.saturated hv C.real C.small_real hΓ
    B₀ hntB A
  rw [ringClass_iso G hc _ ha, intD_liftOf, bottomRight_mk, measuredIntegral_forgetMVF_lift C hc hv A _ _ ha,
    measured_chartIso C hc (chartIso C hc hΓ a)]

/-! ### The top-left arrow `K μVF^◇[*] → K VF_*` -/

section TopLeft

/-- Two Section 3 finite VF objects with the same arities and domain are equal. -/
theorem finiteVF_ext {n r : ℕ} {D D' : GammaGroundDefSet hc C.base (rawMixedSpace (M := M) n r)} (h : D = D')
    (f : ∀ a, {t | (a, t) ∈ D.carrier}.Finite) (f' : ∀ a, {t | (a, t) ∈ D'.carrier}.Finite) :
    (⟨n, r, D, f⟩ : GammaGroundFiniteVFObject hc C.base) = ⟨n, r, D', f'⟩ := by
  subst h
  rfl

theorem forgetVF_product {k l : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) k)
    (B : DiamondCategory.VFObject (M := M) (C.real : Set M) l) :
    Remark728.forgetVF hc C (DiamondProduct.VFObject.product hc A B) =
      (Remark728.forgetVF hc C A).product (Remark728.forgetVF hc C B) := by
  have h : (GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) (DiamondProduct.VFObject.product hc A B).carrier) =
      gammaGroundMixedProductDomain (GammaGroundDefSet.ofReal A.carrier) (GammaGroundDefSet.ofReal B.carrier) := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    ext p
    rw [mem_gammaGroundMixedProductDomain]
    exact mem_mixedProductDomain A.carrier B.carrier p
  exact finiteVF_ext C hc h _ _

theorem forgetVF_compl {k : ℕ} (U : DiamondCategory.VFObject (M := M) (C.real : Set M) k)
    (X : DefSet (rawMixedSpace (M := M) k U.labels) (C.real : Set M)) (hP : ProperInvariant (C.real : Set M) X.carrier) :
    Remark728.forgetVF hc C (complObject U X hP) =
      (Remark728.forgetVF hc C U).restrict ((Remark728.forgetVF hc C U).domain.sdiff (GammaGroundDefSet.ofReal X))
        (fun _ h => h.1) := by
  have h : (GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) (complObject U X hP).carrier) =
      (Remark728.forgetVF hc C U).domain.sdiff (GammaGroundDefSet.ofReal X) := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    rfl
  exact finiteVF_ext C hc h _ _

theorem forgetVF_empty (k : ℕ) :
    gammaGroundVFSemiringClass (Remark728.forgetVF hc C (emptyObject (S := (C.real : Set M)) hc k)) = 0 := by
  let f : GammaGroundBijection (Remark728.forgetVF hc C (emptyObject (S := (C.real : Set M)) hc k)).domain
      (GammaGroundFiniteVFObject.empty hc C.base).domain := GammaGroundBijection.ofEmpty rfl rfl
  rw [gammaGroundVFSemiringClass_iso (CategoryTheory.asIso (show Remark728.forgetVF hc C (emptyObject (S := (C.real : Set M)) hc k) ⟶
    GammaGroundFiniteVFObject.empty hc C.base from f)), gammaGroundVFSemiringClass_empty]

/-- The unit object of `μVF^◇[0]` is a single point with no labels. -/
theorem one_carrier : (one G C hc hv hΓ).carrier.carrier = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hd : (StrictCharts.strictChart C.model00 (RVBoundedRing.unit (BT C.real)).toChart).domain.Nonempty :=
    Set.Nonempty.image _ ⟨fun i => i.elim0, Set.mem_univ _⟩
  rw [← IsoOfMeasured.rvValues_image_rawDefSet hc _
    (StrictCharts.strictChart C.model00 (RVBoundedRing.unit (BT C.real)).toChart).domain_definable] at hd
  obtain ⟨u, hu⟩ := hd.of_image
  exact ⟨⟨u, hu⟩, funext fun i => i.elim0, funext fun i => i.elim0⟩

theorem forgetVF_one : gammaGroundVFSemiringClass (Remark728.forgetVF hc C (one G C hc hv hΓ)) = 1 := by
  let f : GammaGroundBijection (Remark728.forgetVF hc C (one G C hc hv hΓ)).domain
      (GammaGroundFiniteVFObject.unit hc C.base).domain := GammaGroundBijection.ofCarrierEq (one_carrier G C hc hv hΓ)
  rw [gammaGroundVFSemiringClass_iso (CategoryTheory.asIso (show Remark728.forgetVF hc C (one G C hc hv hΓ) ⟶
    GammaGroundFiniteVFObject.unit hc C.base from f)), gammaGroundVFSemiringClass_unit]

/-- The forgetful map, as an invariant of the ring presentation of `K μVF^◇[*]`. -/
def forgetInvariant : RingInvariant G hc (one G C hc hv hΓ) (GammaGroundVFGrothendieckRing hc C.base) where
  value _ A := Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A))
  unit := by rw [forgetVF_one]; rfl
  product _ _ A B := by
    rw [forgetVF_product, gammaGroundVFSemiringClass_product, ← Algebra.GrothendieckAddGroup.of_mul_of]
  iso _ _ _ h := by rw [Remark728.forgetVF_iso hc C h]
  empty k := by rw [forgetVF_empty, map_zero]
  scissor k U X hX hP := by
    rw [← map_add]
    congr 1
    have h := PositiveGrothendieck.of_scissor (gammaGroundVFSemiringPresentation hc C.base)
      (a := Remark728.forgetVF hc C (restrictObject U X hX hP))
      (b := Remark728.forgetVF hc C (complObject U X hP)) (c := Remark728.forgetVF hc C U)
      (d := GammaGroundFiniteVFObject.empty hc C.base)
      ⟨Remark728.forgetVF hc C U, GammaGroundDefSet.ofReal X, hX, rfl, forgetVF_compl C hc U X hP, rfl, rfl⟩
    have he : PositiveGrothendieck.of (gammaGroundVFSemiringPresentation hc C.base)
        (GammaGroundFiniteVFObject.empty hc C.base) = 0 := PositiveGrothendieck.of_empty _
    rw [he, add_zero] at h
    exact h

/-- **The top-left arrow `K μVF^◇[*] → K VF_*`** of (diag-diamond-interpol),
induced by the forgetful functor (forget the volume forms; Remark 6.36: the
morphisms of `μVF^◇` are bijections). -/
def topLeft : KVF G C hc hv hΓ →+* GammaGroundVFGrothendieckRing hc C.base :=
  DiamondRing.lift (forgetInvariant G C hc hv hΓ)

theorem topLeft_ringClass {k : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) k) :
    topLeft G C hc hv hΓ (ringClass G hc (one G C hc hv hΓ) A) =
      Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (Remark728.forgetVF hc C A)) :=
  lift_ringClass _ A

end TopLeft

/-- **Corollary 7.27, left square, as an equality of ring maps**:
`∫ ∘ forget = bottomLeft ∘ ∫^◇ : K μVF^◇[*] → K RV[*]/(P - 1)`, for every
accepted Section 3 lift input. -/
theorem corollary_7_27_left_ring (H : YinGammaGroundUnmeasuredLiftInput C hc) :
    (nativeVFChartIntegral H).comp (topLeft G C hc hv hΓ) =
      (bottomLeft C).comp (intD G C hc hv hΓ B₀ hntB).toRingHom := by
  apply DiamondRing.hom_ext
  intro k A
  rw [RingHom.comp_apply, RingHom.comp_apply, topLeft_ringClass]
  exact left_object G C hc hv hΓ B₀ hntB H A

/-! ### The top-right arrow `K μVF^◇[*] → K μVF[*]` -/

section TopRight
variable [CharZero (VF M)]

/-- The ring structure of `K μVF[*]` used by Section 3's `∫^μ`. -/
abbrev mvfSemiring : CommSemiring (GammaGroundMeasuredVFDirectSum C hc hv) :=
  gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
    (completedGammaGroundDegreeMeasuredLiftInput C hc hv)

/-- `∫^μ` is injective (Theorem 3.22: it has an inverse). -/
theorem measuredIntegral_injective :
    letI := mvfSemiring G C hc hv
    Function.Injective (theorem_3_22_measured_graded C hc hv) := by
  let _ := mvfSemiring G C hc hv
  intro x y h
  have hx : theorem_3_22_measured_graded_inverse C hc hv (theorem_3_22_measured_graded C hc hv x) = x :=
    DFunLike.congr_fun (theorem_3_22_measured_graded_inverse_comp C hc hv) x
  have hy : theorem_3_22_measured_graded_inverse C hc hv (theorem_3_22_measured_graded C hc hv y) = y :=
    DFunLike.congr_fun (theorem_3_22_measured_graded_inverse_comp C hc hv) y
  rw [← hx, ← hy, h]

/-- The inclusion `μVF^◇ ⊆ μVF`, as an invariant of the ring presentation of
`K μVF^◇[*]`. Additivity and multiplicativity are read off through `∫^μ`, which
is injective, from the object form of the right square (`right_object`) and the
ring isomorphism `∫^◇`. -/
def forgetMInvariant :
    letI := mvfSemiring G C hc hv
    RingInvariant G hc (one G C hc hv hΓ) (RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)) := by
  letI := mvfSemiring G C hc hv
  exact
  { value := fun _ A => Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A))
    unit := by
      apply measuredIntegral_injective G C hc hv
      rw [right_object G C hc hv hΓ B₀ hntB, ringClass_one, map_one, map_one, map_one]
    product := fun _ _ A B => by
      apply measuredIntegral_injective G C hc hv
      rw [map_mul, right_object G C hc hv hΓ B₀ hntB, right_object G C hc hv hΓ B₀ hntB,
        right_object G C hc hv hΓ B₀ hntB, ringClass_product, map_mul, map_mul]
    iso := fun _ A B h => by
      apply measuredIntegral_injective G C hc hv
      rw [right_object G C hc hv hΓ B₀ hntB, right_object G C hc hv hΓ B₀ hntB, ringClass_iso G hc _ h]
    empty := fun k => by
      apply measuredIntegral_injective G C hc hv
      rw [right_object G C hc hv hΓ B₀ hntB, ringClass_empty, map_zero, map_zero, map_zero]
    scissor := fun k U X hX hP => by
      apply measuredIntegral_injective G C hc hv
      rw [map_add, right_object G C hc hv hΓ B₀ hntB, right_object G C hc hv hΓ B₀ hntB,
        right_object G C hc hv hΓ B₀ hntB, ← map_add, ← map_add, ringClass_scissor] }

/-- **The top-right arrow `K μVF^◇[*] → K μVF[*]`** of (diag-diamond-interpol),
induced by the subcategory relation `μVF^◇ ⊆ μVF` (`forgetMVF`). -/
def topRight :
    letI := mvfSemiring G C hc hv
    KVF G C hc hv hΓ →+* RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv) := by
  letI := mvfSemiring G C hc hv
  exact DiamondRing.lift (forgetMInvariant G C hc hv hΓ B₀ hntB)

theorem topRight_ringClass {k : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) k) :
    letI := mvfSemiring G C hc hv
    topRight G C hc hv hΓ B₀ hntB (ringClass G hc (one G C hc hv hΓ) A) =
      Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (forgetMVF C hc A)) := by
  let _ := mvfSemiring G C hc hv
  exact lift_ringClass _ A

/-- **Corollary 7.27, right square, as an equality of ring maps**:
`∫^μ ∘ incl = bottomRight ∘ ∫^◇ : K μVF^◇[*] → K μRV[*]/(P)`. -/
theorem corollary_7_27_right_ring :
    letI := mvfSemiring G C hc hv
    (theorem_3_22_measured_graded C hc hv).toRingHom.comp (topRight G C hc hv hΓ B₀ hntB) =
      (bottomRight C hc).comp (intD G C hc hv hΓ B₀ hntB).toRingHom := by
  let _ := mvfSemiring G C hc hv
  apply DiamondRing.hom_ext
  intro k A
  rw [RingHom.comp_apply, RingHom.comp_apply, topRight_ringClass]
  exact right_object G C hc hv hΓ B₀ hntB A

end TopRight

/-- **Corollary 7.27 (`db:to:novol`), as equalities of ring maps**: both squares
of (diag-diamond-interpol) commute, with Section 3's integral `∫` for the proved
lift record `completed18GroundLiftInput`. -/
theorem corollary_7_27_rings [CharZero (VF M)] :
    (nativeVFChartIntegral (completed18GroundLiftInput C hc)).comp (topLeft G C hc hv hΓ) =
      (bottomLeft C).comp (intD G C hc hv hΓ B₀ hntB).toRingHom ∧
    (letI := mvfSemiring G C hc hv
     (theorem_3_22_measured_graded C hc hv).toRingHom.comp (topRight G C hc hv hΓ B₀ hntB) =
      (bottomRight C hc).comp (intD G C hc hv hΓ B₀ hntB).toRingHom) :=
  ⟨corollary_7_27_left_ring G C hc hv hΓ B₀ hntB _, corollary_7_27_right_ring G C hc hv hΓ B₀ hntB⟩

end DiamondIntegral.Section7.Corollary727Rings
