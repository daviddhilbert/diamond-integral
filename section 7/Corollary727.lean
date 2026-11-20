import «section 7».Remark728
import «section 7».PieceCombination
import «section 7».Proposition724Zero
import «section 7».RingClasses
import FubiniTheorems.Fubini.Completed18GroundLiftInput

/-! Corollary 7.27 (`db:to:novol`): the diagram (diag-diamond-interpol) commutes.

```
K VF_*              ←  K μVF^◇[*]            →  K μVF[*]
  ↓ ∫                    ↓ ∫^◇                    ↓ ∫^μ
K RV[*]/(P - 1)     ←  K μRV^db[*]/J_var     →  K μRV[*]/(P)
```

The paper's proof: the image of `[A]` under any of the three integrals is
represented by a standard contraction of `A`. This file proves the **left
square** on the classes of objects, over the real part `T` of a Section 3
ground context `C` (as in Remark 7.28):

* The bottom-left arrow (`bottomLeft`) is the ring map
  `K μRV^db[*]/J_var → K RV[*]/(P - 1)` induced by forgetting volume forms
  (`RVOrdinaryMaps.boundedForget`), followed by the extension of the base from
  `⟨T, ∅⟩` to `⟨T, Γ⟩` (`ordinaryExt`) and the quotient by `P - 1`. It kills
  `J_var` by Lemma 4.18 (`manuscriptIdeal_le_forget_kernel`). Its target is
  the ring `RVOrdinaryPNormalization.Ring C.base`, where Section 3's integral
  `nativeVFChartIntegral` lands.
* The top-left arrow is `Remark728.forgetVF` (forget the form; morphisms of
  `μVF^◇` are bijections, so isomorphic objects have equal classes,
  `Remark728.forgetVF_iso`).
* `∫^◇[A]` is taken through a standard contraction, with no input: for an
  object `A` of `μVF^◇[n+1]` and **any** standard contraction `F` of `A`, the
  class of `F` (`PieceCombination.clsOf`) modulo `J_var` represents
  `∫^◇[A]`; in degree `0`, `∫^◇` is the input-free
  `Proposition724Zero.integralZero`.

Proof (`corollary_7_27_left`): Remark 6.28 gives `A ≅ μ𝕃 W` with
`clsOf A F = [W]`. Forgetting forms sends this to an isomorphism of Section 3
VF objects, and `μ𝕃 W` to Section 3's lift of the RV object of `W`
(`Remark728.forgetVF_lift`); so `∫(forget A)` is the class of the chart of
`W` (`nativeVFChartIntegral_lift_class`, `Remark728.chart_ordinary_class`),
which is the bottom-left image of `[W]` (`bottomLeft_mk`). The statements
hold for every accepted Section 3 lift input, and in particular for the proved
`completed18GroundLiftInput`.

The right square (the measured integral `∫^μ`) is not formalized here; see
the Section 7 records. -/

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

end Context

end DiamondIntegral.Section7.Corollary727
