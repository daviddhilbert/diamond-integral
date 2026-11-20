import «section 7».KernelDimOne
import «section 7».BaseExtension
import «section 4».RVT001BoundedFactor
import FubiniTheorems.Fubini.NativeVFIntegral

/-! Remark 7.28 (`eg:eb:factor`): for proper invariant objects, `𝔼_g` and
`𝔼_b` differ by `[𝔸]^{-n}`.

Statement (`remark_7_28`): for an object `A` of `μVF^◇[n+1]` over the real part
of a Section 3 ground context, with Section 3's integral `∫` (any accepted lift
input; its values on lifts are fixed), `𝔼_g(∫[A]) = 𝔼_b(∫[A])·[𝔸]^{-(n+1)}`.

Proof, as in the paper:
1. A standard contraction gives `A ≅ 𝕃U` in `μVF^◇` with `U` doubly bounded
   (Remark 6.28; standard contractions exist by `remark_6_28_exists`).
2. Forgetting the volume forms (`forgetVF`) sends this isomorphism to an
   isomorphism of Section 3's VF objects, and `𝕃U` to Section 3's lift of `U`.
   So `∫[A] = [U]`, as a Section 4 ordinary chart class
   (`nativeVFChartIntegral_lift_class`).
3. That class is the forgetful image of a doubly bounded class of degree
   `n + 1` (Section 7's chart of `U`, with its base extended to the context's
   base, `BaseExtension`).
4. On such classes the geometric and bounded evaluations agree (the bounded
   RV decomposition), and `RVT001BoundedFactor.geometric_eq_bounded_mul`
   converts this into the stated identity.

The Section 3 context carries strong homogeneity (author decision,
2026-11-19). Section 6's objects live over the raw base `⟨T, ∅⟩` with `T` the
context's real part; Section 3's and Section 4's rings live over `⟨T, Γ⟩`, and
raw definable sets are definable there (`GammaGroundDefSet.ofReal`,
`BaseExtension`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Remark728
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section3 DiamondIntegral.Section5
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.BaseExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : GammaGroundContext M)

/-! ### Forgetting volume forms -/

/-- An object of `μVF^◇[n]` over the real part of the context, as a Section 3
VF object (its volume form forgotten). -/
def forgetVF {n : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) n) : GammaGroundFiniteVFObject hc C.base :=
  ⟨n, A.labels, GammaGroundDefSet.ofReal A.carrier, A.finiteRV⟩

/-- Isomorphic objects of `μVF^◇` have equal Section 3 classes. -/
theorem forgetVF_iso {n : ℕ} {A B : DiamondCategory.VFObject (M := M) (C.real : Set M) n} (F : Isomorphic G A B) :
    gammaGroundVFSemiringClass (forgetVF hc C A) = gammaGroundVFSemiringClass (forgetVF hc C B) := by
  obtain ⟨Φ⟩ := F
  apply gammaGroundVFSemiringClass_iso
  exact (CategoryTheory.Groupoid.isoEquivHom _ _).symm
    (⟨GammaGroundMap.ofReal (hc := hc) (ground := C.base) Φ.map, Φ.bijective⟩ : GammaGroundBijection _ _)

/-- The RV object of a measured RV object, as a Section 3 RV object. -/
def forgetRV {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n) :
    GammaGroundRVObject hc C.base n where
  arity := U.object.arity
  domain := GammaGroundDefSet.ofReal U.object.domain
  volume := GammaGroundMap.ofReal (hc := hc) (ground := C.base) U.object.volume
  finite := U.finiteVolume
  nonzero := U.nonzero

/-- The lift of a measured RV object forgets to Section 3's lift of its RV
object. -/
theorem forgetVF_lift {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n)
    (hP : ProperInvariant (C.real : Set M) (rvLift U.object).carrier) :
    gammaGroundVFSemiringClass (forgetVF hc C (liftObject U hP)) =
      gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite (forgetRV hc C U)) := by
  rfl

/-! ### The chart of a measured RV object -/

/-- Section 3's chart of the RV object of `U` and Section 7's chart of `U`,
with its base extended, have the same ordinary class. -/
theorem chart_ordinary_class {n : ℕ} (U : DiamondIntegral.Section6.MeasuredRVObject (M := M) (C.real : Set M) n) :
    DiamondIntegral.Section4.RVOrdinaryRing.objectClass (DiamondIntegral.Section4.Section3RVChartBridge.chart (forgetRV hc C U)) =
      DiamondIntegral.Section4.RVOrdinaryRing.objectClass (chartExt (B := ⟨(C.real : Set M), ∅⟩) (C := C.base) (fun _ h => h) (Set.empty_subset _) (chartOf hc U)) := by
  apply DiamondIntegral.Section4.RVOrdinaryRing.objectClass_iso
  exact DiamondIntegral.Section4.RVForgetScissors.ofMap _ _ id
    (DiamondIntegral.Section4.RVSharpCharts.identity_graph_definable C.base _ (DiamondIntegral.Section4.Section3RVCodeBridge.rawDomain_definable _))
    (Set.bijOn_id _)

/-! ### Remark 7.28 -/

section Main
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hnt : ∃ x : C.fieldBase.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hΓ : NontrivialDefinableGamma (⟨(C.real : Set M), ∅⟩ : ParameterBase M))

/-- The ordinary T001 presentation over the context's base (constructed from
Section 3). -/
abbrev presentation : DiamondIntegral.Section4.ApprovedT001Presentation.Ordinary C.base :=
  DiamondIntegral.Section4.Section3T001Integration.ordinary (hc := hc) C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

/-- `𝔼_g`, normalized by the affine class. -/
abbrev geometric := DiamondIntegral.Section4.RVT001OrdinaryNormalization.geometric C.model00 lin
  C.uncountable.le C.saturated C.base C.small_real C.small_gamma C.nontrivial_definable_gamma (presentation hc C)

/-- `𝔼_b`, mapped into the affine localization. -/
abbrev bounded := DiamondIntegral.Section4.RVT001NormalizedDistinct.boundedInAffine C.model00 lin
  C.uncountable.le C.saturated C.base C.small_real C.small_gamma C.nontrivial_definable_gamma (presentation hc C)

/-- The geometric and bounded evaluations agree on doubly bounded classes
(consequence of the bounded RV decomposition). -/
def BoundedIndependence : Prop :=
  DiamondIntegral.Section4.RVT001OrdinaryDescent.boundedEvaluation C.model00 lin C.uncountable.le C.saturated
      C.base C.small_real C.small_gamma C.nontrivial_definable_gamma (presentation hc C) .geometric =
    DiamondIntegral.Section4.RVT001OrdinaryDescent.boundedEvaluation C.model00 lin C.uncountable.le C.saturated
      C.base C.small_real C.small_gamma C.nontrivial_definable_gamma (presentation hc C) .bounded

include hv hnt hΓ in
/-- Remark 7.28 from the agreement of the two evaluations on doubly bounded
classes. -/
theorem remark_7_28_of_independence (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (hind : BoundedIndependence hc C) {n : ℕ} (A : DiamondCategory.VFObject (M := M) (C.real : Set M) (n + 1)) :
    geometric hc C (nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (forgetVF hc C A)))) =
      bounded hc C (nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (forgetVF hc C A)))) *
        IsLocalization.Away.invSelf (DiamondIntegral.Section4.RESAffineLocalization.dimensionFreeAffine C.base) ^ (n + 1) := by
  obtain ⟨hV, hVS, hSV, hnt'⟩ := vfGenerated_base_support C.real C.fieldBase hnt
  obtain ⟨F⟩ := remark_6_28_exists (G := G) C.model00 hc lin C.uncountable C.saturated hv
    (vfFieldNames C.fieldBase.field) C.small_real hΓ hV hVS hSV hnt' A 1
  obtain ⟨hP, iA⟩ := remark_6_28 C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ A F 0 Fin.elim0
  have hU : (F.headStartMeasuredObject C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ 0 Fin.elim0
      (object_hFin A Fin.elim0)).doublyBounded := F.headStartObject_doublyBounded 0 Fin.elim0
  have iA' : Isomorphic G A (liftObject _ hP) := iA
  rw [forgetVF_iso hc C iA', forgetVF_lift, nativeVFChartIntegral_lift_class, chart_ordinary_class]
  apply DiamondIntegral.Section4.RVT001BoundedFactor.geometric_eq_bounded_mul
  · exact DiamondIntegral.Section4.RVOrdinaryGrading.class_mem _ _
  · have hx : DiamondIntegral.Section4.RVOrdinaryMaps.boundedForget C.base
        (DiamondIntegral.Section4.RVBoundedRing.objectClass
          (objExt (B := ⟨(C.real : Set M), ∅⟩) (C := C.base) (fun _ h => h) (Set.empty_subset _)
            (objOf hc C.real _ hU))) =
        DiamondIntegral.Section4.RVOrdinaryRing.objectClass
          (chartExt (B := ⟨(C.real : Set M), ∅⟩) (C := C.base) (fun _ h => h) (Set.empty_subset _)
            (chartOf hc (F.headStartMeasuredObject C.model00 hc lin C.uncountable C.saturated hv C.small_real hΓ 0
              Fin.elim0 (object_hFin A Fin.elim0)))) :=
      DiamondIntegral.Section4.RVOrdinaryMaps.boundedForget_class C.base _
    rw [← hx]
    exact RingHom.congr_fun hind _

end Main

/-! ### Degree zero -/

section DegreeZero

omit [Valued (VF M) G] in
theorem labels_finite (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) :
    (rvTailMap A.carrier).image.carrier.Finite := by
  apply ((A.finiteRV Fin.elim0)).subset
  rintro _ ⟨p, rfl⟩
  have he : p.val = (Fin.elim0, p.val.2) := Prod.ext (funext (fun i => i.elim0)) rfl
  change (Fin.elim0, p.val.2) ∈ A.carrier.carrier
  rw [← he]
  exact p.property

omit [Valued (VF M) G] in
/-- The labels of an object of `μVF^◇[0]`, as an RV object of degree 0. -/
def labelsRV (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) : GammaGroundRVObject hc C.base 0 where
  arity := A.labels
  domain := GammaGroundDefSet.ofReal (rvTailMap A.carrier).image
  volume := GammaGroundMap.ofReal (hc := hc) (ground := C.base)
    ((rvTupleSelectMap _ (Fin.elim0 : Fin 0 → Fin A.labels)).comp (Map.inclusion (fun _ _ => Set.mem_univ _)))
  finite := by
    intro t
    exact ((labels_finite C A).preimage (f := fun u : (rvTailMap A.carrier).image => u.val)
      (fun x _ y _ he => Subtype.ext he)).subset (fun x _ => x.property)
  nonzero := fun _ i => i.elim0

omit [Valued (VF M) G] in
/-- An object of `μVF^◇[0]` forgets to Section 3's lift of its labels. -/
theorem forgetVF_zero (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) :
    forgetVF hc C A = gammaGroundObjectLiftFinite (labelsRV hc C A) := by
  have hcarrier : (GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) A.carrier).carrier =
      (gammaGroundObjectLift (labelsRV hc C A)).carrier := by
    ext q
    constructor
    · intro hq
      refine ⟨⟨q.2, ⟨⟨q, hq⟩, rfl⟩⟩, rfl, ?_⟩
      funext i
      exact i.elim0
    · rintro ⟨u, hu, -⟩
      obtain ⟨p, hp⟩ := u.property
      have he : q = p.val := Prod.ext (funext (fun i => i.elim0)) (hu.symm.trans hp.symm)
      rw [he]
      exact p.property
  unfold forgetVF gammaGroundObjectLiftFinite
  congr 1
  cases h : GammaGroundDefSet.ofReal (hc := hc) (ground := C.base) A.carrier
  cases h' : gammaGroundObjectLift (labelsRV hc C A)
  rw [h, h'] at hcarrier
  simp only [GammaGroundDefSet.mk.injEq]
  exact hcarrier

/-- Remark 7.28 in degree 0: `𝔼_g(∫[A]) = 𝔼_b(∫[A])`. -/
theorem remark_7_28_zero_of_independence (H : YinGammaGroundUnmeasuredLiftInput C hc)
    (hind : BoundedIndependence hc C) (A : DiamondCategory.VFObject (M := M) (C.real : Set M) 0) :
    geometric hc C (nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (forgetVF hc C A)))) =
      bounded hc C (nativeVFChartIntegral H (Algebra.GrothendieckAddGroup.of (gammaGroundVFSemiringClass (forgetVF hc C A)))) *
        IsLocalization.Away.invSelf (DiamondIntegral.Section4.RESAffineLocalization.dimensionFreeAffine C.base) ^ 0 := by
  rw [forgetVF_zero, nativeVFChartIntegral_lift_class]
  let c := DiamondIntegral.Section4.Section3RVChartBridge.chart (labelsRV hc C A)
  have hfin : c.domain.Finite := (labels_finite C A).image _
  have hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c := by
    apply DiamondIntegral.Section4.RVMeasuredBounds.finite_patterns_bounded
    have : Finite c.domain := hfin.to_subtype
    exact Set.finite_range _
  apply DiamondIntegral.Section4.RVT001BoundedFactor.geometric_eq_bounded_mul
  · exact DiamondIntegral.Section4.RVOrdinaryGrading.class_mem _ _
  · have hx : DiamondIntegral.Section4.RVOrdinaryMaps.boundedForget C.base
        (DiamondIntegral.Section4.RVBoundedRing.objectClass (⟨c, hb⟩ : DiamondIntegral.Section4.RVBoundedCharts.BoundedChart C.base 0)) =
        DiamondIntegral.Section4.RVOrdinaryRing.objectClass c :=
      DiamondIntegral.Section4.RVOrdinaryMaps.boundedForget_class C.base _
    rw [← hx]
    exact RingHom.congr_fun hind _

end DegreeZero

end DiamondIntegral.Section7.Remark728
