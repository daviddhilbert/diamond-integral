import «section 4».Section3RVRestrictionBridge
import «section 4».RVRestrictionInvariants
import «section 3».GammaGroundMeasuredRVSemiring
import «section 3».GammaGroundRVSemiring
import «section 3».GammaGroundCarrierBijections
import «section 3».CompletionFunctor

/-! The actual native ordinary and measured classes satisfy every chart
scissor relation. No presentation equivalence is assumed here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RVClassCuts
open RVMeasuredCharts Section3RVCodeBridge RVChartDisjointUnion RVChartRestrictions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinaryClass {k : ℕ} (U : GammaGroundRVObject hc B k) : GammaGroundRVGrothendieckRing hc B :=
  of (gammaGroundRVSemiringClass U)

def measuredClass {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k) : GammaGroundMeasuredRVGrothendieckRing hc B :=
  of (gammaGroundMeasuredRVSemiringClass U)

theorem ordinary_iso {k : ℕ} {U V : GammaGroundRVObject hc B k}
    (f : GammaGroundBijection U.domain V.domain) : ordinaryClass U = ordinaryClass V :=
  congrArg of (PositiveGrothendieck.of_iso (gammaGroundRVSemiringPresentation hc B) ⟨rfl, ⟨f⟩⟩)

theorem measured_iso {k : ℕ} {U V : GammaGroundMeasuredRVObject hc B k}
    (f : GammaGroundMeasuredRVHom U V) : measuredClass U = measuredClass V :=
  congrArg of (gammaGroundMeasuredRVSemiringClass_iso (asIso (show U ⟶ V from f)))

@[simp] theorem ordinary_empty (k : ℕ) : ordinaryClass (GammaGroundRVObject.empty hc B k) = 0 := by
  simp [ordinaryClass]

@[simp] theorem measured_empty (k : ℕ) : measuredClass (GammaGroundMeasuredRVObject.empty hc B k) = 0 := by
  simp [measuredClass]

theorem ordinary_cut {k : ℕ} (U : GammaGroundRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier) :
    ordinaryClass (U.restrict X hX) + ordinaryClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) =
      ordinaryClass U := by
  have h := congrArg (of : GammaGroundRVPositiveSemiring hc B → GammaGroundRVGrothendieckRing hc B)
    (gammaGroundRVSemiringClass_scissor ⟨U, X, hX, rfl, rfl, rfl, rfl⟩)
  simpa only [ordinaryClass, map_add, gammaGroundRVSemiringClass_empty, map_zero, add_zero] using h

theorem measured_cut {k : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    measuredClass (U.restrict X hX) + measuredClass (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1)) =
      measuredClass U := by
  have h := congrArg (of : GammaGroundMeasuredRVPositiveSemiring hc B → GammaGroundMeasuredRVGrothendieckRing hc B)
    (gammaGroundMeasuredRVSemiringClass_scissor ⟨U, X, hX, rfl, rfl, rfl, rfl⟩)
  simpa only [measuredClass, map_add, gammaGroundMeasuredRVSemiringClass_empty, map_zero, add_zero] using h

def complementIso {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    GammaGroundBijection
      ((Section3RVChartBridge.native hc a.toChart).restrict
        ((Section3RVChartBridge.native hc a.toChart).domain.sdiff (ofRaw (a.domain ∩ I) (a.domain_definable.inter hI)))
        (fun _ h => h.1)).domain
      (Section3RVChartBridge.native hc (outside a I hI).toChart).domain :=
  GammaGroundBijection.ofCarrierEq (by ext x; change (_ ∧ ¬ (_ ∧ _)) ↔ (_ ∧ ¬ _); tauto)

def measuredComplementIso {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    GammaGroundMeasuredRVHom
      ((Section3MeasuredRVChartBridge.native hc a.toChart).restrict
        ((Section3MeasuredRVChartBridge.native hc a.toChart).underlying.domain.sdiff
          (ofRaw (a.domain ∩ I) (a.domain_definable.inter hI))) (fun _ h => h.1))
      (Section3MeasuredRVChartBridge.native hc (outside a I hI).toChart) where
  bijection := complementIso a I hI
  preserves _ := rfl

theorem ordinary_partition {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    ordinaryClass (Section3RVChartBridge.native hc a.toChart) =
      ordinaryClass (Section3RVChartBridge.native hc (outside a I hI).toChart) +
        ordinaryClass (Section3RVChartBridge.native hc (inside a I hI).toChart) := by
  have h := ordinary_cut (Section3RVChartBridge.native hc a.toChart)
    (ofRaw (a.domain ∩ I) (a.domain_definable.inter hI)) (fun _ hx => hx.1)
  rw [ordinary_iso (complementIso a I hI), ordinary_iso
    (Section3RVRestrictionBridge.nativeRestrictionIso a.toChart (a.domain ∩ I)
      (a.domain_definable.inter hI) (fun _ hx => hx.1))] at h
  exact h.symm.trans (add_comm _ _)

theorem measured_partition {n k : ℕ} (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    measuredClass (Section3MeasuredRVChartBridge.native hc a.toChart) =
      measuredClass (Section3MeasuredRVChartBridge.native hc (outside a I hI).toChart) +
        measuredClass (Section3MeasuredRVChartBridge.native hc (inside a I hI).toChart) := by
  have h := measured_cut (Section3MeasuredRVChartBridge.native hc a.toChart)
    (ofRaw (a.domain ∩ I) (a.domain_definable.inter hI)) (fun _ hx => hx.1)
  rw [measured_iso (measuredComplementIso a I hI), measured_iso
    (Section3RVRestrictionBridge.nativeMeasuredRestrictionIso a.toChart (a.domain ∩ I)
      (a.domain_definable.inter hI) (fun _ hx => hx.1))] at h
  exact h.symm.trans (add_comm _ _)

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVRestrictionInvariants.Ordinary B (GammaGroundRVGrothendieckRing hc B) where
  value _ a := ordinaryClass (Section3RVChartBridge.native hc a)
  iso _ _ _ f := ordinary_iso (Section3RVRoundtripBridge.nativeIso f)
  partition := ordinary_partition

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVRestrictionInvariants.Measured B (GammaGroundMeasuredRVGrothendieckRing hc B) where
  value _ a := measuredClass (Section3MeasuredRVChartBridge.native hc a)
  iso _ _ _ f := measured_iso (Section3RVRoundtripBridge.nativeMeasuredIso f)
  partition := measured_partition

end DiamondIntegral.Section4.Section3RVClassCuts
