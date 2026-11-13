import «section 4».Section3RVClassCuts
import «section 4».RVAdmissibleRestrictionInvariants
import «section 3».GammaGroundRESGradedSemiring
import «section 3».GammaGroundMeasuredRESGradedSemiring

/-! Native RES completion classes satisfy actual chart cut additivity.
Finite value support is retained on every component, without inferring
injectivity after group completion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3RESClassCuts
open RVMeasuredCharts Section3RVCodeBridge RVChartDisjointUnion RVChartRestrictions RVAdmissibleFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

abbrev OrdinaryRing (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :=
  Algebra.GrothendieckAddGroup (GammaGroundRESDirectSum hc B)
abbrev MeasuredRing (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :=
  Algebra.GrothendieckAddGroup (GammaGroundMeasuredRESDirectSum hc B)

def ordinaryClass {k : ℕ} (U : GammaGroundRESObject hc B k) : OrdinaryRing hc B :=
  of (gammaGroundRESDirectSumClass U)
def measuredClass {k : ℕ} (U : GammaGroundMeasuredRESObject hc B k) : MeasuredRing hc B :=
  of (gammaGroundMeasuredRESDirectSumClass U)

def ordinaryComponent (k : ℕ) : GammaGroundRESKPlus hc B k →+ OrdinaryRing hc B :=
  of.comp (DirectSum.of (GammaGroundRESKPlus hc B) k)
def measuredComponent (k : ℕ) : GammaGroundMeasuredRESKPlus hc B k →+ MeasuredRing hc B :=
  of.comp (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) k)

theorem ordinary_iso {k : ℕ} {U V : GammaGroundRESObject hc B k}
    (f : GammaGroundBijection U.obj.domain V.obj.domain) : ordinaryClass U = ordinaryClass V :=
  congrArg (ordinaryComponent (hc := hc) (B := B) k)
    (gammaGroundRESClass_iso ((gammaGroundResProperty (hc := hc) (ground := B) (k := k)).isoMk
      (asIso (show U.obj ⟶ V.obj from f))))

theorem measured_iso {k : ℕ} {U V : GammaGroundMeasuredRESObject hc B k}
    (f : GammaGroundMeasuredRVHom U.obj V.obj) : measuredClass U = measuredClass V :=
  congrArg (measuredComponent (hc := hc) (B := B) k)
    (gammaGroundMeasuredRESClass_iso ((gammaGroundMeasuredResProperty (hc := hc) (ground := B) (k := k)).isoMk
      (asIso (show U.obj ⟶ V.obj from f))))

@[simp] theorem ordinary_empty (k : ℕ) : ordinaryClass (GammaGroundRESObject.empty hc B k) = 0 := by
  simp only [ordinaryClass, gammaGroundRESDirectSumClass, gammaGroundRESClass_empty, map_zero]
@[simp] theorem measured_empty (k : ℕ) : measuredClass (GammaGroundMeasuredRESObject.empty hc B k) = 0 := by
  simp only [measuredClass, gammaGroundMeasuredRESDirectSumClass, gammaGroundMeasuredRESClass_empty, map_zero]

theorem ordinary_cut {k : ℕ} (U : GammaGroundRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    ordinaryClass (U.restrict X hX) + ordinaryClass (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) = ordinaryClass U := by
  have h := congrArg (ordinaryComponent (hc := hc) (B := B) k) (gammaGroundRESClass_scissor U X hX)
  simpa only [ordinaryComponent, ordinaryClass, gammaGroundRESDirectSumClass, AddMonoidHom.comp_apply, map_add] using h

theorem measured_cut {k : ℕ} (U : GammaGroundMeasuredRESObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.obj.underlying.arity))
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) :
    measuredClass (U.restrict X hX) + measuredClass (U.restrict (U.obj.underlying.domain.sdiff X) (fun _ h => h.1)) = measuredClass U := by
  have h := congrArg (measuredComponent (hc := hc) (B := B) k) (gammaGroundMeasuredRESClass_scissor U X hX)
  simpa only [measuredComponent, measuredClass, gammaGroundMeasuredRESDirectSumClass, AddMonoidHom.comp_apply, map_add] using h

def ordinaryNative (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : Chart B k)
    (ha : (res B).good k a) : GammaGroundRESObject hc B k := Section3RVChartBridge.nativeRES hc ⟨a, ha⟩
def measuredNative (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (a : Chart B k)
    (ha : (res B).good k a) : GammaGroundMeasuredRESObject hc B k := Section3MeasuredRVChartBridge.nativeRES hc ⟨a, ha⟩

theorem ordinary_partition {n k : ℕ} (a : Data B n k) (ha : (res B).good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    ordinaryClass (ordinaryNative hc a.toChart ha) =
      ordinaryClass (ordinaryNative hc (outside a I hI).toChart ((res B).outside_good a I hI ha)) +
        ordinaryClass (ordinaryNative hc (inside a I hI).toChart ((res B).inside_good a I hI ha)) := by
  let U := ordinaryNative hc a.toChart ha
  let X := ofRaw (hc := hc) (a.domain ∩ I) (a.domain_definable.inter hI)
  have hX : X.carrier ⊆ U.obj.domain.carrier := fun _ hx => hx.1
  have hi : ordinaryClass (U.restrict X hX) =
      ordinaryClass (ordinaryNative hc (inside a I hI).toChart ((res B).inside_good a I hI ha)) :=
    ordinary_iso (Section3RVRestrictionBridge.nativeRestrictionIso a.toChart _ _ (fun _ hx => hx.1))
  have ho : ordinaryClass (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) =
      ordinaryClass (ordinaryNative hc (outside a I hI).toChart ((res B).outside_good a I hI ha)) :=
    ordinary_iso (Section3RVClassCuts.complementIso a I hI)
  have h := ordinary_cut U X hX
  rw [hi, ho] at h
  exact h.symm.trans (add_comm _ _)

theorem measured_partition {n k : ℕ} (a : Data B n k) (ha : (res B).good k a.toChart)
    (I : Set (Fin n → M)) (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    measuredClass (measuredNative hc a.toChart ha) =
      measuredClass (measuredNative hc (outside a I hI).toChart ((res B).outside_good a I hI ha)) +
        measuredClass (measuredNative hc (inside a I hI).toChart ((res B).inside_good a I hI ha)) := by
  let U := measuredNative hc a.toChart ha
  let X := ofRaw (hc := hc) (a.domain ∩ I) (a.domain_definable.inter hI)
  have hX : X.carrier ⊆ U.obj.underlying.domain.carrier := fun _ hx => hx.1
  have hi : measuredClass (U.restrict X hX) =
      measuredClass (measuredNative hc (inside a I hI).toChart ((res B).inside_good a I hI ha)) :=
    measured_iso (Section3RVRestrictionBridge.nativeMeasuredRestrictionIso a.toChart _ _ (fun _ hx => hx.1))
  have ho : measuredClass (U.restrict (U.obj.underlying.domain.sdiff X) (fun _ h => h.1)) =
      measuredClass (measuredNative hc (outside a I hI).toChart ((res B).outside_good a I hI ha)) :=
    measured_iso (Section3RVClassCuts.measuredComplementIso a I hI)
  have h := measured_cut U X hX
  rw [hi, ho] at h
  exact h.symm.trans (add_comm _ _)

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVAdmissibleRestrictionInvariants.Ordinary (res B) (OrdinaryRing hc B) where
  value _ a ha := ordinaryClass (ordinaryNative hc a ha)
  iso _ _ _ _ _ f := ordinary_iso (Section3RVRoundtripBridge.nativeIso f)
  partition := ordinary_partition

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    RVAdmissibleRestrictionInvariants.Measured (res B) (MeasuredRing hc B) where
  value _ a ha := measuredClass (measuredNative hc a ha)
  iso _ _ _ _ _ f := measured_iso (Section3RVRoundtripBridge.nativeMeasuredIso f)
  partition := measured_partition

end DiamondIntegral.Section4.Section3RESClassCuts
