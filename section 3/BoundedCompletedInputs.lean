import «section 3».BoundedNativeIntegral
import «section 5».Completed18GroundLiftInput

/-! Theorem 3.22, bounded part: the complete Gamma-ground bounded input
record is constructed from [18]. The fixed-degree integral of [18] is
applied over the definable closure of the ground, which has the same
definable sets; no new input is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-- The bounded unmeasured input of Theorem 3.22 over the complete Gamma
ground, proved from the fixed-degree integral of [18]. -/
def completedGammaGroundBoundedLiftInput :
    YinGammaGroundBoundedUnmeasuredLiftInput (G := G) C hc hv := by
  let D := closureBase C.base
  let δ : Values.Gamma (M := M) := (completed18ContextPositive C).choose
  have hδ : δ ∈ C.base.gamma := (completed18ContextPositive C).choose_spec.1
  have hδ1 : 1 < δ := (completed18ContextPositive C).choose_spec.2
  have hr : Cardinal.mk D.real < C.κ :=
    closureBase_real_small C.uncountable C.base C.small_real C.small_gamma
  have hγ : Cardinal.mk D.gamma < C.κ :=
    closureBase_gamma_small C.uncountable C.base C.small_real C.small_gamma
  have hD : VFGammaGeneratedBase D := C.fieldBase.gamma_closure_generated C.base.gamma
  have H : ∀ {n : ℕ} (sn : Fin n → SortTag) (U : Set (Fin n → M)),
      DefinableOverBase C.base sn U → DefinableOverBase D sn U :=
    fun {_} sn U h => (DefinableOverBase.closureBase_iff C.base sn U).mpr h
  have K : ∀ {n : ℕ} (sn : Fin n → SortTag) (U : Set (Fin n → M)),
      DefinableOverBase D sn U → DefinableOverBase C.base sn U :=
    fun {_} sn U h => (DefinableOverBase.closureBase_iff C.base sn U).mp h
  have hdim : ∀ {n r : ℕ} (E : GammaGroundDefSet hc D (rawMixedSpace (M := M) n r)) (k : ℕ),
      Section2.vfDimension E.carrier ≤ (k : WithBot ℕ) ↔ GammaHasVFDimLE D E.carrier k :=
    fun E k => boundedNative_dimension_iff C.uncountable.le C.saturated C.model00 hr hv E k
  exact {
    lift := boundedNativeLift C.uncountable.le C.saturated C.model00 hr (closureBase_field C.base) hγ δ
      ((subset_closureBase C.base).2 hδ) hδ1 hD H K hdim
    lift_class := fun k i U => boundedNativeLift_class C.uncountable.le C.saturated C.model00 hr
      (closureBase_field C.base) hγ δ ((subset_closureBase C.base).2 hδ) hδ1 hD H K hdim i U
    surjective := boundedNativeLift_surjective C.uncountable.le C.saturated C.model00 hr
      (closureBase_field C.base) hγ δ ((subset_closureBase C.base).2 hδ) hδ1 hD H K hdim
    kernel := boundedNativeLift_kernel C.uncountable.le C.saturated C.model00 hr
      (closureBase_field C.base) hγ δ ((subset_closureBase C.base).2 hδ) hδ1 hD H K hdim }

/-- Theorem 3.22, first sentence, with no accepted input: for each `k`, the
canonical isomorphism `∫₊ : K₊VF[k] ≅ K₊RV[≤k]/I_sp` over the complete
Gamma ground. -/
def theorem_3_22_bounded (k : ℕ) :
    GammaGroundVFKPlus hc C.base k ≃+
      (gammaGroundRVBoundedSpecialCongruence (ground := C.base) (k := k) hc).Quotient :=
  gammaGroundBoundedUnmeasuredIntegral (completedGammaGroundBoundedLiftInput (G := G) C hc hv) k

/-- The characterization in Theorem 3.22: `∫₊ [A] = [U]/I_sp` iff `[A] = [𝕃U]`. -/
theorem theorem_3_22_bounded_characterization (k : ℕ)
    (A : GammaGroundVFObject hc C.base k) (i : Fin (k + 1)) (U : GammaGroundRVObject hc C.base i.val) :
    theorem_3_22_bounded (G := G) C hc hv k (gammaGroundVFClass A) =
      (gammaGroundRVBoundedSpecialCongruence (ground := C.base) (k := k) hc).mk' (gammaGroundRVBoundedClass i U) ↔
      gammaGroundVFClass A = gammaGroundVFClass ((gammaGroundObjectLiftVF U).raise (Nat.le_of_lt_succ i.isLt)) :=
  gammaGroundBoundedUnmeasuredIntegral_characterization _ k A i U

/-- Compatibility of the bounded isomorphisms with the inductive systems. -/
theorem theorem_3_22_bounded_transition {k l : ℕ} (hkl : k ≤ l) (x : GammaGroundVFKPlus hc C.base k) :
    theorem_3_22_bounded (G := G) C hc hv l (gammaGroundVFRaiseKPlus hkl x) =
      gammaGroundRVBoundedQuotientTransition hc hkl (theorem_3_22_bounded (G := G) C hc hv k x) :=
  (gammaGroundBoundedUnmeasuredIntegral_transition _ hkl x).symm

end DiamondIntegral.Section3
