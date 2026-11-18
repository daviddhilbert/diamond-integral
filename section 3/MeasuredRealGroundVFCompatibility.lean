import «section 3».MeasuredRealGroundVFArrows
import «section 3».MeasuredVFSemiring
import «section 3».GammaMeasuredArrowLift
import «section 3».GammaMeasuredClassLift
import «section 3».GammaGroundMeasuredVFProducts

/-! Uniform VF data scissors, restrictions and products agree across
the ordinary and redundant-Gamma presentations. Empty forms are compared
by actual arrows, uniformly in zero and positive degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem dataScissor_exists {k : ℕ} {A E F H : MeasuredVFData C hc k}
    (h : (measuredVFPresentation C hc k).scissor A.toObject E.toObject F.toObject H.toObject) :
    ∃ U : MeasuredVFData C hc k,
      ∃ X : DefSet (rawMixedSpace (M := M) k U.arity) (C.base : Set M),
      ∃ hX : X.carrier ⊆ U.domain.carrier,
        A = U.restrict X hX ∧ E = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
        F = U ∧ H = MeasuredVFData.empty C hc k := by
  cases A
  cases E
  cases F
  cases H
  cases k <;> obtain ⟨U,X,hX,hA,hE,hF,hH⟩ := h
  all_goals
    refine ⟨MeasuredVFData.ofObject U,X,hX,?_,?_,?_,?_⟩
    · simpa only [MeasuredVFData.of_toObject,MeasuredVFData.ofObject,MeasuredVFData.toObject,MeasuredVFData.restrict,
        ZeroMeasuredVF.restrict,PositiveMeasuredVF.restrict,MeasuredVFData.empty,ZeroMeasuredVF.empty,PositiveMeasuredVF.empty] using congrArg MeasuredVFData.ofObject hA
    · simpa only [MeasuredVFData.of_toObject,MeasuredVFData.ofObject,MeasuredVFData.toObject,MeasuredVFData.restrict,
        ZeroMeasuredVF.restrict,PositiveMeasuredVF.restrict,MeasuredVFData.empty,ZeroMeasuredVF.empty,PositiveMeasuredVF.empty] using congrArg MeasuredVFData.ofObject hE
    · simpa only [MeasuredVFData.of_toObject,MeasuredVFData.ofObject,MeasuredVFData.toObject,MeasuredVFData.restrict,
        ZeroMeasuredVF.restrict,PositiveMeasuredVF.restrict,MeasuredVFData.empty,ZeroMeasuredVF.empty,PositiveMeasuredVF.empty] using congrArg MeasuredVFData.ofObject hF
    · simpa only [MeasuredVFData.of_toObject,MeasuredVFData.ofObject,MeasuredVFData.toObject,MeasuredVFData.restrict,
        ZeroMeasuredVF.restrict,PositiveMeasuredVF.restrict,MeasuredVFData.empty,ZeroMeasuredVF.empty,PositiveMeasuredVF.empty] using congrArg MeasuredVFData.ofObject hH

theorem dataScissor_of_pieces {k : ℕ} (U : MeasuredVFData C hc k)
    (X : DefSet (rawMixedSpace (M := M) k U.arity) (C.base : Set M)) (hX : X.carrier ⊆ U.domain.carrier) :
    (measuredVFPresentation C hc k).scissor (U.restrict X hX).toObject
      (U.restrict (U.domain.sdiff X) (fun _ h => h.1)).toObject U.toObject (MeasuredVFData.empty C hc k).toObject := by
  cases k <;> exact ⟨U.toObject,X,hX,rfl,rfl,rfl,rfl⟩

theorem vfFromReal_product {k l : ℕ} (U : MeasuredVFData C hc k) (V : MeasuredVFData C hc l) :
    vfFromReal C hc B (U.product V) = (vfFromReal C hc B U).product (vfFromReal C hc B V) := rfl

theorem vfToReal_product {k l : ℕ}
    (U : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k)
    (V : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base l) :
    vfToReal C hc B (U.product V) = (vfToReal C hc B U).product (vfToReal C hc B V) := rfl

theorem vfFromReal_restrict {k : ℕ} (U : MeasuredVFData C hc k)
    (X : DefSet (rawMixedSpace (M := M) k U.arity) (C.base : Set M)) (hX : X.carrier ⊆ U.domain.carrier) :
    vfFromReal C hc B (U.restrict X hX) = (vfFromReal C hc B U).restrict (GammaGroundDefSet.ofReal X) hX := rfl

theorem vfToReal_restrict {k : ℕ} (U : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k)
    (X : GammaGroundDefSet hc (measuredRealGroundContext C B).base (rawMixedSpace (M := M) k U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    vfToReal C hc B (U.restrict X hX) =
      (vfToReal C hc B U).restrict (X.toRealNames (measuredRealGroundContext_gamma_names C B)) hX := rfl

def vfFromRealEmptyHom (k : ℕ) : GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small hv
    (vfFromReal C hc B (MeasuredVFData.empty C hc k))
    (GammaGroundMeasuredVFData.empty hc (measuredRealGroundContext C B).base k) :=
  gammaMeasuredHomOfCarrierEq C.uncountable.le C.saturated C.small hv rfl
    (heq_of_eq (gammaDefSet_eq_of_carrierEq rfl)) (fun p _ _ => False.elim p.property)

include hv in
theorem vfToRealEmptyIso (k : ℕ) : Nonempty ((vfToReal C hc B
    (GammaGroundMeasuredVFData.empty hc (measuredRealGroundContext C B).base k)).toObject ≅
      (MeasuredVFData.empty C hc k).toObject) := by
  have h := vfIsoToReal C hc B hv _ _
    ⟨(gammaGroundMeasuredVFGroupoid C.uncountable.le C.saturated C.small hv k).inv (vfFromRealEmptyHom C hc B hv k)⟩
  simpa only [vfToReal_fromReal] using h

end DiamondIntegral.Section3.MeasuredRealGround
