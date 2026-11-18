import «section 3».MeasuredRealGroundObjects
import «section 3».GammaGroundMeasuredRVSemiring
import «section 3».GammaGroundMeasuredRVScissors
import «section 3».MeasuredRVSemiring

/-! The literal real/Gamma object adapters preserve products and
inherited cuts by actual measured arrows. Empty objects are compared
without imposing a density value on their empty domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base) {k l : ℕ}

def rvFromRealProductHom (U : MeasuredRVObject (M := M) (C.base : Set M) k)
    (V : MeasuredRVObject (M := M) (C.base : Set M) l) :
    GammaGroundMeasuredRVHom (rvFromReal C hc B (U.product hc V))
      ((rvFromReal C hc B U).product (rvFromReal C hc B V)) :=
  ⟨GammaGroundBijection.id _,fun _ => rfl⟩

def rvToRealProductHom (U : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k)
    (V : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base l) :
    MeasuredRVHom (rvToReal C hc B (U.product V)) ((rvToReal C hc B U).product hc (rvToReal C hc B V)) :=
  ⟨DefinableBijection.id _,fun _ => rfl⟩

def rvFromRealRestrictionHom (U : MeasuredRVObject (M := M) (C.base : Set M) k)
    (X : DefSet (rawRVSpace (M := M) U.underlying.arity) (C.base : Set M))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    GammaGroundMeasuredRVHom (rvFromReal C hc B (U.restrict hc X hX))
      ((rvFromReal C hc B U).restrict (GammaGroundDefSet.ofReal X) hX) :=
  ⟨GammaGroundBijection.id _,fun _ => rfl⟩

def rvToRealRestrictionHom (U : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k)
    (X : GammaGroundDefSet hc (measuredRealGroundContext C B).base (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    MeasuredRVHom (rvToReal C hc B (U.restrict X hX))
      ((rvToReal C hc B U).restrict hc (X.toRealNames (measuredRealGroundContext_gamma_names C B)) hX) :=
  ⟨DefinableBijection.id _,fun _ => rfl⟩

theorem rvFromReal_empty_class (k : ℕ) :
    gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B (MeasuredRVObject.empty (C.base : Set M) k)) = 0 := by
  let f : GammaGroundMeasuredRVHom (rvFromReal C hc B (MeasuredRVObject.empty (C.base : Set M) k))
      (GammaGroundMeasuredRVObject.empty hc (measuredRealGroundContext C B).base k) :=
    ⟨GammaGroundBijection.id _,fun p => False.elim p.property⟩
  exact (gammaGroundMeasuredRVSemiringClass_iso (asIso f)).trans gammaGroundMeasuredRVSemiringClass_empty

theorem rvToReal_empty_class (k : ℕ) :
    measuredRVSemiringClass hc (rvToReal C hc B (GammaGroundMeasuredRVObject.empty hc (measuredRealGroundContext C B).base k)) = 0 := by
  let f : MeasuredRVHom (rvToReal C hc B (GammaGroundMeasuredRVObject.empty hc (measuredRealGroundContext C B).base k))
      (MeasuredRVObject.empty (C.base : Set M) k) :=
    ⟨DefinableBijection.id _,fun p => False.elim p.property⟩
  exact (measuredRVSemiringClass_iso hc (asIso f)).trans (measuredRVSemiringClass_empty hc)

theorem rvFromReal_scissor_class {A E F H : MeasuredRVObject (M := M) (C.base : Set M) k}
    (h : MeasuredRVScissor hc A E F H) :
    gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B A) + gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B E) =
      gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B F) + gammaGroundMeasuredRVSemiringClass (rvFromReal C hc B H) := by
  obtain ⟨U,X,hX,hA,hE,hF,hH⟩ := h
  subst A
  subst E
  subst F
  subst H
  rw [gammaGroundMeasuredRVSemiringClass_iso (asIso (rvFromRealRestrictionHom C hc B U X hX)),
    gammaGroundMeasuredRVSemiringClass_iso (asIso (rvFromRealRestrictionHom C hc B U (U.underlying.difference X) (fun _ h => h.1))),
    rvFromReal_empty_class,add_zero]
  have hC := gammaGroundMeasuredRVSemiringClass_scissor (hc := hc) (ground := (measuredRealGroundContext C B).base)
    ⟨rvFromReal C hc B U,GammaGroundDefSet.ofReal X,hX,rfl,rfl,rfl,rfl⟩
  have hDiff : GammaGroundDefSet.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base)
      (U.underlying.difference X) = (rvFromReal C hc B U).underlying.domain.sdiff (GammaGroundDefSet.ofReal X) := rfl
  simpa only [hDiff,gammaGroundMeasuredRVSemiringClass_empty,add_zero] using hC

theorem rvToReal_scissor_class
    {A E F H : GammaGroundMeasuredRVObject hc (measuredRealGroundContext C B).base k}
    (h : gammaGroundMeasuredRVScissor A E F H) :
    measuredRVSemiringClass hc (rvToReal C hc B A) + measuredRVSemiringClass hc (rvToReal C hc B E) =
      measuredRVSemiringClass hc (rvToReal C hc B F) + measuredRVSemiringClass hc (rvToReal C hc B H) := by
  obtain ⟨U,X,hX,hA,hE,hF,hH⟩ := h
  subst A
  subst E
  subst F
  subst H
  rw [measuredRVSemiringClass_iso hc (asIso (rvToRealRestrictionHom C hc B U X hX)),
    measuredRVSemiringClass_iso hc (asIso (rvToRealRestrictionHom C hc B U (U.underlying.domain.sdiff X) (fun _ h => h.1))),
    rvToReal_empty_class,add_zero]
  have hC := measuredRVSemiringClass_scissor hc
    ⟨rvToReal C hc B U,X.toRealNames (measuredRealGroundContext_gamma_names C B),hX,rfl,rfl,rfl,rfl⟩
  have hDiff : (U.underlying.domain.sdiff X).toRealNames (measuredRealGroundContext_gamma_names C B) =
      (rvToReal C hc B U).underlying.difference (X.toRealNames (measuredRealGroundContext_gamma_names C B)) := rfl
  simpa only [hDiff,measuredRVSemiringClass_empty,add_zero] using hC

end DiamondIntegral.Section3.MeasuredRealGround
