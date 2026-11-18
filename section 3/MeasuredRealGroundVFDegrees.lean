import «section 3».MeasuredRealGroundVFCompatibility
import «section 3».PresentationHomExt

/-! Inverse additive maps between the literal ordinary measured VF
categories and their redundant-Gamma presentations, in every degree. -/
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

def vfDegreeFromRealInvariant (k : ℕ) : PositiveAdditiveGrothendieck.Invariant (measuredVFPresentation C hc k)
    (A := GammaGroundMeasuredVFKPlus (hc := hc) (ground := (measuredRealGroundContext C B).base)
      C.uncountable.le C.saturated C.small hv k) where
  toFun U := gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small hv
    (vfFromReal C hc B (MeasuredVFData.ofObject U))
  iso := by
    intro U V h
    have he : Nonempty (U ≅ V) := by cases k <;> exact h
    have hg := vfIsoFromReal C hc B hv (MeasuredVFData.ofObject U) (MeasuredVFData.ofObject V)
      (by simpa only [MeasuredVFData.to_ofObject] using he)
    obtain ⟨f⟩ := hg
    exact gammaGroundMeasuredVFClass_iso C.uncountable.le C.saturated C.small hv f
  empty := by
    have he : MeasuredVFData.ofObject (measuredVFPresentation C hc k).empty = MeasuredVFData.empty C hc k := by cases k <;> rfl
    rw [he]
    exact (gammaGroundMeasuredVFClass_iso C.uncountable.le C.saturated C.small hv (vfFromRealEmptyHom C hc B hv k)).trans
      (gammaGroundMeasuredVFClass_empty C.uncountable.le C.saturated C.small hv)
  scissor := by
    intro A E F H h
    have hd : (measuredVFPresentation C hc k).scissor
        (MeasuredVFData.ofObject A).toObject (MeasuredVFData.ofObject E).toObject
        (MeasuredVFData.ofObject F).toObject (MeasuredVFData.ofObject H).toObject := by
      simpa only [MeasuredVFData.to_ofObject] using h
    obtain ⟨U,X,hX,hA,hE,hF,hH⟩ := dataScissor_exists C hc hd
    rw [hA,hE,hF,hH,vfFromReal_restrict,vfFromReal_restrict]
    have hDiff : GammaGroundDefSet.ofReal (U.domain.sdiff X) =
        (vfFromReal C hc B U).domain.sdiff (GammaGroundDefSet.ofReal X) := rfl
    simp only [hDiff]
    have hz := (gammaGroundMeasuredVFClass_iso C.uncountable.le C.saturated C.small hv (vfFromRealEmptyHom C hc B hv k)).trans
      (gammaGroundMeasuredVFClass_empty C.uncountable.le C.saturated C.small hv)
    rw [hz,add_zero]
    exact gammaGroundMeasuredVFClass_scissor C.uncountable.le C.saturated C.small hv _ _ _

def vfDegreeFromReal (k : ℕ) : MeasuredVFKPlus C hc k →+
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := (measuredRealGroundContext C B).base)
      C.uncountable.le C.saturated C.small hv k :=
  PositiveAdditiveGrothendieck.lift _ (vfDegreeFromRealInvariant C hc B hv k)

theorem vfDegreeFromReal_class {k : ℕ} (U : MeasuredVFData C hc k) :
    vfDegreeFromReal C hc B hv k (positiveClass (measuredVFPresentation C hc k) U.toObject) =
      gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small hv (vfFromReal C hc B U) := by
  rw [vfDegreeFromReal,positiveClass,PositiveAdditiveGrothendieck.lift_of]
  change gammaGroundMeasuredVFClass _ _ _ _ (vfFromReal C hc B (MeasuredVFData.ofObject U.toObject)) = _
  rw [MeasuredVFData.of_toObject]

def vfDegreeToRealInvariant (k : ℕ) : PositiveAdditiveGrothendieck.Invariant
    (gammaGroundMeasuredVFPresentation (hc := hc) (ground := (measuredRealGroundContext C B).base)
      C.uncountable.le C.saturated C.small hv k) (A := MeasuredVFKPlus C hc k) where
  toFun U := positiveClass (measuredVFPresentation C hc k) (vfToReal C hc B U).toObject
  iso := by
    intro U V h
    obtain ⟨e⟩ := vfIsoToReal C hc B hv U V h
    apply positiveClass_iso
    cases k <;> exact ⟨e⟩
  empty := by
    obtain ⟨e⟩ := vfToRealEmptyIso C hc B hv k
    have he : (measuredVFPresentation C hc k).iso
        (vfToReal C hc B (GammaGroundMeasuredVFData.empty hc (measuredRealGroundContext C B).base k)).toObject
        (measuredVFPresentation C hc k).empty := by cases k <;> exact ⟨e⟩
    exact (positiveClass_iso _ he).trans (positiveClass_empty _)
  scissor := by
    rintro A E F H ⟨U,X,hX,hA,hE,hF,hH⟩
    rw [hA,hE,hF,hH,vfToReal_restrict,vfToReal_restrict]
    have hDiff : (U.domain.sdiff X).toRealNames (measuredRealGroundContext_gamma_names C B) =
        (vfToReal C hc B U).domain.sdiff (X.toRealNames (measuredRealGroundContext_gamma_names C B)) := rfl
    simp only [hDiff]
    have h := positiveClass_scissor (measuredVFPresentation C hc k)
      (dataScissor_of_pieces C hc (vfToReal C hc B U) (X.toRealNames (measuredRealGroundContext_gamma_names C B)) hX)
    obtain ⟨e⟩ := vfToRealEmptyIso C hc B hv k
    have he : (measuredVFPresentation C hc k).iso
        (vfToReal C hc B (GammaGroundMeasuredVFData.empty hc (measuredRealGroundContext C B).base k)).toObject
        (MeasuredVFData.empty C hc k).toObject := by cases k <;> exact ⟨e⟩
    rw [positiveClass_iso _ he]
    exact h

def vfDegreeToReal (k : ℕ) :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := (measuredRealGroundContext C B).base)
      C.uncountable.le C.saturated C.small hv k →+ MeasuredVFKPlus C hc k :=
  PositiveAdditiveGrothendieck.lift _ (vfDegreeToRealInvariant C hc B hv k)

theorem vfDegreeToReal_class {k : ℕ} (U : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k) :
    vfDegreeToReal C hc B hv k (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small hv U) =
      positiveClass (measuredVFPresentation C hc k) (vfToReal C hc B U).toObject :=
  PositiveAdditiveGrothendieck.lift_of _ (vfDegreeToRealInvariant C hc B hv k) U

theorem vfDegreeToReal_fromReal (k : ℕ) (a : MeasuredVFKPlus C hc k) :
    vfDegreeToReal C hc B hv k (vfDegreeFromReal C hc B hv k a) = a := by
  have he : (vfDegreeToReal C hc B hv k).comp (vfDegreeFromReal C hc B hv k) = AddMonoidHom.id _ := by
    apply positiveAdditivePresentationHom_ext (measuredVFPresentation C hc k)
    intro U
    change vfDegreeToReal C hc B hv k (vfDegreeFromReal C hc B hv k (positiveClass _ U)) = _
    have hU := vfDegreeFromReal_class C hc B hv (MeasuredVFData.ofObject U)
    simp only [MeasuredVFData.to_ofObject] at hU
    rw [hU,vfDegreeToReal_class,vfToReal_fromReal,MeasuredVFData.to_ofObject]
    rfl
  exact DFunLike.congr_fun he a

theorem vfDegreeFromReal_toReal (k : ℕ)
    (a : GammaGroundMeasuredVFKPlus (hc := hc) (ground := (measuredRealGroundContext C B).base)
      C.uncountable.le C.saturated C.small hv k) :
    vfDegreeFromReal C hc B hv k (vfDegreeToReal C hc B hv k a) = a := by
  have he : (vfDegreeFromReal C hc B hv k).comp (vfDegreeToReal C hc B hv k) = AddMonoidHom.id _ := by
    apply positiveAdditivePresentationHom_ext (gammaGroundMeasuredVFPresentation (hc := hc) (ground := (measuredRealGroundContext C B).base)
      C.uncountable.le C.saturated C.small hv k)
    intro U
    change vfDegreeFromReal C hc B hv k (vfDegreeToReal C hc B hv k (gammaGroundMeasuredVFClass _ _ _ _ U)) = _
    rw [vfDegreeToReal_class,vfDegreeFromReal_class,vfFromReal_toReal]
    rfl
  exact DFunLike.congr_fun he a

end DiamondIntegral.Section3.MeasuredRealGround
