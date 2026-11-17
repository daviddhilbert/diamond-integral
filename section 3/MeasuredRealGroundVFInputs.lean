import «section 3».MeasuredRealGroundVFDegrees
import «section 3».GammaGroundMeasuredVFSemiring

/-! The inverse VF comparisons respect actual cartesian products and
therefore descend to inverse maps on the full positive semirings. -/
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

theorem vfFromReal_empty_semiring (k : ℕ) :
    gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B (MeasuredVFData.empty C hc k)) = 0 :=
  (gammaGroundMeasuredVFSemiringClass_iso (measuredRealGroundContext C B) hc hv (vfFromRealEmptyHom C hc B hv k)).trans
    (gammaGroundMeasuredVFSemiringClass_empty _ _ _)

include hv in
theorem vfToReal_empty_semiring (k : ℕ) :
    measuredVFDataSemiringClass C hc (vfToReal C hc B (GammaGroundMeasuredVFData.empty hc (measuredRealGroundContext C B).base k)) = 0 := by
  obtain ⟨e⟩ := vfToRealEmptyIso C hc B hv k
  exact (measuredVFDataSemiringClass_iso C hc e).trans (measuredVFDataSemiringClass_empty C hc)

theorem vfFromReal_scissor_semiring {k : ℕ} {A E F H : MeasuredVFData C hc k}
    (h : (measuredVFPresentation C hc k).scissor A.toObject E.toObject F.toObject H.toObject) :
    gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B A) +
      gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B E) =
    gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B F) +
      gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B H) := by
  have h0 := (vfDegreeFromRealInvariant C hc B hv k).scissor h
  change gammaGroundMeasuredVFClass _ _ _ _ (vfFromReal C hc B (MeasuredVFData.ofObject A.toObject)) +
    gammaGroundMeasuredVFClass _ _ _ _ (vfFromReal C hc B (MeasuredVFData.ofObject E.toObject)) =
    gammaGroundMeasuredVFClass _ _ _ _ (vfFromReal C hc B (MeasuredVFData.ofObject F.toObject)) +
    gammaGroundMeasuredVFClass _ _ _ _ (vfFromReal C hc B (MeasuredVFData.ofObject H.toObject)) at h0
  simp only [MeasuredVFData.of_toObject] at h0
  simpa only [map_add,gammaGroundMeasuredVFKPlusToSemiring_class] using
    congrArg (gammaGroundMeasuredVFKPlusToSemiring (measuredRealGroundContext C B) hc hv) h0

include hv in
theorem vfToReal_scissor_semiring {k : ℕ}
    {A E F H : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k}
    (h : gammaGroundMeasuredVFScissor A E F H) :
    measuredVFDataSemiringClass C hc (vfToReal C hc B A) + measuredVFDataSemiringClass C hc (vfToReal C hc B E) =
      measuredVFDataSemiringClass C hc (vfToReal C hc B F) + measuredVFDataSemiringClass C hc (vfToReal C hc B H) := by
  have h0 := (vfDegreeToRealInvariant C hc B hv k).scissor h
  change positiveClass _ (vfToReal C hc B A).toObject + positiveClass _ (vfToReal C hc B E).toObject =
    positiveClass _ (vfToReal C hc B F).toObject + positiveClass _ (vfToReal C hc B H).toObject at h0
  have he := congrArg (measuredVFKPlusToSemiring C hc) h0
  simpa only [map_add,measuredVFKPlusToSemiring_class,measuredVFObjectSemiringClass,MeasuredVFData.of_toObject] using he

def vfSemiringFromRealInvariant : PositiveGrothendieck.Invariant (measuredVFSemiringPresentation C hc)
    (R := GammaGroundMeasuredVFPositiveSemiring (measuredRealGroundContext C B) hc hv) where
  toFun A := gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B A.2)
  iso := by
    rintro A E ⟨k,U,V,h,rfl,rfl⟩
    obtain ⟨f⟩ := vfIsoFromReal C hc B hv U V h
    exact gammaGroundMeasuredVFSemiringClass_iso _ _ _ f
  empty := vfFromReal_empty_semiring C hc B hv 0
  unit := by
    have he : vfFromReal C hc B (MeasuredVFData.unit C hc) = GammaGroundMeasuredVFData.unit hc (measuredRealGroundContext C B).base := rfl
    change gammaGroundMeasuredVFSemiringClass _ _ _ (vfFromReal C hc B (MeasuredVFData.unit C hc)) = 1
    rw [he]
    exact gammaGroundMeasuredVFSemiringClass_unit _ _ _
  product A E := by
    change gammaGroundMeasuredVFSemiringClass _ _ _ (vfFromReal C hc B (A.2.product E.2)) = _
    rw [vfFromReal_product]
    exact gammaGroundMeasuredVFSemiringClass_product _ _ _ _ _
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · exact vfFromReal_scissor_semiring C hc B hv h
    · simp only [vfFromReal_empty_semiring,add_zero]

def vfSemiringFromReal : MeasuredVFPositiveSemiring C hc →+*
    GammaGroundMeasuredVFPositiveSemiring (measuredRealGroundContext C B) hc hv :=
  PositiveGrothendieck.lift _ (vfSemiringFromRealInvariant C hc B hv)

theorem vfSemiringFromReal_class {k : ℕ} (U : MeasuredVFData C hc k) :
    vfSemiringFromReal C hc B hv (measuredVFDataSemiringClass C hc U) =
      gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv (vfFromReal C hc B U) :=
  PositiveGrothendieck.lift_of (measuredVFSemiringPresentation C hc) (vfSemiringFromRealInvariant C hc B hv) ⟨k,U⟩

def vfSemiringToRealInvariant : PositiveGrothendieck.Invariant
    (gammaGroundMeasuredVFSemiringPresentation (measuredRealGroundContext C B) hc hv)
    (R := MeasuredVFPositiveSemiring C hc) where
  toFun A := measuredVFDataSemiringClass C hc (vfToReal C hc B A.2)
  iso := by
    rintro A E ⟨k,U,V,h,rfl,rfl⟩
    obtain ⟨e⟩ := vfIsoToReal C hc B hv U V h
    exact measuredVFDataSemiringClass_iso C hc e
  empty := vfToReal_empty_semiring C hc B hv 0
  unit := by
    have he : vfToReal C hc B (GammaGroundMeasuredVFData.unit hc (measuredRealGroundContext C B).base) = MeasuredVFData.unit C hc := rfl
    change measuredVFDataSemiringClass C hc (vfToReal C hc B (GammaGroundMeasuredVFData.unit hc (measuredRealGroundContext C B).base)) = 1
    rw [he]
    exact PositiveGrothendieck.of_unit _
  product A E := by
    change measuredVFDataSemiringClass C hc (vfToReal C hc B (A.2.product E.2)) = _
    rw [vfToReal_product]
    exact measuredVFDataSemiringClass_product _ _ _ _
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · exact vfToReal_scissor_semiring C hc B hv h
    · simp only [vfToReal_empty_semiring C hc B hv,add_zero]

def vfSemiringToReal : GammaGroundMeasuredVFPositiveSemiring (measuredRealGroundContext C B) hc hv →+*
    MeasuredVFPositiveSemiring C hc :=
  PositiveGrothendieck.lift _ (vfSemiringToRealInvariant C hc B hv)

theorem vfSemiringToReal_class {k : ℕ} (U : GammaGroundMeasuredVFData hc (measuredRealGroundContext C B).base k) :
    vfSemiringToReal C hc B hv (gammaGroundMeasuredVFSemiringClass (measuredRealGroundContext C B) hc hv U) =
      measuredVFDataSemiringClass C hc (vfToReal C hc B U) :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredVFSemiringPresentation (measuredRealGroundContext C B) hc hv)
    (vfSemiringToRealInvariant C hc B hv) ⟨k,U⟩

theorem vfSemiringToReal_fromReal (a : MeasuredVFPositiveSemiring C hc) :
    vfSemiringToReal C hc B hv (vfSemiringFromReal C hc B hv a) = a := by
  have he : (vfSemiringToReal C hc B hv).comp (vfSemiringFromReal C hc B hv) = RingHom.id _ := by
    apply positivePresentationHom_ext (measuredVFSemiringPresentation C hc)
    rintro ⟨k,U⟩
    change vfSemiringToReal C hc B hv (vfSemiringFromReal C hc B hv (measuredVFDataSemiringClass C hc U)) = _
    rw [vfSemiringFromReal_class,vfSemiringToReal_class,vfToReal_fromReal]
    rfl
  exact RingHom.congr_fun he a

theorem vfSemiringFromReal_toReal (a : GammaGroundMeasuredVFPositiveSemiring (measuredRealGroundContext C B) hc hv) :
    vfSemiringFromReal C hc B hv (vfSemiringToReal C hc B hv a) = a := by
  have he : (vfSemiringFromReal C hc B hv).comp (vfSemiringToReal C hc B hv) = RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundMeasuredVFSemiringPresentation (measuredRealGroundContext C B) hc hv)
    rintro ⟨k,U⟩
    change vfSemiringFromReal C hc B hv (vfSemiringToReal C hc B hv (gammaGroundMeasuredVFSemiringClass _ _ _ U)) = _
    rw [vfSemiringToReal_class,vfSemiringFromReal_class,vfFromReal_toReal]
    rfl
  exact RingHom.congr_fun he a

end DiamondIntegral.Section3.MeasuredRealGround
