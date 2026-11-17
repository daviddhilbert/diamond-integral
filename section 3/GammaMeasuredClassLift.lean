import «section 3».GammaMeasuredArrowLift

/-! The Gamma-valued forward lift on the literal additive scissor
monoids, before any kernel relation or groupification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hS : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaDefSet_eq_of_carrierEq {Q : Space LRV M}
    {A D : GammaGroundDefSet hc B Q} (h : A.carrier = D.carrier) : A = D := by
  cases A
  cases D
  cases h
  rfl

def gammaMeasuredLiftEmptyHom : GammaGroundMeasuredVFHom hκ hs hS hv
    (gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.empty hc B k))
    (GammaGroundMeasuredVFData.empty hc B k) := by
  apply gammaMeasuredHomOfCarrierEq hκ hs hS hv
    (U := gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.empty hc B k))
    (V := GammaGroundMeasuredVFData.empty hc B k) rfl
  · apply heq_of_eq
    apply gammaDefSet_eq_of_carrierEq
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨u,_,_⟩
    exact u.property
  · rintro p _ _
    obtain ⟨u,_,_⟩ := p.property
    exact False.elim u.property

theorem gammaMeasuredLift_class_empty :
    gammaGroundMeasuredVFClass hκ hs hS hv
      (gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.empty hc B k)) = 0 :=
  (gammaGroundMeasuredVFClass_iso hκ hs hS hv (gammaMeasuredLiftEmptyHom hκ hs hS hv)).trans
    (gammaGroundMeasuredVFClass_empty hκ hs hS hv)

theorem gammaMeasuredLift_class_scissor
    (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift (U.restrict X hX)) +
      gammaGroundMeasuredVFClass hκ hs hS hv
        (gammaGroundMeasuredObjectLift (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1))) =
      gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U) := by
  let V := gammaGroundMeasuredObjectLift U
  let Y := (gammaGroundMeasuredObjectLift (U.restrict X hX)).domain
  have hY := gammaMeasuredObjectLift_restrict_subset U X hX
  have hEq := gammaMeasuredObjectLift_restrict_eq U X hX
  let F := gammaMeasuredHomOfCarrierEq hκ hs hS hv
    (U := V.restrict (V.domain.sdiff Y) (fun _ h => h.1))
    (V := gammaGroundMeasuredObjectLift (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1)))
    rfl (heq_of_eq (gammaDefSet_eq_of_carrierEq (gammaMeasuredObjectLift_complement U X hX)))
    (fun p q h => by
      have he : p.val = q.val := eq_of_heq h
      apply congrArg (fun z : U.underlying.domain => (gammaGroundFormValue U.form z).val)
      exact Subtype.ext (congrArg Prod.snd he))
  have h := gammaGroundMeasuredVFClass_scissor hκ hs hS hv V Y hY
  rw [hEq,gammaGroundMeasuredVFClass_iso hκ hs hS hv F] at h
  exact h

def gammaMeasuredRVLiftInvariant :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundMeasuredRVPresentation hc B k)
      (A := GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ hs hS hv k) where
  toFun U := gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U)
  iso := by
    rintro U V ⟨e⟩
    exact gammaGroundMeasuredVFClass_iso hκ hs hS hv (gammaMeasuredArrowLift hκ hs hS hv h00 hB e.hom)
  empty := gammaMeasuredLift_class_empty hκ hs hS hv
  scissor := by
    rintro A D E F ⟨U,X,hX,hA,hD,hE,hF⟩
    subst A
    subst D
    subst E
    subst F
    simpa only [gammaMeasuredLift_class_empty hκ hs hS hv,add_zero] using
      gammaMeasuredLift_class_scissor hκ hs hS hv U X hX

def gammaMeasuredRVClassLift : GammaGroundMeasuredRVKPlus hc B k →+
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ hs hS hv k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredRVPresentation hc B k)
    (gammaMeasuredRVLiftInvariant hκ hs h00 hS hB hv)

@[simp] theorem gammaMeasuredRVClassLift_class (U : GammaGroundMeasuredRVObject hc B k) :
    gammaMeasuredRVClassLift hκ hs h00 hS hB hv (gammaGroundMeasuredRVClass U) =
      gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

end DiamondIntegral.Section3
