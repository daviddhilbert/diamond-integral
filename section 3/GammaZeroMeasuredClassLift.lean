import «section 3».GammaZeroMeasuredClassDescent

/-! The degree-zero positive additive lift, inverse to literal descent.
The proof uses the actual scissor presentations and exact weighted arrows. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem gammaMeasuredObjectLift_restrict_subset {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    (gammaGroundMeasuredObjectLift (U.restrict X hX)).domain.carrier ⊆
      (gammaGroundMeasuredObjectLift U).domain.carrier := by
  rintro q ⟨u,hu,hv⟩
  exact ⟨⟨u.val,hX u.property⟩,hu,hv⟩

theorem gammaMeasuredObjectLift_restrict_eq {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    (gammaGroundMeasuredObjectLift U).restrict
      (gammaGroundMeasuredObjectLift (U.restrict X hX)).domain
      (gammaMeasuredObjectLift_restrict_subset U X hX) =
        gammaGroundMeasuredObjectLift (U.restrict X hX) := rfl

theorem gammaMeasuredObjectLift_complement {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    ((gammaGroundMeasuredObjectLift U).domain.sdiff
      (gammaGroundMeasuredObjectLift (U.restrict X hX)).domain).carrier =
        (gammaGroundMeasuredObjectLift
          (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1))).domain.carrier := by
  ext q
  constructor
  · rintro ⟨⟨u,hu,hv⟩,hn⟩
    have hux : u.val ∉ X.carrier := by
      intro hx
      exact hn ⟨⟨u.val,hx⟩,hu,hv⟩
    exact ⟨⟨u.val,u.property,hux⟩,hu,hv⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨⟨⟨u.val,u.property.1⟩,hu,hv⟩,?_⟩
    rintro ⟨v,hv',_⟩
    apply u.property.2
    have he : u.val = v.val := hu.trans hv'.symm
    exact he.symm ▸ v.property

def gammaZeroMeasuredRVLiftInvariant :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundMeasuredRVPresentation hc B 0)
      (A := GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ hs hS hv 0) where
  toFun U := gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U)
  iso := by
    rintro U V ⟨e⟩
    exact gammaGroundMeasuredVFClass_iso hκ hs hS hv (n := 0) (gammaGroundZeroMeasuredRVLiftHom e.hom)
  empty := by
    let U := gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.empty hc B 0)
    have he : U.domain.carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro q ⟨u,_,_⟩
      exact u.property
    let f : GammaGroundZeroMeasuredVFHom U (GammaGroundMeasuredVFData.empty hc B 0) := {
      bijection := GammaGroundBijection.ofEmpty he rfl
      preserves := fun a => False.elim ((Set.eq_empty_iff_forall_notMem.mp he) a.val a.property) }
    exact (gammaGroundMeasuredVFClass_iso hκ hs hS hv (n := 0) f).trans
      (gammaGroundMeasuredVFClass_empty hκ hs hS hv)
  scissor := by
    rintro A D E F ⟨U,X,hX,hA,hD,hE,hF⟩
    subst A
    subst D
    subst E
    subst F
    let V := gammaGroundMeasuredObjectLift U
    let Y := (gammaGroundMeasuredObjectLift (U.restrict X hX)).domain
    have hY := gammaMeasuredObjectLift_restrict_subset U X hX
    have hEq := gammaMeasuredObjectLift_restrict_eq U X hX
    let f : GammaGroundZeroMeasuredVFHom
        (V.restrict (V.domain.sdiff Y) (fun _ h => h.1))
        (gammaGroundMeasuredObjectLift
          (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1))) := {
      bijection := GammaGroundBijection.ofCarrierEq (gammaMeasuredObjectLift_complement U X hX)
      preserves := fun _ => rfl }
    have h := gammaGroundMeasuredVFClass_scissor hκ hs hS hv V Y hY
    rw [hEq,gammaGroundMeasuredVFClass_iso hκ hs hS hv (n := 0) f] at h
    have hEmpty := (gammaGroundMeasuredVFClass_iso hκ hs hS hv (n := 0)
      (show GammaGroundZeroMeasuredVFHom
        (gammaGroundMeasuredObjectLift (GammaGroundMeasuredRVObject.empty hc B 0))
        (GammaGroundMeasuredVFData.empty hc B 0) from {
          bijection := GammaGroundBijection.ofEmpty (by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro q ⟨u,_,_⟩
            exact u.property) rfl
          preserves := by rintro a; obtain ⟨u,_,_⟩ := a.property; exact False.elim u.property })).trans
        (gammaGroundMeasuredVFClass_empty hκ hs hS hv)
    simpa only [hEmpty,add_zero] using h

def gammaZeroMeasuredRVClassLift :
    GammaGroundMeasuredRVKPlus hc B 0 →+
      GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ hs hS hv 0 :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredRVPresentation hc B 0)
    (gammaZeroMeasuredRVLiftInvariant hκ hs hS hv)

@[simp] theorem gammaZeroMeasuredRVClassLift_class (U : GammaGroundMeasuredRVObject hc B 0) :
    gammaZeroMeasuredRVClassLift hκ hs hS hv (gammaGroundMeasuredRVClass U) =
      gammaGroundMeasuredVFClass hκ hs hS hv (gammaGroundMeasuredObjectLift U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def gammaZeroMeasuredClassEquiv :
    GammaGroundMeasuredRVKPlus hc B 0 ≃+
      GammaGroundMeasuredVFKPlus (hc := hc) (ground := B) hκ hs hS hv 0 := by
  let F := gammaZeroMeasuredRVClassLift (hc := hc) (B := B) hκ hs hS hv
  let D := gammaZeroMeasuredVFClassDescent (hc := hc) (B := B) hκ hs hS hv
  have hDF : D.comp F = AddMonoidHom.id _ := by
    apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundMeasuredRVPresentation hc B 0)
    intro U
    change D (F (gammaGroundMeasuredRVClass U)) = gammaGroundMeasuredRVClass U
    rw [gammaZeroMeasuredRVClassLift_class,gammaZeroMeasuredVFClassDescent_lift]
  have hFD : F.comp D = AddMonoidHom.id _ := by
    apply PositiveAdditiveGrothendieck.hom_ext
      (gammaGroundMeasuredVFPresentation (hc := hc) (ground := B) hκ hs hS hv 0)
    intro U
    change F (D (gammaGroundMeasuredVFClass hκ hs hS hv U)) =
      gammaGroundMeasuredVFClass hκ hs hS hv U
    rw [gammaZeroMeasuredVFClassDescent_class,gammaZeroMeasuredRVClassLift_class]
    exact gammaGroundMeasuredVFClass_iso hκ hs hS hv (n := 0) (gammaZeroVFRepresentationIso U).hom
  exact {
    toFun := F
    invFun := D
    left_inv := fun a => DFunLike.congr_fun hDF a
    right_inv := fun a => DFunLike.congr_fun hFD a
    map_add' := F.map_add }

end DiamondIntegral.Section3
