import «section 3».BoundedOrdinaryInputs
import «section 3».CitedUnmeasuredIntegral
import «section 5».Completed18GroundLiftInput

/-! Theorem 3.22, global unmeasured part, over an ordinary VF-generated base.
The ordinary and Γ-ground positive VF semirings are identified
(`vfSemiringEquiv`), and the global Γ-ground record proved from [18]
(`Section5.completed18GroundLiftInput`) transfers, through the identified
RV semirings and special congruences, to the ordinary record
`YinUnmeasuredLiftInput` (`completedOrdinaryLiftInput`). This mirrors the
bounded transfer `completedOrdinaryBoundedLiftInput`; no new input. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3.MeasuredRealGround
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-! ### Global RV semirings: the remaining inverse identity -/

theorem rvSemiringFrom_to (a : GammaGroundRVPositiveSemiring hc (measuredRealGroundContext C B).base) :
    rvSemiringFrom C hc B (rvSemiringTo C hc B a) = a := by
  have he : (rvSemiringFrom C hc B).comp (rvSemiringTo C hc B) = RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundRVSemiringPresentation hc (measuredRealGroundContext C B).base)
    rintro ⟨k,U⟩
    change rvSemiringFrom C hc B (rvSemiringTo C hc B (gammaGroundRVSemiringClass U)) = gammaGroundRVSemiringClass U
    rw [rvSemiringTo_class,rvSemiringFrom_class]
    exact gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (rvToRealUnderlying C hc B U) ⟶ U from
      GammaGroundBijection.id _))
  exact RingHom.congr_fun he a

/-! ### Global VF semirings -/

/-- An ordinary VF object as a Γ-ground finite VF object. -/
def vfFiniteFromReal {k : ℕ} (U : VFObject (M := M) (C.base : Set M) k) :
    GammaGroundFiniteVFObject hc (measuredRealGroundContext C B).base :=
  GammaGroundFiniteVFObject.ofBound (vfObjFromReal (G := G) C hc B U)

/-- A Γ-ground finite VF object as an ordinary VF object (degree its VF arity). -/
def vfFiniteToReal (U : GammaGroundFiniteVFObject hc (measuredRealGroundContext C B).base) :
    VFObject (M := M) (C.base : Set M) U.vfArity :=
  vfObjToReal (G := G) C hc B U.toBound

def vfSemiringFromInvariant : PositiveGrothendieck.Invariant (vfSemiringPresentation C hc hv)
    (R := GammaGroundVFPositiveSemiring hc (measuredRealGroundContext C B).base) where
  toFun A := gammaGroundVFSemiringClass (vfFiniteFromReal (G := G) C hc B A.2)
  iso := by
    rintro A E ⟨e⟩
    exact gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B A.2 ⟶ vfFiniteFromReal (G := G) C hc B E.2 from
      ⟨GammaGroundMap.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) e.map,e.bijective⟩))
  empty := (gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (VFObject.empty (C.base : Set M) 0) ⟶
    GammaGroundFiniteVFObject.empty hc (measuredRealGroundContext C B).base from GammaGroundBijection.ofCarrierEq rfl))).trans
      gammaGroundVFSemiringClass_empty
  unit := (gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (VFObject.unit (C.base : Set M)) ⟶
    GammaGroundFiniteVFObject.unit hc (measuredRealGroundContext C B).base from GammaGroundBijection.ofCarrierEq rfl))).trans
      gammaGroundVFSemiringClass_unit
  product A E := (gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (A.2.product hc C.saturated C.small hv E.2) ⟶
    (vfFiniteFromReal (G := G) C hc B A.2).product (vfFiniteFromReal (G := G) C hc B E.2) from GammaGroundBijection.ofCarrierEq (by
      ext x
      exact (mem_mixedProductDomain A.2.domain E.2.domain x).trans
        (mem_gammaGroundMixedProductDomain (vfFiniteFromReal (G := G) C hc B A.2).domain
          (vfFiniteFromReal (G := G) C hc B E.2).domain x).symm)))).trans
    (gammaGroundVFSemiringClass_product _ _)
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · obtain ⟨U₀,Y,hY,hU,hV,hW,hX⟩ := h
      subst U V W X
      have e₁ := gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (U₀.restrict Y hY) ⟶
        (vfFiniteFromReal (G := G) C hc B U₀).restrict (GammaGroundDefSet.ofReal Y) hY from GammaGroundBijection.ofCarrierEq rfl))
      have e₂ := gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (U₀.restrict (U₀.difference Y) (fun _ h => h.1)) ⟶
        (vfFiniteFromReal (G := G) C hc B U₀).restrict ((vfFiniteFromReal (G := G) C hc B U₀).domain.sdiff (GammaGroundDefSet.ofReal Y))
          (fun _ h => h.1) from GammaGroundBijection.ofCarrierEq rfl))
      have e₃ := gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (VFObject.empty (C.base : Set M) k) ⟶
        GammaGroundFiniteVFObject.empty hc (measuredRealGroundContext C B).base from GammaGroundBijection.ofCarrierEq rfl))
      change gammaGroundVFSemiringClass _ + gammaGroundVFSemiringClass _ =
        gammaGroundVFSemiringClass _ + gammaGroundVFSemiringClass _
      rw [e₁,e₂,e₃]
      exact gammaGroundVFSemiringClass_scissor ⟨_,_,hY,rfl,rfl,rfl,rfl⟩
    · have e₀ (j : ℕ) := gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (VFObject.empty (C.base : Set M) j) ⟶
        GammaGroundFiniteVFObject.empty hc (measuredRealGroundContext C B).base from GammaGroundBijection.ofCarrierEq rfl))
      change gammaGroundVFSemiringClass _ + gammaGroundVFSemiringClass _ =
        gammaGroundVFSemiringClass _ + gammaGroundVFSemiringClass _
      rw [e₀ k,e₀ 0]

/-- Ordinary → Γ-ground positive VF semiring. -/
def vfSemiringFrom : VFPositiveSemiring C hc hv →+* GammaGroundVFPositiveSemiring hc (measuredRealGroundContext C B).base :=
  PositiveGrothendieck.lift _ (vfSemiringFromInvariant C hc B hv)

theorem vfSemiringFrom_class {k : ℕ} (U : VFObject (M := M) (C.base : Set M) k) :
    vfSemiringFrom C hc B hv (vfSemiringClass C hc hv U) = gammaGroundVFSemiringClass (vfFiniteFromReal (G := G) C hc B U) :=
  PositiveGrothendieck.lift_of (vfSemiringPresentation C hc hv) (vfSemiringFromInvariant C hc B hv) ⟨k,U⟩

def vfSemiringToInvariant : PositiveGrothendieck.Invariant (gammaGroundVFSemiringPresentation hc (measuredRealGroundContext C B).base)
    (R := VFPositiveSemiring C hc hv) where
  toFun A := vfSemiringClass C hc hv (vfFiniteToReal (G := G) C hc B A)
  iso := by
    rintro A E ⟨e⟩
    exact vfSemiringClass_bijection C hc hv
      ⟨e.hom.map.toRealNames (measuredRealGroundContext_gamma_names C B),e.hom.bijective⟩
  empty := (vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq (A := (vfFiniteToReal (G := G) C hc B
      (GammaGroundFiniteVFObject.empty hc (measuredRealGroundContext C B).base)).domain)
      (B := (VFObject.empty (C.base : Set M) 0).domain) rfl)).trans (vfSemiringClass_empty C hc hv)
  unit := (vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq (A := (vfFiniteToReal (G := G) C hc B
      (GammaGroundFiniteVFObject.unit hc (measuredRealGroundContext C B).base)).domain)
      (B := (VFObject.unit (C.base : Set M)).domain) rfl)).trans (vfSemiringClass_unit C hc hv)
  product A E := (vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq
      (A := (vfFiniteToReal (G := G) C hc B (A.product E)).domain)
      (B := ((vfFiniteToReal (G := G) C hc B A).product hc C.saturated C.small hv (vfFiniteToReal (G := G) C hc B E)).domain) (by
      ext x
      exact (mem_gammaGroundMixedProductDomain A.domain E.domain x).trans
        (mem_mixedProductDomain (vfFiniteToReal (G := G) C hc B A).domain (vfFiniteToReal (G := G) C hc B E).domain x).symm))).trans
    (vfSemiringClass_product C hc hv _ _)
  scissor := by
    rintro A E F H ⟨U,X,hX,hA,hE,hF,hH⟩
    subst A E F H
    have e₁ := vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq
      (A := (vfFiniteToReal (G := G) C hc B (U.restrict X hX)).domain)
      (B := ((vfFiniteToReal (G := G) C hc B U).restrict (X.toRealNames (measuredRealGroundContext_gamma_names C B)) hX).domain) rfl)
    have e₂ := vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq
      (A := (vfFiniteToReal (G := G) C hc B (U.restrict (U.domain.sdiff X) (fun _ h => h.1))).domain)
      (B := ((vfFiniteToReal (G := G) C hc B U).restrict ((vfFiniteToReal (G := G) C hc B U).difference
        (X.toRealNames (measuredRealGroundContext_gamma_names C B))) (fun _ h => h.1)).domain) rfl)
    have e₃ := vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq
      (A := (vfFiniteToReal (G := G) C hc B (GammaGroundFiniteVFObject.empty hc (measuredRealGroundContext C B).base)).domain)
      (B := (VFObject.empty (C.base : Set M) U.vfArity).domain) rfl)
    change vfSemiringClass C hc hv _ + vfSemiringClass C hc hv _ = vfSemiringClass C hc hv _ + vfSemiringClass C hc hv _
    rw [e₁,e₂,e₃]
    exact vfSemiringClass_scissor C hc hv ⟨_,_,hX,rfl,rfl,rfl,rfl⟩

/-- Γ-ground → ordinary positive VF semiring. -/
def vfSemiringTo : GammaGroundVFPositiveSemiring hc (measuredRealGroundContext C B).base →+* VFPositiveSemiring C hc hv :=
  PositiveGrothendieck.lift _ (vfSemiringToInvariant C hc B hv)

theorem vfSemiringTo_class (U : GammaGroundFiniteVFObject hc (measuredRealGroundContext C B).base) :
    vfSemiringTo C hc B hv (gammaGroundVFSemiringClass U) = vfSemiringClass C hc hv (vfFiniteToReal (G := G) C hc B U) :=
  PositiveGrothendieck.lift_of (gammaGroundVFSemiringPresentation hc (measuredRealGroundContext C B).base)
    (vfSemiringToInvariant C hc B hv) U

theorem vfSemiringTo_from (a : VFPositiveSemiring C hc hv) :
    vfSemiringTo C hc B hv (vfSemiringFrom C hc B hv a) = a := by
  have he : (vfSemiringTo C hc B hv).comp (vfSemiringFrom C hc B hv) = RingHom.id _ := by
    apply positivePresentationHom_ext (vfSemiringPresentation C hc hv)
    rintro ⟨k,U⟩
    change vfSemiringTo C hc B hv (vfSemiringFrom C hc B hv (vfSemiringClass C hc hv U)) = vfSemiringClass C hc hv U
    rw [vfSemiringFrom_class,vfSemiringTo_class]
    exact vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq rfl)
  exact RingHom.congr_fun he a

theorem vfSemiringFrom_to (a : GammaGroundVFPositiveSemiring hc (measuredRealGroundContext C B).base) :
    vfSemiringFrom C hc B hv (vfSemiringTo C hc B hv a) = a := by
  have he : (vfSemiringFrom C hc B hv).comp (vfSemiringTo C hc B hv) = RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundVFSemiringPresentation hc (measuredRealGroundContext C B).base)
    intro U
    change vfSemiringFrom C hc B hv (vfSemiringTo C hc B hv (gammaGroundVFSemiringClass U)) = gammaGroundVFSemiringClass U
    rw [vfSemiringTo_class,vfSemiringFrom_class]
    exact gammaGroundVFSemiringClass_iso (asIso (show vfFiniteFromReal (G := G) C hc B (vfFiniteToReal (G := G) C hc B U) ⟶ U from
      GammaGroundBijection.ofCarrierEq rfl))
  exact RingHom.congr_fun he a

/-- The ordinary and Γ-ground positive VF semirings are isomorphic. -/
def vfSemiringEquiv : VFPositiveSemiring C hc hv ≃+* GammaGroundVFPositiveSemiring hc (measuredRealGroundContext C B).base :=
  RingEquiv.ofRingHom (vfSemiringFrom C hc B hv) (vfSemiringTo C hc B hv)
    (RingHom.ext (vfSemiringFrom_to C hc B hv)) (RingHom.ext (vfSemiringTo_from C hc B hv))

/-! ### The ordinary global record -/

/-- Theorem 3.22, global unmeasured part, over an ordinary VF-generated base:
the record is constructed from the Γ-ground record proved from [18]. -/
def completedOrdinaryLiftInput : YinUnmeasuredLiftInput C hc hv B := by
  let H := Section5.completed18GroundLiftInput (measuredRealGroundContext C B) hc
  exact {
    lift := (vfSemiringTo C hc B hv).comp (H.lift.comp (rvSemiringFrom C hc B))
    lift_class := fun {k} U => by
      change vfSemiringTo C hc B hv (H.lift (rvSemiringFrom C hc B (rvSemiringClass U))) = _
      rw [rvSemiringFrom_class,H.lift_class,vfSemiringTo_class]
      exact vfSemiringClass_bijection C hc hv (DefinableBijection.ofCarrierEq rfl)
    surjective := by
      intro y
      obtain ⟨z,hz⟩ := H.surjective (vfSemiringFrom C hc B hv y)
      refine ⟨rvSemiringTo C hc B z,?_⟩
      change vfSemiringTo C hc B hv (H.lift (rvSemiringFrom C hc B (rvSemiringTo C hc B z))) = y
      rw [rvSemiringFrom_to,hz,vfSemiringTo_from]
    kernel := by
      ext a b
      rw [← rvSpecial_from_iff C hc B,H.kernel]
      change H.lift (rvSemiringFrom C hc B a) = H.lift (rvSemiringFrom C hc B b) ↔
        vfSemiringTo C hc B hv (H.lift (rvSemiringFrom C hc B a)) =
          vfSemiringTo C hc B hv (H.lift (rvSemiringFrom C hc B b))
      constructor
      · intro h
        rw [h]
      · intro h
        simpa only [vfSemiringFrom_to] using congrArg (vfSemiringFrom C hc B hv) h }

end DiamondIntegral.Section3.MeasuredRealGround
