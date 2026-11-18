import «section 3».BoundedCompletedInputs
import «section 3».CitedBoundedIntegral
import «section 3».MeasuredRealGroundObjects
import «section 3».RVGradedComparison
import «section 3».GammaGroundRVGradedComparison

/-! Theorem 3.22, bounded part, over an ordinary VF-generated base. A
VF-generated base is (VF, Γ)-generated with the Γ names of its own values
(`measuredRealGroundContext`). The ordinary unmeasured categories over the
base are identified with the Γ-ground ones, without forms (the unmeasured
counterpart of the `MeasuredRealGround` comparisons), and the bounded input
record proved from [18] over the Γ-ground transfers to the ordinary record. -/

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
variable (B : Section2.VFGeneratedFieldBase C.base) {k l : ℕ}

/-! ### RV objects and bijections -/

def rvObjFromReal (U : RVObject (M := M) (C.base : Set M) k) : GammaGroundRVObject hc (measuredRealGroundContext C B).base k :=
  GammaGroundRVObject.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) U

def rvBijFromReal {U V : RVObject (M := M) (C.base : Set M) k}
    (e : DefinableBijection U.domain V.domain) :
    GammaGroundBijection (rvObjFromReal C hc B U).domain (rvObjFromReal C hc B V).domain :=
  ⟨GammaGroundMap.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) e.map,e.bijective⟩

def rvBijToReal {U V : GammaGroundRVObject hc (measuredRealGroundContext C B).base k} (e : GammaGroundBijection U.domain V.domain) :
    DefinableBijection (rvToRealUnderlying C hc B U).domain (rvToRealUnderlying C hc B V).domain :=
  ⟨e.map.toRealNames (measuredRealGroundContext_gamma_names C B),e.bijective⟩

theorem rvDegreeFrom_empty (k : ℕ) :
    gammaGroundRVClass (rvObjFromReal C hc B (RVObject.empty (C.base : Set M) k)) = 0 :=
  (gammaGroundRVClass_iso (asIso (show rvObjFromReal C hc B (RVObject.empty (C.base : Set M) k) ⟶
    GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base k from GammaGroundBijection.id _))).trans gammaGroundRVClass_empty

theorem rvDegreeTo_empty (k : ℕ) :
    rvClass (rvToRealUnderlying C hc B (GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base k)) = 0 :=
  (rvClass_iso (asIso (show rvToRealUnderlying C hc B (GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base k) ⟶
    RVObject.empty (C.base : Set M) k from DefinableBijection.id _))).trans rvClass_empty

def rvDegreeFromInvariant (k : ℕ) : PositiveAdditiveGrothendieck.Invariant (rvPresentation (M := M) (C.base : Set M) k)
    (A := GammaGroundRVKPlus hc (measuredRealGroundContext C B).base k) where
  toFun U := gammaGroundRVClass (rvObjFromReal C hc B U)
  iso {U V} h := by
    obtain ⟨e⟩ := h
    exact gammaGroundRVClass_iso (asIso (show rvObjFromReal C hc B U ⟶ rvObjFromReal C hc B V from
      rvBijFromReal C hc B e.hom))
  empty := rvDegreeFrom_empty C hc B k
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    have h₁ := gammaGroundRVClass_iso (asIso (show rvObjFromReal C hc B (U.restrict X hX) ⟶
      (rvObjFromReal C hc B U).restrict (GammaGroundDefSet.ofReal X) hX from GammaGroundBijection.id _))
    have h₂ := gammaGroundRVClass_iso (asIso (show rvObjFromReal C hc B (U.restrict (U.difference X) (fun _ h => h.1)) ⟶
      (rvObjFromReal C hc B U).restrict ((rvObjFromReal C hc B U).domain.sdiff (GammaGroundDefSet.ofReal X))
        (fun _ h => h.1) from GammaGroundBijection.id _))
    change gammaGroundRVClass _ + gammaGroundRVClass _ = gammaGroundRVClass _ +
      gammaGroundRVClass (rvObjFromReal C hc B (RVObject.empty (C.base : Set M) k))
    rw [h₁,h₂,rvDegreeFrom_empty,add_zero]
    exact gammaGroundRVClass_scissor _ _ _

def rvDegreeToInvariant (k : ℕ) : PositiveAdditiveGrothendieck.Invariant (gammaGroundRVPresentation hc (measuredRealGroundContext C B).base k)
    (A := RVKPlus (M := M) (C.base : Set M) k) where
  toFun U := rvClass (rvToRealUnderlying C hc B U)
  iso {U V} h := by
    obtain ⟨e⟩ := h
    exact rvClass_iso (asIso (show rvToRealUnderlying C hc B U ⟶ rvToRealUnderlying C hc B V from
      rvBijToReal C hc B e.hom))
  empty := rvDegreeTo_empty C hc B k
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    have h₁ := rvClass_iso (asIso (show rvToRealUnderlying C hc B (U.restrict X hX) ⟶
      (rvToRealUnderlying C hc B U).restrict (X.toRealNames (measuredRealGroundContext_gamma_names C B)) hX from DefinableBijection.id _))
    have h₂ := rvClass_iso (asIso (show rvToRealUnderlying C hc B (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) ⟶
      (rvToRealUnderlying C hc B U).restrict ((rvToRealUnderlying C hc B U).difference (X.toRealNames (measuredRealGroundContext_gamma_names C B)))
        (fun _ h => h.1) from DefinableBijection.id _))
    change rvClass _ + rvClass _ = rvClass _ + rvClass (rvToRealUnderlying C hc B (GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base k))
    rw [h₁,h₂,rvDegreeTo_empty,add_zero]
    exact rvClass_scissor _ _ _

def rvDegreeFrom (k : ℕ) : RVKPlus (M := M) (C.base : Set M) k →+ GammaGroundRVKPlus hc (measuredRealGroundContext C B).base k :=
  PositiveAdditiveGrothendieck.lift _ (rvDegreeFromInvariant C hc B k)

def rvDegreeTo (k : ℕ) : GammaGroundRVKPlus hc (measuredRealGroundContext C B).base k →+ RVKPlus (M := M) (C.base : Set M) k :=
  PositiveAdditiveGrothendieck.lift _ (rvDegreeToInvariant C hc B k)

theorem rvDegreeFrom_class (U : RVObject (M := M) (C.base : Set M) k) :
    rvDegreeFrom C hc B k (rvClass U) = gammaGroundRVClass (rvObjFromReal C hc B U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem rvDegreeTo_class (U : GammaGroundRVObject hc (measuredRealGroundContext C B).base k) :
    rvDegreeTo C hc B k (gammaGroundRVClass U) = rvClass (rvToRealUnderlying C hc B U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

/-- Ordinary and Γ-ground `K₊RV[k]` agree. -/
def rvDegreeEquiv (k : ℕ) : RVKPlus (M := M) (C.base : Set M) k ≃+ GammaGroundRVKPlus hc (measuredRealGroundContext C B).base k := by
  have h₁ : (rvDegreeTo C hc B k).comp (rvDegreeFrom C hc B k) = AddMonoidHom.id _ := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro U
    change rvDegreeTo C hc B k (rvDegreeFrom C hc B k (rvClass U)) = rvClass U
    rw [rvDegreeFrom_class,rvDegreeTo_class]
    exact rvClass_iso (asIso (show rvToRealUnderlying C hc B (rvObjFromReal C hc B U) ⟶ U from DefinableBijection.id _))
  have h₂ : (rvDegreeFrom C hc B k).comp (rvDegreeTo C hc B k) = AddMonoidHom.id _ := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro U
    change rvDegreeFrom C hc B k (rvDegreeTo C hc B k (gammaGroundRVClass U)) = gammaGroundRVClass U
    rw [rvDegreeTo_class,rvDegreeFrom_class]
    exact gammaGroundRVClass_iso (asIso (show rvObjFromReal C hc B (rvToRealUnderlying C hc B U) ⟶ U from
      GammaGroundBijection.id _))
  exact {
    toFun := rvDegreeFrom C hc B k
    invFun := rvDegreeTo C hc B k
    left_inv := fun x => DFunLike.congr_fun h₁ x
    right_inv := fun x => DFunLike.congr_fun h₂ x
    map_add' := (rvDegreeFrom C hc B k).map_add }

/-! ### VF[k] -/

section VF
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def vfObjFromReal (U : VFObject (M := M) (C.base : Set M) k) : GammaGroundVFObject hc (measuredRealGroundContext C B).base k :=
  GammaGroundVFObject.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) U

def vfObjToReal (U : GammaGroundVFObject hc (measuredRealGroundContext C B).base k) : VFObject (M := M) (C.base : Set M) k :=
  ⟨U.vfArity,U.rvArity,U.domain.toRealNames (measuredRealGroundContext_gamma_names C B),U.dimension,U.finite⟩

theorem vfDegreeFrom_empty (k : ℕ) :
    gammaGroundVFClass (vfObjFromReal C hc B (VFObject.empty (C.base : Set M) k)) = 0 :=
  (gammaGroundVFClass_iso (asIso (show vfObjFromReal C hc B (VFObject.empty (C.base : Set M) k) ⟶
    GammaGroundVFObject.empty hc (measuredRealGroundContext C B).base k from GammaGroundBijection.id _))).trans gammaGroundVFClass_empty

theorem vfDegreeTo_empty (k : ℕ) :
    vfClass (vfObjToReal C hc B (GammaGroundVFObject.empty hc (measuredRealGroundContext C B).base k)) = 0 :=
  (vfClass_iso (asIso (show vfObjToReal C hc B (GammaGroundVFObject.empty hc (measuredRealGroundContext C B).base k) ⟶
    VFObject.empty (C.base : Set M) k from DefinableBijection.id _))).trans vfClass_empty

def vfDegreeFromInvariant (k : ℕ) : PositiveAdditiveGrothendieck.Invariant (vfPresentation (M := M) (C.base : Set M) k)
    (A := GammaGroundVFKPlus hc (measuredRealGroundContext C B).base k) where
  toFun U := gammaGroundVFClass (vfObjFromReal C hc B U)
  iso {U V} h := by
    obtain ⟨e⟩ := h
    exact gammaGroundVFClass_iso (asIso (show vfObjFromReal C hc B U ⟶ vfObjFromReal C hc B V from
      ⟨GammaGroundMap.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) e.hom.map,e.hom.bijective⟩))
  empty := vfDegreeFrom_empty C hc B k
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    have h₁ := gammaGroundVFClass_iso (asIso (show vfObjFromReal C hc B (U.restrict X hX) ⟶
      (vfObjFromReal C hc B U).restrict (GammaGroundDefSet.ofReal X) hX from GammaGroundBijection.id _))
    have h₂ := gammaGroundVFClass_iso (asIso (show vfObjFromReal C hc B (U.restrict (U.difference X) (fun _ h => h.1)) ⟶
      (vfObjFromReal C hc B U).restrict ((vfObjFromReal C hc B U).domain.sdiff (GammaGroundDefSet.ofReal X))
        (fun _ h => h.1) from GammaGroundBijection.id _))
    change gammaGroundVFClass _ + gammaGroundVFClass _ = gammaGroundVFClass _ +
      gammaGroundVFClass (vfObjFromReal C hc B (VFObject.empty (C.base : Set M) k))
    rw [h₁,h₂,vfDegreeFrom_empty,add_zero]
    exact gammaGroundVFClass_scissor _ _ _

def vfDegreeToInvariant (k : ℕ) : PositiveAdditiveGrothendieck.Invariant (gammaGroundVFPresentation hc (measuredRealGroundContext C B).base k)
    (A := VFKPlus (M := M) (C.base : Set M) k) where
  toFun U := vfClass (vfObjToReal C hc B U)
  iso {U V} h := by
    obtain ⟨e⟩ := h
    exact vfClass_iso (asIso (show vfObjToReal C hc B U ⟶ vfObjToReal C hc B V from
      ⟨e.hom.map.toRealNames (measuredRealGroundContext_gamma_names C B),e.hom.bijective⟩))
  empty := vfDegreeTo_empty C hc B k
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    have h₁ := vfClass_iso (asIso (show vfObjToReal C hc B (U.restrict X hX) ⟶
      (vfObjToReal C hc B U).restrict (X.toRealNames (measuredRealGroundContext_gamma_names C B)) hX from DefinableBijection.id _))
    have h₂ := vfClass_iso (asIso (show vfObjToReal C hc B (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) ⟶
      (vfObjToReal C hc B U).restrict ((vfObjToReal C hc B U).difference (X.toRealNames (measuredRealGroundContext_gamma_names C B)))
        (fun _ h => h.1) from DefinableBijection.id _))
    change vfClass _ + vfClass _ = vfClass _ + vfClass (vfObjToReal C hc B (GammaGroundVFObject.empty hc (measuredRealGroundContext C B).base k))
    rw [h₁,h₂,vfDegreeTo_empty,add_zero]
    exact vfClass_scissor _ _ _

def vfDegreeFrom (k : ℕ) : VFKPlus (M := M) (C.base : Set M) k →+ GammaGroundVFKPlus hc (measuredRealGroundContext C B).base k :=
  PositiveAdditiveGrothendieck.lift _ (vfDegreeFromInvariant C hc B k)

def vfDegreeTo (k : ℕ) : GammaGroundVFKPlus hc (measuredRealGroundContext C B).base k →+ VFKPlus (M := M) (C.base : Set M) k :=
  PositiveAdditiveGrothendieck.lift _ (vfDegreeToInvariant C hc B k)

theorem vfDegreeFrom_class (U : VFObject (M := M) (C.base : Set M) k) :
    vfDegreeFrom C hc B k (vfClass U) = gammaGroundVFClass (vfObjFromReal C hc B U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem vfDegreeTo_class (U : GammaGroundVFObject hc (measuredRealGroundContext C B).base k) :
    vfDegreeTo C hc B k (gammaGroundVFClass U) = vfClass (vfObjToReal C hc B U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

/-- Ordinary and Γ-ground `K₊VF[k]` agree. -/
def vfDegreeEquiv (k : ℕ) : VFKPlus (M := M) (C.base : Set M) k ≃+ GammaGroundVFKPlus hc (measuredRealGroundContext C B).base k := by
  have h₁ : (vfDegreeTo C hc B k).comp (vfDegreeFrom C hc B k) = AddMonoidHom.id _ := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro U
    change vfDegreeTo C hc B k (vfDegreeFrom C hc B k (vfClass U)) = vfClass U
    rw [vfDegreeFrom_class,vfDegreeTo_class]
    exact vfClass_iso (asIso (show vfObjToReal C hc B (vfObjFromReal C hc B U) ⟶ U from DefinableBijection.id _))
  have h₂ : (vfDegreeFrom C hc B k).comp (vfDegreeTo C hc B k) = AddMonoidHom.id _ := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro U
    change vfDegreeFrom C hc B k (vfDegreeTo C hc B k (gammaGroundVFClass U)) = gammaGroundVFClass U
    rw [vfDegreeTo_class,vfDegreeFrom_class]
    exact gammaGroundVFClass_iso (asIso (show vfObjFromReal C hc B (vfObjToReal C hc B U) ⟶ U from
      GammaGroundBijection.id _))
  exact {
    toFun := vfDegreeFrom C hc B k
    invFun := vfDegreeTo C hc B k
    left_inv := fun x => DFunLike.congr_fun h₁ x
    right_inv := fun x => DFunLike.congr_fun h₂ x
    map_add' := (vfDegreeFrom C hc B k).map_add }

theorem vfDegreeEquiv_class (U : VFObject (M := M) (C.base : Set M) k) :
    vfDegreeEquiv (G := G) C hc B k (vfClass U) = gammaGroundVFClass (vfObjFromReal C hc B U) :=
  vfDegreeFrom_class C hc B U

end VF

/-! ### Global RV semirings and special congruences -/

def rvSemiringFromInvariant : PositiveGrothendieck.Invariant (rvSemiringPresentation (M := M) (C.base : Set M))
    (R := GammaGroundRVPositiveSemiring hc (measuredRealGroundContext C B).base) where
  toFun A := gammaGroundRVSemiringClass (rvObjFromReal C hc B A.2)
  iso := by
    rintro ⟨k,U⟩ ⟨l,V⟩ ⟨hkl,⟨e⟩⟩
    change k = l at hkl
    subst hkl
    exact gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B U ⟶ rvObjFromReal C hc B V from
      rvBijFromReal C hc B e))
  empty := (gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (RVObject.empty (C.base : Set M) 0) ⟶
    GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base 0 from GammaGroundBijection.id _))).trans gammaGroundRVSemiringClass_empty
  unit := (gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (RVObject.unit (C.base : Set M)) ⟶
    GammaGroundRVObject.unit hc (measuredRealGroundContext C B).base from GammaGroundBijection.id _))).trans gammaGroundRVSemiringClass_unit
  product A E := (gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (A.2.product E.2) ⟶
    (rvObjFromReal C hc B A.2).product (rvObjFromReal C hc B E.2) from GammaGroundBijection.ofCarrierEq (by
      ext x
      exact (mem_rvProductDomain A.2.domain E.2.domain x).trans
        (mem_gammaGroundRVProductDomain (rvObjFromReal C hc B A.2).domain (rvObjFromReal C hc B E.2).domain x).symm)))).trans
    (gammaGroundRVSemiringClass_product _ _)
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · obtain ⟨U₀,Y,hY,hU,hV,hW,hX⟩ := h
      subst U V W X
      have e₁ := gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (U₀.restrict Y hY) ⟶
        (rvObjFromReal C hc B U₀).restrict (GammaGroundDefSet.ofReal Y) hY from GammaGroundBijection.id _))
      have e₂ := gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (U₀.restrict (U₀.difference Y) (fun _ h => h.1)) ⟶
        (rvObjFromReal C hc B U₀).restrict ((rvObjFromReal C hc B U₀).domain.sdiff (GammaGroundDefSet.ofReal Y))
          (fun _ h => h.1) from GammaGroundBijection.id _))
      have e₃ := gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (RVObject.empty (C.base : Set M) k) ⟶
        GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base k from GammaGroundBijection.id _))
      change gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _ =
        gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _
      rw [e₁,e₂,e₃]
      exact gammaGroundRVSemiringClass_scissor ⟨_,_,hY,rfl,rfl,rfl,rfl⟩
    · have e₀ (j : ℕ) := gammaGroundRVSemiringClass_iso (asIso (show rvObjFromReal C hc B (RVObject.empty (C.base : Set M) j) ⟶
        GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base j from GammaGroundBijection.id _))
      change gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _ =
        gammaGroundRVSemiringClass _ + gammaGroundRVSemiringClass _
      rw [e₀ k,e₀ 0]
      simp only [gammaGroundRVSemiringClass_empty,add_zero]

def rvSemiringFrom : RVPositiveSemiring (M := M) (C.base : Set M) →+* GammaGroundRVPositiveSemiring hc (measuredRealGroundContext C B).base :=
  PositiveGrothendieck.lift _ (rvSemiringFromInvariant C hc B)

theorem rvSemiringFrom_class (U : RVObject (M := M) (C.base : Set M) k) :
    rvSemiringFrom C hc B (rvSemiringClass U) = gammaGroundRVSemiringClass (rvObjFromReal C hc B U) :=
  PositiveGrothendieck.lift_of (rvSemiringPresentation (M := M) (C.base : Set M)) (rvSemiringFromInvariant C hc B) ⟨k,U⟩

def rvSemiringToInvariant : PositiveGrothendieck.Invariant (gammaGroundRVSemiringPresentation hc (measuredRealGroundContext C B).base)
    (R := RVPositiveSemiring (M := M) (C.base : Set M)) where
  toFun A := rvSemiringClass (rvToRealUnderlying C hc B A.2)
  iso := by
    rintro ⟨k,U⟩ ⟨l,V⟩ ⟨hkl,⟨e⟩⟩
    change k = l at hkl
    subst hkl
    exact rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B U ⟶ rvToRealUnderlying C hc B V from
      rvBijToReal C hc B e))
  empty := (rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base 0) ⟶
    RVObject.empty (C.base : Set M) 0 from DefinableBijection.id _))).trans rvSemiringClass_empty
  unit := (rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (GammaGroundRVObject.unit hc (measuredRealGroundContext C B).base) ⟶
    RVObject.unit (C.base : Set M) from DefinableBijection.id _))).trans rvSemiringClass_unit
  product A E := (rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (A.2.product E.2) ⟶
    (rvToRealUnderlying C hc B A.2).product (rvToRealUnderlying C hc B E.2) from DefinableBijection.ofCarrierEq (by
      ext x
      exact (mem_gammaGroundRVProductDomain A.2.domain E.2.domain x).trans
        (mem_rvProductDomain (rvToRealUnderlying C hc B A.2).domain (rvToRealUnderlying C hc B E.2).domain x).symm)))).trans
    (rvSemiringClass_product _ _)
  scissor := by
    rintro A E F H (⟨k,U,V,W,X,h,rfl,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl,rfl⟩)
    · obtain ⟨U₀,Y,hY,hU,hV,hW,hX⟩ := h
      subst U V W X
      have e₁ := rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (U₀.restrict Y hY) ⟶
        (rvToRealUnderlying C hc B U₀).restrict (Y.toRealNames (measuredRealGroundContext_gamma_names C B)) hY from DefinableBijection.id _))
      have e₂ := rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (U₀.restrict (U₀.domain.sdiff Y) (fun _ h => h.1)) ⟶
        (rvToRealUnderlying C hc B U₀).restrict ((rvToRealUnderlying C hc B U₀).difference (Y.toRealNames (measuredRealGroundContext_gamma_names C B)))
          (fun _ h => h.1) from DefinableBijection.id _))
      have e₃ := rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base k) ⟶
        RVObject.empty (C.base : Set M) k from DefinableBijection.id _))
      change rvSemiringClass _ + rvSemiringClass _ = rvSemiringClass _ + rvSemiringClass _
      rw [e₁,e₂,e₃]
      exact rvSemiringClass_scissor ⟨_,_,hY,rfl,rfl,rfl,rfl⟩
    · have e₀ (j : ℕ) := rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (GammaGroundRVObject.empty hc (measuredRealGroundContext C B).base j) ⟶
        RVObject.empty (C.base : Set M) j from DefinableBijection.id _))
      change rvSemiringClass _ + rvSemiringClass _ = rvSemiringClass _ + rvSemiringClass _
      rw [e₀ k,e₀ 0]
      simp only [rvSemiringClass_empty,add_zero]

def rvSemiringTo : GammaGroundRVPositiveSemiring hc (measuredRealGroundContext C B).base →+* RVPositiveSemiring (M := M) (C.base : Set M) :=
  PositiveGrothendieck.lift _ (rvSemiringToInvariant C hc B)

theorem rvSemiringTo_class (U : GammaGroundRVObject hc (measuredRealGroundContext C B).base k) :
    rvSemiringTo C hc B (gammaGroundRVSemiringClass U) = rvSemiringClass (rvToRealUnderlying C hc B U) :=
  PositiveGrothendieck.lift_of (gammaGroundRVSemiringPresentation hc (measuredRealGroundContext C B).base) (rvSemiringToInvariant C hc B) ⟨k,U⟩

theorem rvSemiringTo_from (a : RVPositiveSemiring (M := M) (C.base : Set M)) :
    rvSemiringTo C hc B (rvSemiringFrom C hc B a) = a := by
  have he : (rvSemiringTo C hc B).comp (rvSemiringFrom C hc B) = RingHom.id _ := by
    apply positivePresentationHom_ext (rvSemiringPresentation (M := M) (C.base : Set M))
    rintro ⟨k,U⟩
    change rvSemiringTo C hc B (rvSemiringFrom C hc B (rvSemiringClass U)) = rvSemiringClass U
    rw [rvSemiringFrom_class,rvSemiringTo_class]
    exact rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B (rvObjFromReal C hc B U) ⟶ U from DefinableBijection.id _))
  exact RingHom.congr_fun he a

theorem rvSpecial_from {a b : RVPositiveSemiring (M := M) (C.base : Set M)}
    (h : rvSpecialCongruence hc (C.base : Set M) a b) :
    gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base (rvSemiringFrom C hc B a) (rvSemiringFrom C hc B b) := by
  let q := (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk'
  have hle : rvSpecialCongruence hc (C.base : Set M) ≤ RingCon.ker (q.comp (rvSemiringFrom C hc B)) := by
    apply RingCon.ringConGen_le.mpr
    rintro x y ⟨rfl,rfl⟩
    change q (rvSemiringFrom C hc B _) = q (rvSemiringFrom C hc B (_ + 1))
    rw [RingHom.map_add,RingHom.map_one,rvSemiringFrom_class,rvSemiringFrom_class]
    exact (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).eq.mpr (RingConGen.Rel.of _ _ ⟨rfl,rfl⟩)
  exact (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).eq.mp (hle h)

theorem rvSpecial_to {a b : GammaGroundRVPositiveSemiring hc (measuredRealGroundContext C B).base}
    (h : gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base a b) :
    rvSpecialCongruence hc (C.base : Set M) (rvSemiringTo C hc B a) (rvSemiringTo C hc B b) := by
  let q := (rvSpecialCongruence hc (C.base : Set M)).mk'
  have hle : gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base ≤ RingCon.ker (q.comp (rvSemiringTo C hc B)) := by
    apply RingCon.ringConGen_le.mpr
    rintro x y ⟨rfl,rfl⟩
    change q (rvSemiringTo C hc B _) = q (rvSemiringTo C hc B (_ + 1))
    rw [RingHom.map_add,RingHom.map_one,rvSemiringTo_class,rvSemiringTo_class]
    have h₁ := rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B
      (GammaGroundRVObject.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) (rvOneObject (measuredRealGroundContext C B).base.real)) ⟶
      rvOneObject (C.base : Set M) from DefinableBijection.id _))
    have h₂ := rvSemiringClass_iso (asIso (show rvToRealUnderlying C hc B
      (GammaGroundRVObject.ofReal (hc := hc) (ground := (measuredRealGroundContext C B).base) (rvPositiveObject hc (measuredRealGroundContext C B).base.real)) ⟶
      rvPositiveObject hc (C.base : Set M) from DefinableBijection.id _))
    rw [h₁,h₂]
    exact (rvSpecialCongruence hc (C.base : Set M)).eq.mpr (RingConGen.Rel.of _ _ ⟨rfl,rfl⟩)
  exact (rvSpecialCongruence hc (C.base : Set M)).eq.mp (hle h)

theorem rvSpecial_from_iff (a b : RVPositiveSemiring (M := M) (C.base : Set M)) :
    gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base (rvSemiringFrom C hc B a) (rvSemiringFrom C hc B b) ↔
      rvSpecialCongruence hc (C.base : Set M) a b := by
  constructor
  · intro h
    simpa only [rvSemiringTo_from] using rvSpecial_to C hc B h
  · exact rvSpecial_from C hc B

/-! ### Bounded RV sources -/

def rvBoundedEquiv (k : ℕ) : RVBoundedPositive (M := M) (C.base : Set M) k ≃+ GammaGroundRVBoundedPositive hc (measuredRealGroundContext C B).base k where
  toFun := DirectSum.map (fun i : Fin (k+1) => (rvDegreeEquiv C hc B i.val).toAddMonoidHom)
  invFun := DirectSum.map (fun i : Fin (k+1) => (rvDegreeEquiv C hc B i.val).symm.toAddMonoidHom)
  left_inv x := by
    apply DFinsupp.ext
    intro i
    exact (rvDegreeEquiv C hc B i.val).symm_apply_apply (x i)
  right_inv x := by
    apply DFinsupp.ext
    intro i
    exact (rvDegreeEquiv C hc B i.val).apply_symm_apply (x i)
  map_add' := (DirectSum.map (fun i : Fin (k+1) => (rvDegreeEquiv C hc B i.val).toAddMonoidHom)).map_add

theorem rvBoundedEquiv_class (i : Fin (k+1)) (U : RVObject (M := M) (C.base : Set M) i.val) :
    rvBoundedEquiv C hc B k (rvBoundedClass i U) = gammaGroundRVBoundedClass i (rvObjFromReal C hc B U) := by
  change DirectSum.map (fun i : Fin (k+1) => (rvDegreeEquiv C hc B i.val).toAddMonoidHom)
    (DirectSum.of _ i (rvClass U)) = DirectSum.of _ i (gammaGroundRVClass (rvObjFromReal C hc B U))
  rw [DirectSum.map_of]
  exact congrArg (DirectSum.of _ i) (rvDegreeFrom_class C hc B U)

theorem rvBoundedEquiv_include (a : RVBoundedPositive (M := M) (C.base : Set M) k) :
    rvSemiringFrom C hc B (rvBoundedInclude a) = gammaGroundRVBoundedInclude (rvBoundedEquiv C hc B k a) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i c =>
    obtain ⟨U,rfl⟩ := rvClass_surjective c
    change rvSemiringFrom C hc B (rvBoundedInclude (rvBoundedClass i U)) =
      gammaGroundRVBoundedInclude (rvBoundedEquiv C hc B k (rvBoundedClass i U))
    rw [rvBoundedInclude_class,rvSemiringFrom_class,rvBoundedEquiv_class,gammaGroundRVBoundedInclude_class]
  | add a b ha hb => rw [map_add,RingHom.map_add,map_add,map_add,ha,hb]

theorem rvBoundedSpecial_iff (a b : RVBoundedPositive (M := M) (C.base : Set M) k) :
    gammaGroundRVBoundedSpecialCongruence (ground := (measuredRealGroundContext C B).base) (k := k) hc (rvBoundedEquiv C hc B k a) (rvBoundedEquiv C hc B k b) ↔
      rvBoundedSpecialCongruence (S := (C.base : Set M)) (k := k) hc a b := by
  change (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk' (gammaGroundRVBoundedInclude (rvBoundedEquiv C hc B k a)) =
      (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk' (gammaGroundRVBoundedInclude (rvBoundedEquiv C hc B k b)) ↔
    (rvSpecialCongruence hc (C.base : Set M)).mk' (rvBoundedInclude a) = (rvSpecialCongruence hc (C.base : Set M)).mk' (rvBoundedInclude b)
  rw [← rvBoundedEquiv_include,← rvBoundedEquiv_include]
  rw [show ∀ x y, (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk' x = (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).mk' y ↔
      gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base x y from fun x y => (gammaGroundRVSpecialCongruence hc (measuredRealGroundContext C B).base).eq,
    show ∀ x y, (rvSpecialCongruence hc (C.base : Set M)).mk' x = (rvSpecialCongruence hc (C.base : Set M)).mk' y ↔
      rvSpecialCongruence hc (C.base : Set M) x y from fun x y => (rvSpecialCongruence hc (C.base : Set M)).eq]
  exact rvSpecial_from_iff C hc B _ _

section Assembly
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem lift_vfDegree (i : Fin (k+1)) (U : RVObject (M := M) (C.base : Set M) i.val) :
    vfDegreeEquiv (G := G) C hc B k (vfClass ((objectLiftVF U).raise (Nat.le_of_lt_succ i.isLt))) =
      gammaGroundVFClass ((gammaGroundObjectLiftVF (rvObjFromReal C hc B U)).raise (Nat.le_of_lt_succ i.isLt)) := by
  rw [vfDegreeEquiv_class]
  apply gammaGroundVFClass_iso
  exact asIso (show _ ⟶ _ from GammaGroundBijection.ofCarrierEq rfl)

/-- Theorem 3.22, bounded part, over an ordinary VF-generated base: the input
record is constructed from the Γ-ground record proved from [18]. -/
def completedOrdinaryBoundedLiftInput : YinBoundedUnmeasuredLiftInput C hc hv B := by
  let H := completedGammaGroundBoundedLiftInput (G := G) (measuredRealGroundContext C B) hc hv
  exact {
    lift := fun k => (vfDegreeEquiv (G := G) C hc B k).symm.toAddMonoidHom.comp
      ((H.lift k).comp (rvBoundedEquiv C hc B k).toAddMonoidHom)
    lift_class := fun k i U => by
      apply (vfDegreeEquiv (G := G) C hc B k).injective
      change vfDegreeEquiv C hc B k ((vfDegreeEquiv C hc B k).symm (H.lift k (rvBoundedEquiv C hc B k (rvBoundedClass i U)))) = _
      rw [AddEquiv.apply_symm_apply,rvBoundedEquiv_class,H.lift_class,lift_vfDegree]
    surjective := fun k => (vfDegreeEquiv (G := G) C hc B k).symm.surjective.comp
      ((H.surjective k).comp (rvBoundedEquiv C hc B k).surjective)
    kernel := fun k => by
      ext a b
      rw [AddCon.ker_rel,← rvBoundedSpecial_iff,H.kernel k,AddCon.ker_rel]
      change _ ↔ (vfDegreeEquiv C hc B k).symm (H.lift k (rvBoundedEquiv C hc B k a)) =
        (vfDegreeEquiv C hc B k).symm (H.lift k (rvBoundedEquiv C hc B k b))
      exact (vfDegreeEquiv (G := G) C hc B k).symm.injective.eq_iff.symm }

end Assembly

end DiamondIntegral.Section3.MeasuredRealGround
