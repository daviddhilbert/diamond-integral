import «section 3».GammaGroundVFFiltration

/-! The genuine dimension filtration has the expected directed-limit
universal property over the entire Gamma ground. No injectivity or
semiring-presentation comparison is assumed by this additive statement. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {A : Type*} [AddCommMonoid A]

structure CompatibleGammaGroundVFPositiveMaps (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (A : Type*) [AddCommMonoid A] where
  map : ∀ k, GammaGroundVFKPlus hc ground k →+ A
  compatible : ∀ k l (hkl : k ≤ l), (map l).comp (gammaGroundVFRaiseKPlus hkl) = map k

@[ext] theorem CompatibleGammaGroundVFPositiveMaps.ext {F H : CompatibleGammaGroundVFPositiveMaps hc ground A}
    (h : F.map = H.map) : F = H := by
  cases F
  cases H
  cases h
  rfl

theorem compatibleGammaGroundVF_value_bijection (F : CompatibleGammaGroundVFPositiveMaps hc ground A)
    {k l : ℕ} (U : GammaGroundVFObject hc ground k) (V : GammaGroundVFObject hc ground l)
    (f : GammaGroundBijection U.domain V.domain) :
    F.map k (gammaGroundVFClass U) = F.map l (gammaGroundVFClass V) := by
  have hu := congrArg (fun g : GammaGroundVFKPlus hc ground k →+ A => g (gammaGroundVFClass U))
    (F.compatible k (max k l) (le_max_left k l))
  have hv := congrArg (fun g : GammaGroundVFKPlus hc ground l →+ A => g (gammaGroundVFClass V))
    (F.compatible l (max k l) (le_max_right k l))
  change F.map (max k l) (gammaGroundVFRaiseKPlus _ (gammaGroundVFClass U)) = _ at hu
  change F.map (max k l) (gammaGroundVFRaiseKPlus _ (gammaGroundVFClass V)) = _ at hv
  rw [gammaGroundVFRaiseKPlus_class] at hu hv
  have he : gammaGroundVFClass (U.raise (le_max_left k l)) =
      gammaGroundVFClass (V.raise (le_max_right k l)) :=
    gammaGroundVFClass_iso (asIso (show U.raise (le_max_left k l) ⟶ V.raise (le_max_right k l) from f))
  exact hu.symm.trans ((congrArg (F.map (max k l)) he).trans hv)

def gammaGroundVFColimitInvariant (F : CompatibleGammaGroundVFPositiveMaps hc ground A) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundFiniteVFPresentation hc ground) (A := A) where
  toFun U := F.map U.vfArity (gammaGroundVFClass U.toBound)
  iso := by
    rintro U V ⟨e⟩
    exact compatibleGammaGroundVF_value_bijection F U.toBound V.toBound e.hom
  empty := by
    change F.map 0 (gammaGroundVFClass (GammaGroundVFObject.empty hc ground 0)) = 0
    rw [gammaGroundVFClass_empty, map_zero]
  scissor := by
    intro A B D E h
    obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
    subst A
    subst B
    subst D
    subst E
    have h := gammaGroundVFClass_scissor U.toBound X hX
    have ht := congrArg (F.map U.vfArity) h
    have hleft : (U.restrict X hX).toBound = U.toBound.restrict X hX := by cases U; rfl
    have hright : (U.restrict (U.domain.sdiff X) (fun _ h => h.1)).toBound =
        U.toBound.restrict (U.toBound.domain.sdiff X) (fun _ h => h.1) := by cases U; rfl
    change F.map U.vfArity (gammaGroundVFClass _) + F.map U.vfArity (gammaGroundVFClass _) =
      F.map U.vfArity (gammaGroundVFClass _) + F.map 0 (gammaGroundVFClass (GammaGroundVFObject.empty hc ground 0))
    rw [gammaGroundVFClass_empty, map_zero, add_zero]
    simpa only [map_add, hleft, hright] using ht

def gammaGroundVFColimitLift (F : CompatibleGammaGroundVFPositiveMaps hc ground A) :
    GammaGroundFiniteVFKPlus hc ground →+ A :=
  PositiveAdditiveGrothendieck.lift (gammaGroundFiniteVFPresentation hc ground) (gammaGroundVFColimitInvariant F)

@[simp] theorem gammaGroundVFColimitLift_class (F : CompatibleGammaGroundVFPositiveMaps hc ground A)
    {k : ℕ} (U : GammaGroundVFObject hc ground k) :
    gammaGroundVFColimitLift F (gammaGroundFiniteVFClass (.ofBound U)) = F.map k (gammaGroundVFClass U) := by
  change PositiveAdditiveGrothendieck.lift _ (gammaGroundVFColimitInvariant F)
    (PositiveAdditiveGrothendieck.of _ (GammaGroundFiniteVFObject.ofBound U)) = _
  rw [PositiveAdditiveGrothendieck.lift_of]
  exact compatibleGammaGroundVF_value_bijection F (GammaGroundFiniteVFObject.ofBound U).toBound U
    (GammaGroundBijection.id U.domain)

theorem gammaGroundVFColimitLift_inclusion (F : CompatibleGammaGroundVFPositiveMaps hc ground A) (k : ℕ) :
    (gammaGroundVFColimitLift F).comp (gammaGroundVFToFiniteKPlus (k := k)) = F.map k := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundVFPresentation hc ground k)
  intro U
  change gammaGroundVFColimitLift F (gammaGroundVFToFiniteKPlus (gammaGroundVFClass U)) = _
  rw [gammaGroundVFToFiniteKPlus_class, gammaGroundVFColimitLift_class]
  rfl

theorem gammaGroundVFColimitLift_unique (F : CompatibleGammaGroundVFPositiveMaps hc ground A)
    (f : GammaGroundFiniteVFKPlus hc ground →+ A)
    (hf : ∀ k, f.comp (gammaGroundVFToFiniteKPlus (k := k)) = F.map k) :
    f = gammaGroundVFColimitLift F := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundFiniteVFPresentation hc ground)
  intro U
  have h := congrArg (fun g : GammaGroundVFKPlus hc ground U.vfArity →+ A => g (gammaGroundVFClass U.toBound))
    (hf U.vfArity)
  change f (gammaGroundVFToFiniteKPlus (gammaGroundVFClass U.toBound)) = _ at h
  rw [gammaGroundVFToFiniteKPlus_class, GammaGroundFiniteVFObject.of_toBound] at h
  exact h.trans (gammaGroundVFColimitLift_class F U.toBound).symm

def gammaGroundVFPositiveColimitUniversal :
    (GammaGroundFiniteVFKPlus hc ground →+ A) ≃ CompatibleGammaGroundVFPositiveMaps hc ground A where
  toFun f := {
    map := fun _ => f.comp gammaGroundVFToFiniteKPlus
    compatible := by
      intro k l hkl
      rw [AddMonoidHom.comp_assoc, gammaGroundVFToFiniteKPlus_raise] }
  invFun := gammaGroundVFColimitLift
  left_inv f := (gammaGroundVFColimitLift_unique _ f (fun _ => rfl)).symm
  right_inv F := by
    apply CompatibleGammaGroundVFPositiveMaps.ext
    funext k
    exact gammaGroundVFColimitLift_inclusion F k

end DiamondIntegral.Section3
