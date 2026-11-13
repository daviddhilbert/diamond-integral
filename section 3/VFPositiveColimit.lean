import «section 3».VFFilteredComparison

/-! The universal property of the directed limit of dimension-bounded
positive VF scissors, with actual bound-raising maps. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) {A : Type*} [AddCommMonoid A]

structure CompatibleVFPositiveMaps where
  map : ∀ k, VFKPlus (M := M) (C.base : Set M) k →+ A
  compatible : ∀ k l (hkl : k ≤ l), (map l).comp (vfRaiseKPlus hkl) = map k

@[ext] theorem CompatibleVFPositiveMaps.ext {F H : CompatibleVFPositiveMaps C (A := A)}
    (h : F.map = H.map) : F = H := by
  cases F
  cases H
  cases h
  rfl

theorem compatibleVF_value_bijection (F : CompatibleVFPositiveMaps C (A := A)) {k l : ℕ}
    (U : VFObject (M := M) (C.base : Set M) k) (V : VFObject (M := M) (C.base : Set M) l)
    (f : DefinableBijection U.domain V.domain) : F.map k (vfClass U) = F.map l (vfClass V) := by
  have hu := congrArg (fun g : VFKPlus (C.base : Set M) k →+ A => g (vfClass U))
    (F.compatible k (max k l) (le_max_left k l))
  have hv := congrArg (fun g : VFKPlus (C.base : Set M) l →+ A => g (vfClass V))
    (F.compatible l (max k l) (le_max_right k l))
  change F.map (max k l) (vfRaiseKPlus _ (vfClass U)) = _ at hu
  change F.map (max k l) (vfRaiseKPlus _ (vfClass V)) = _ at hv
  rw [vfRaiseKPlus_class] at hu hv
  have he : vfClass (U.raise (le_max_left k l)) = vfClass (V.raise (le_max_right k l)) :=
    vfClass_iso (asIso (show U.raise (le_max_left k l) ⟶ V.raise (le_max_right k l) from f))
  exact hu.symm.trans ((congrArg (F.map (max k l)) he).trans hv)

variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def vfColimitInvariant (F : CompatibleVFPositiveMaps C (A := A)) :
    PositiveAdditiveGrothendieck.Invariant (vfFiniteScissorPresentation (M := M) (C.base : Set M)) (A := A) where
  toFun U := F.map U.obj.index.1 (vfClass (vfObjectOfCompanionFinite C U))
  iso := by
    intro U V h
    obtain ⟨e⟩ := h
    exact compatibleVF_value_bijection C F (vfObjectOfCompanionFinite C U) (vfObjectOfCompanionFinite C V)
      ⟨e.hom.hom, DefinableSetCat.bijective_of_iso ((vfFiniteProperty (C.base : Set M)).ι.mapIso e)⟩
  empty := by
    change F.map 0 (vfClass (VFObject.empty (C.base : Set M) 0)) = 0
    rw [vfClass_empty, map_zero]
  scissor := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ ⟨D, hD⟩ ⟨E, hE⟩ h
    change VFAllScissor X Y D E at h
    obtain ⟨i, X', Y', hX', hY', hD', hE'⟩ := h
    subst X
    subst Y
    subst D
    subst E
    have hs : vfClass (vfObjectOfFiniteFibres X' hX) + vfClass (vfObjectOfFiniteFibres Y' hY) =
        vfClass (vfObjectOfFiniteFibres (X'.union Y') hD) + vfClass (vfObjectOfFiniteFibres (X'.inter Y') hE) := by
      apply vfKPlusToSemiring_injective C hc hv
      simp only [map_add, vfKPlusToSemiring_class]
      exact vfFiniteDomainClass_union_inter C hc hv X' Y' hX hY
    have ht := congrArg (F.map i.1) hs
    have ht' : F.map i.1 (vfClass (vfObjectOfFiniteFibres X' hX)) + F.map i.1 (vfClass (vfObjectOfFiniteFibres Y' hY)) =
        F.map i.1 (vfClass (vfObjectOfFiniteFibres (X'.union Y') hD)) + F.map i.1 (vfClass (vfObjectOfFiniteFibres (X'.inter Y') hE)) := by
      simpa only [map_add] using ht
    exact ht'

def vfColimitLift (F : CompatibleVFPositiveMaps C (A := A)) : VFPositiveSemiring C hc hv →+ A :=
  (PositiveAdditiveGrothendieck.lift (vfFiniteScissorPresentation (C.base : Set M))
    (vfColimitInvariant C hc hv F)).comp (vfSemiringToFinite C hc hv).toAddMonoidHom

@[simp] theorem vfColimitLift_class (F : CompatibleVFPositiveMaps C (A := A)) {k : ℕ}
    (U : VFObject (M := M) (C.base : Set M) k) :
    vfColimitLift C hc hv F (vfSemiringClass C hc hv U) = F.map k (vfClass U) := by
  change PositiveAdditiveGrothendieck.lift _ (vfColimitInvariant C hc hv F)
    (vfSemiringToFinite C hc hv (vfSemiringClass C hc hv U)) = _
  rw [vfSemiringToFinite_class]
  rw [vfFiniteClass, PositiveAdditiveGrothendieck.lift_of]
  exact compatibleVF_value_bijection C F (vfObjectOfCompanionFinite C U.toCompanionFinite) U
    (DefinableBijection.id U.domain)

theorem vfColimitLift_inclusion (F : CompatibleVFPositiveMaps C (A := A)) (k : ℕ) :
    (vfColimitLift C hc hv F).comp (vfKPlusToSemiring C hc hv (k := k)) = F.map k := by
  apply PositiveAdditiveGrothendieck.hom_ext (vfPresentation (C.base : Set M) k)
  intro U
  change vfColimitLift C hc hv F (vfKPlusToSemiring C hc hv (vfClass U)) = _
  rw [vfKPlusToSemiring_class, vfColimitLift_class]
  rfl

theorem vfColimitLift_unique (F : CompatibleVFPositiveMaps C (A := A))
    (f : VFPositiveSemiring C hc hv →+ A)
    (hf : ∀ k, f.comp (vfKPlusToSemiring C hc hv (k := k)) = F.map k) :
    f = vfColimitLift C hc hv F := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨⟨k, U⟩, rfl⟩ := vfSemiringClass_surjective C hc hv a
  rw [vfColimitLift_class]
  have h := congrArg (fun g : VFKPlus (C.base : Set M) k →+ A => g (vfClass U)) (hf k)
  change f (vfKPlusToSemiring C hc hv (vfClass U)) = _ at h
  simpa only [vfKPlusToSemiring_class] using h

def vfPositiveColimitUniversal :
    (VFPositiveSemiring C hc hv →+ A) ≃ CompatibleVFPositiveMaps C (A := A) where
  toFun f := {
    map := fun _ => f.comp (vfKPlusToSemiring C hc hv)
    compatible := by
      intro k l hkl
      rw [AddMonoidHom.comp_assoc, vfKPlusToSemiring_raise] }
  invFun := vfColimitLift C hc hv
  left_inv f := (vfColimitLift_unique C hc hv _ f (fun _ => rfl)).symm
  right_inv F := by
    apply CompatibleVFPositiveMaps.ext
    funext k
    exact vfColimitLift_inclusion C hc hv F k

end DiamondIntegral.Section3
