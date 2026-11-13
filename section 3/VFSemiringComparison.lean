import «section 3».VFFiniteDomainClasses

/-! The filtered VF positive semiring is exactly the positive scissors
of all actual finite-RV-fibre mixed domains. -/
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
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def vfObjectOfCompanionFinite (U : VFFiniteAllObject (M := M) (C.base : Set M)) :
    VFObject (C.base : Set M) U.obj.index.1 := vfObjectOfFiniteFibres U.obj.set U.property

def vfSemiringToFiniteInvariant : PositiveGrothendieck.Invariant
    (vfSemiringPresentation C hc hv) (R := VFFiniteKPlus (M := M) (C.base : Set M)) where
  toFun A := vfFiniteClass A.2.toCompanionFinite
  iso := fun h => by obtain ⟨f⟩ := h; exact vfFiniteClass_iso (vfCompanionFiniteIso f)
  empty := vfFiniteClass_empty
  unit := rfl
  product A B := (vfFiniteClass_mul A.2.toCompanionFinite B.2.toCompanionFinite).symm
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      have hh : vfClass a + vfClass b = vfClass d + vfClass e :=
        positiveClass_scissor (vfPresentation (C.base : Set M) k) hs
      have ht := congrArg vfToFiniteKPlus hh
      simpa only [map_add, vfToFiniteKPlus_class] using ht
    · obtain ⟨k, rfl, rfl, rfl, rfl⟩ := h
      change vfFiniteClass (vfFiniteAllEmpty (M := M) (C.base : Set M)) + vfFiniteClass (vfFiniteAllEmpty (C.base : Set M)) =
        vfFiniteClass (vfFiniteAllEmpty (C.base : Set M)) + vfFiniteClass (vfFiniteAllEmpty (C.base : Set M))
      simp only [vfFiniteClass_empty, add_zero]

def vfSemiringToFinite : VFPositiveSemiring C hc hv →+* VFFiniteKPlus (M := M) (C.base : Set M) :=
  PositiveGrothendieck.lift (vfSemiringPresentation C hc hv) (vfSemiringToFiniteInvariant C hc hv)

@[simp] theorem vfSemiringToFinite_class {k : ℕ} (U : VFObject (M := M) (C.base : Set M) k) :
    vfSemiringToFinite C hc hv (vfSemiringClass C hc hv U) = vfFiniteClass U.toCompanionFinite :=
  PositiveGrothendieck.lift_of (vfSemiringPresentation C hc hv) (vfSemiringToFiniteInvariant C hc hv) ⟨k, U⟩

def vfFiniteToSemiringInvariant : PositiveAdditiveGrothendieck.Invariant
    (vfFiniteScissorPresentation (M := M) (C.base : Set M)) (A := VFPositiveSemiring C hc hv) where
  toFun U := vfSemiringClass C hc hv (vfObjectOfCompanionFinite C U)
  iso := by
    intro U V h
    obtain ⟨e⟩ := h
    exact vfSemiringClass_bijection C hc hv
      ⟨e.hom.hom, DefinableSetCat.bijective_of_iso ((vfFiniteProperty (C.base : Set M)).ι.mapIso e)⟩
  empty := vfSemiringClass_empty C hc hv
  scissor := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨D, hD⟩ ⟨E, hE⟩ h
    change VFAllScissor A B D E at h
    obtain ⟨i, X, Y, hA', hB', hD', hE'⟩ := h
    subst A
    subst B
    subst D
    subst E
    have h := vfFiniteDomainClass_union_inter C hc hv X Y hA hB
    exact h

def vfFiniteToSemiringAdd : VFFiniteKPlus (M := M) (C.base : Set M) →+ VFPositiveSemiring C hc hv :=
  PositiveAdditiveGrothendieck.lift (vfFiniteScissorPresentation (C.base : Set M)) (vfFiniteToSemiringInvariant C hc hv)

@[simp] theorem vfFiniteToSemiringAdd_class (U : VFFiniteAllObject (M := M) (C.base : Set M)) :
    vfFiniteToSemiringAdd C hc hv (vfFiniteClass U) = vfSemiringClass C hc hv (vfObjectOfCompanionFinite C U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem vfFiniteToSemiringAdd_one : vfFiniteToSemiringAdd C hc hv (1 : VFFiniteKPlus (M := M) (C.base : Set M)) = 1 := by
  change vfFiniteToSemiringAdd C hc hv (vfFiniteClass (vfFiniteUnitObject _)) = _
  rw [vfFiniteToSemiringAdd_class]
  exact vfSemiringClass_unit C hc hv

theorem vfFiniteToSemiringAdd_mul (a b : VFFiniteKPlus (M := M) (C.base : Set M)) :
    vfFiniteToSemiringAdd C hc hv (a * b) = vfFiniteToSemiringAdd C hc hv a * vfFiniteToSemiringAdd C hc hv b := by
  obtain ⟨U, rfl⟩ := vfFiniteClass_surjective a
  obtain ⟨V, rfl⟩ := vfFiniteClass_surjective b
  rw [vfFiniteClass_mul, vfFiniteToSemiringAdd_class, vfFiniteToSemiringAdd_class, vfFiniteToSemiringAdd_class]
  exact vfSemiringClass_product C hc hv (vfObjectOfCompanionFinite C U) (vfObjectOfCompanionFinite C V)

def vfFiniteToSemiring : VFFiniteKPlus (M := M) (C.base : Set M) →+* VFPositiveSemiring C hc hv where
  __ := vfFiniteToSemiringAdd C hc hv
  map_one' := vfFiniteToSemiringAdd_one C hc hv
  map_mul' := vfFiniteToSemiringAdd_mul C hc hv

@[simp] theorem vfFiniteToSemiring_class (U : VFFiniteAllObject (M := M) (C.base : Set M)) :
    vfFiniteToSemiring C hc hv (vfFiniteClass U) = vfSemiringClass C hc hv (vfObjectOfCompanionFinite C U) :=
  vfFiniteToSemiringAdd_class C hc hv U

def vfSemiringEquivFinite : VFPositiveSemiring C hc hv ≃+* VFFiniteKPlus (M := M) (C.base : Set M) := by
  let F := vfSemiringToFinite C hc hv
  let B := vfFiniteToSemiring C hc hv
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (vfSemiringPresentation C hc hv)
    rintro ⟨k, U⟩
    change B (F (vfSemiringClass C hc hv U)) = vfSemiringClass C hc hv U
    rw [vfSemiringToFinite_class, vfFiniteToSemiring_class]
    exact vfSemiringClass_bijection C hc hv (DefinableBijection.id U.domain)
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    obtain ⟨U, rfl⟩ := vfFiniteClass_surjective a
    change F (B (vfFiniteClass U)) = vfFiniteClass U
    rw [vfFiniteToSemiring_class, vfSemiringToFinite_class]
    rfl
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
