import «section 3».VFSemiringComparison
import «section 3».VFFiltration

/-! The fixed-degree positive VF quotients inject into the genuine
unbounded positive semiring and exhaust it. -/
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

theorem vfKPlusToSemiring_raise {k l : ℕ} (hkl : k ≤ l) :
    (vfKPlusToSemiring C hc hv).comp (vfRaiseKPlus (M := M) (S := (C.base : Set M)) hkl) =
      (vfKPlusToSemiring C hc hv : VFKPlus (C.base : Set M) k →+ _) := by
  apply PositiveAdditiveGrothendieck.hom_ext (vfPresentation (C.base : Set M) k)
  intro U
  change vfKPlusToSemiring C hc hv (vfRaiseKPlus hkl (vfClass U)) = _
  rw [vfRaiseKPlus_class, vfKPlusToSemiring_class, vfSemiringClass_raise]
  exact (vfKPlusToSemiring_class C hc hv U).symm

theorem vfKPlusToSemiring_injective {k : ℕ} :
    Function.Injective (vfKPlusToSemiring C hc hv (k := k)) := by
  have he : (vfSemiringToFinite C hc hv).toAddMonoidHom.comp (vfKPlusToSemiring C hc hv (k := k)) =
      vfToFiniteKPlus := by
    apply PositiveAdditiveGrothendieck.hom_ext (vfPresentation (C.base : Set M) k)
    intro U
    change vfSemiringToFinite C hc hv (vfKPlusToSemiring C hc hv (vfClass U)) = _
    rw [vfKPlusToSemiring_class, vfSemiringToFinite_class]
    exact (vfToFiniteKPlus_class U).symm
  intro a b h
  apply vfToFiniteKPlus_injective hc C.saturated C.small hv
  have ht := congrArg (vfSemiringToFinite C hc hv) h
  exact congrArg (fun f : VFKPlus (C.base : Set M) k →+ VFFiniteKPlus (C.base : Set M) => f a) he.symm |>.trans
    (ht.trans (congrArg (fun f : VFKPlus (C.base : Set M) k →+ VFFiniteKPlus (C.base : Set M) => f b) he))

include hc hv in
theorem vfRaiseKPlus_injective {k l : ℕ} (hkl : k ≤ l) :
    Function.Injective (vfRaiseKPlus (M := M) (S := (C.base : Set M)) hkl) := by
  intro a b h
  apply vfKPlusToSemiring_injective C hc hv
  have ht := congrArg (vfKPlusToSemiring C hc hv (k := l)) h
  have he := vfKPlusToSemiring_raise C hc hv hkl
  exact congrArg (fun f : VFKPlus (C.base : Set M) k →+ VFPositiveSemiring C hc hv => f a) he.symm |>.trans
    (ht.trans (congrArg (fun f : VFKPlus (C.base : Set M) k →+ VFPositiveSemiring C hc hv => f b) he))

theorem vfSemiringClass_surjective :
    Function.Surjective (fun A : FilteredVFObject (M := M) (C.base : Set M) => vfSemiringClass C hc hv A.2) := by
  intro a
  obtain ⟨U, hU⟩ := vfFiniteClass_surjective (vfSemiringToFinite C hc hv a)
  refine ⟨⟨U.obj.index.1, vfObjectOfCompanionFinite C U⟩, ?_⟩
  apply (vfSemiringEquivFinite C hc hv).injective
  change vfSemiringToFinite C hc hv (vfSemiringClass C hc hv (vfObjectOfCompanionFinite C U)) = _
  rw [vfSemiringToFinite_class]
  exact hU

theorem vfSemiringClass_eq_iff_bijection {k l : ℕ}
    (U : VFObject (M := M) (C.base : Set M) k) (V : VFObject (M := M) (C.base : Set M) l) :
    vfSemiringClass C hc hv U = vfSemiringClass C hc hv V ↔ Nonempty (DefinableBijection U.domain V.domain) := by
  constructor
  · intro h
    have ht := congrArg (vfSemiringToFinite C hc hv) h
    rw [vfSemiringToFinite_class, vfSemiringToFinite_class] at ht
    obtain ⟨e⟩ := vfFiniteClass_eq_iff_iso.mp ht
    exact ⟨vfBijectionOfFiniteIso e⟩
  · rintro ⟨f⟩
    exact vfSemiringClass_bijection C hc hv f

end DiamondIntegral.Section3
