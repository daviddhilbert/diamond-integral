import «section 3».MeasuredRVMapUnions
import «section 3».MeasuredRVRepresentatives
import «section 3».CarrierBijections
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.TypeTags.Basic

/-! The measured positive quotient identifies exactly the genuinely
pointwise weight-preserving definable bijections, before group completion. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

instance measuredRVMapMonoidal : MonoidalCategory (MeasuredRVMapObject hc S k) := monoidalOfHasFiniteCoproducts _
instance measuredRVMapSymmetric : SymmetricCategory (MeasuredRVMapObject hc S k) := symmetricOfHasFiniteCoproducts _

abbrev MeasuredRVIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  Additive (Skeleton (MeasuredRVMapObject hc S k))

def measuredRVIsoClass (hc : CanonicalStructure.IsCanonical (M := M)) (U : MeasuredRVObject (M := M) S k) :
    MeasuredRVIsoClasses hc S k := Additive.ofMul (toSkeleton (⟨U⟩ : MeasuredRVMapObject hc S k))

theorem measuredRVIsoClass_eq_iff {U V : MeasuredRVObject (M := M) S k} :
    measuredRVIsoClass hc U = measuredRVIsoClass hc V ↔ Nonempty (U ≅ V) :=
  toSkeleton_eq_toSkeleton_iff.trans measuredRVMapIso_iff

@[simp] theorem measuredRVIsoClass_empty : measuredRVIsoClass hc (MeasuredRVObject.empty (M := M) S k) = 0 := by
  change toSkeleton (MeasuredRVMapObject.empty hc S k) = (1 : Skeleton (MeasuredRVMapObject hc S k))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (measuredRVMapEmptyIsInitial.uniqueUpToIso initialIsInitial)

theorem measuredRVIsoClass_coprod (U V : MeasuredRVObject (M := M) S k) :
    measuredRVIsoClass hc (U.coprod hc V) = measuredRVIsoClass hc U + measuredRVIsoClass hc V := by
  let A : MeasuredRVMapObject hc S k := ⟨U⟩
  let B : MeasuredRVMapObject hc S k := ⟨V⟩
  change toSkeleton (A.coprod B) = toSkeleton A * toSkeleton B
  calc
    _ = toSkeleton (A ⨿ B) := congr_toSkeleton_of_iso
      (colimit.isoColimitCocone
        { cocone := BinaryCofan.mk (measuredRVMapInl A B) (measuredRVMapInr A B)
          isColimit := measuredRVMapCoprodIsColimit A B }).symm
    _ = _ := Skeleton.toSkeleton_tensorObj A B

def measuredRVRestrictionIsoOfCarrierEq (U : MeasuredRVObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.underlying.arity) S) (hX : X.carrier ⊆ U.underlying.domain.carrier)
    (he : X.carrier = U.underlying.domain.carrier) : MeasuredRVHom (U.restrict hc X hX) U :=
  ⟨DefinableBijection.ofCarrierEq he, fun _ => rfl⟩

theorem measuredRVIsoClass_scissor {A B D E : MeasuredRVObject (M := M) S k}
    (h : MeasuredRVScissor hc A B D E) :
    measuredRVIsoClass hc A + measuredRVIsoClass hc B = measuredRVIsoClass hc D + measuredRVIsoClass hc E := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  let Y := U.underlying.difference X
  have hY : Y.carrier ⊆ U.underlying.domain.carrier := fun _ h => h.1
  have hd : Disjoint X.carrier Y.carrier := Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  let W : MeasuredRVMapObject hc S k := ⟨U⟩
  have he : (X.union Y).carrier = U.underlying.domain.carrier := by
    ext t
    constructor
    · rintro (hx | hy)
      · exact hX hx
      · exact hy.1
    · intro ht
      by_cases hx : t ∈ X.carrier
      · exact Or.inl hx
      · exact Or.inr ⟨ht, hx⟩
  have e : (W.restrict X hX).coprod (W.restrict Y hY) ≅ W :=
    (measuredRVCoprodUnionIso W X Y hX hY hd).trans
      (measuredRVMapIsoOfHom (U := W.restrict (X.union Y) (measuredRVUnionSubset W X Y hX hY)) (V := W)
        (measuredRVRestrictionIsoOfCarrierEq U (X.union Y) (measuredRVUnionSubset W X Y hX hY) he))
  change measuredRVIsoClass hc (U.restrict hc X hX) + measuredRVIsoClass hc (U.restrict hc Y hY) =
    measuredRVIsoClass hc U + measuredRVIsoClass hc (MeasuredRVObject.empty S k)
  rw [measuredRVIsoClass_empty, add_zero, ← measuredRVIsoClass_coprod]
  exact measuredRVIsoClass_eq_iff.mpr (measuredRVMapIso_iff.mp ⟨e⟩)

def measuredRVKPlusToIsoClasses : MeasuredRVKPlus hc S k →+ MeasuredRVIsoClasses hc S k :=
  PositiveAdditiveGrothendieck.lift (measuredRVPresentation hc S k) {
    toFun := measuredRVIsoClass hc
    iso := measuredRVIsoClass_eq_iff.mpr
    empty := measuredRVIsoClass_empty
    scissor := measuredRVIsoClass_scissor }

@[simp] theorem measuredRVKPlusToIsoClasses_class (U : MeasuredRVObject (M := M) S k) :
    measuredRVKPlusToIsoClasses (measuredRVClass hc U) = measuredRVIsoClass hc U := PositiveAdditiveGrothendieck.lift_of _ _ U

theorem measuredRVClass_eq_iff_iso {U V : MeasuredRVObject (M := M) S k} :
    measuredRVClass hc U = measuredRVClass hc V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    apply measuredRVIsoClass_eq_iff.mp
    simpa only [measuredRVKPlusToIsoClasses_class] using congrArg measuredRVKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact measuredRVClass_iso hc e

end DiamondIntegral.Section3
