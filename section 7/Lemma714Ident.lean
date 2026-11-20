import «section 7».Lemma714Compare
import «section 6».NormalizedMeasuredHeadStarts

/-! Lemma 7.14, part 17: standard contractions as head-start chain sets.

For a unary normalized measured contraction `F` of `(A, ω)` and head-start
labels `π`, the target of `F` with labels `F.oldIndex ∘ π` and form `F.form` is
a head-start chain set (`targetHGood`). Its head-start class is the class of
Section 6's head-start object `F.headStartMeasuredObject k π`
(`cls_headStart_eq_clsH`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  {T : LRV.Substructure M} (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  {r k : ℕ} {A : DefSet (rawMixedSpace (M := M) (0 + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (0 + 1))}

include hc h00 hκ hs hv hsmall hΓ in
/-- The target of a unary standard contraction, with the carried head-start
labels, is a head-start chain set. -/
def targetHGood (F : NormalizedMeasuredContraction (G := G) A ω e) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (0 + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    HGood (X := F.target) (F.oldIndex ∘ π) where
  pullback := F.preparedContraction.lift.originalTarget_pullback
  finite := unbundle_finite (head_start_finite_rv_fibres_of_bijective hc h00 hκ.le hs hsmall F.map
    (F.homeomorphism h00 hc lin hκ hs hv hsmall hΓ).bijective k π (F.oldIndex ∘ π)
    (fun p i => F.retained p (π i)) hFin)
  vfBounded := F.preparedContraction.lift.originalTarget_doublyBounded
  rvBounded := F.preparedContraction.lift.originalTarget_proper.rvBounded
  form := F.form
  form_labels := F.form_same_tags

/-- **The head-start object of a unary standard contraction has the head-start
class of its target.** -/
theorem cls_headStart_eq_clsH (F : NormalizedMeasuredContraction (G := G) A ω e) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (0 + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    cls (objOf hc T (F.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π hFin)
        (F.headStartObject_doublyBounded k π)) =
      clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F π hFin) := by
  rw [clsH_eq_hsObj hc _ F.target_tagged]
  apply cls_objOf_eq hc
  exact MeasuredRVIso.identity _

end DiamondIntegral.Section7.Lemma714Head
