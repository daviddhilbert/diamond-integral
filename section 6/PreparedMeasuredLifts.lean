import «section 6».UnaryMeasuredExistenceFieldBase

/-! A prepared finite-RV-fiber domain with a label-constant Gamma map
is literally the lift of an actual finite, doubly bounded measured RV
object. This adapter works in every arity, conditional on preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n m r s : ℕ} {S : Set M}

def measured_lift_of_prepared
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : A, p.val.2 = q.val.2 → ω p = ω q)
    (hFin : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    MeasuredRVLiftData (G := G) A ω := by
  let U := preparedRVObject A hTag
  have hLift : A = rvLift U := (defSet_eq_of_carrier_eq (preparedRVObject_lift_carrier A hARV hTag)).symm
  let F := changeMapTarget (Map.id A) hLift
  let π := definableSurjectiveDescent (pureRVTagQuotient A) (pureRVTagQuotient_surjective A) ω
    (fun p q he => hSame p q ((pureRVTagQuotient_eq_iff A p q).mp he))
  refine {
    object := U
    finiteVolume := preparedRVObject_finite_volume A hARV hTag hFin
    domainBounded := preparedRVObject_domain_doublyBounded A hTag hA.rvBounded
    valueBounded := preparedRVObject_values_doublyBounded A hTag hD
    rvForm := π
    map := F
    special := SpecialCovariantChain.changeTarget hLift
      (fun p => (changeMapTarget_value (Map.id A) hLift p).symm) (.identity A hA)
    labelMap := pureRVTagQuotient A
    label_eq := ?_
    form_preserves := ?_
  }
  · intro p
    change p.val.2 = (changeMapTarget (Map.id A) hLift p).val.2
    rw [changeMapTarget_value]
    rfl
  · intro p
    exact congrArg Subtype.val (definableSurjectiveDescent_apply _ _ _ _ p)

theorem measured_lift_of_prepared_map_value
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : A, p.val.2 = q.val.2 → ω p = ω q)
    (hFin : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) (p : A) :
    ((measured_lift_of_prepared (G := G) A hA hD hARV hTag ω hSame hFin).map p).val = p.val :=
  changeMapTarget_value (Map.id A) _ p

def MeasuredRVLiftData.precompose
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    {σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (T : MeasuredRVLiftData (G := G) B σ) (f : Map A B) (hf : SpecialCovariantChain (G := G) A B f)
    (hForm : ∀ p : A, (σ (f p)).val = (ω p).val) : MeasuredRVLiftData (G := G) A ω where
  object := T.object
  finiteVolume := T.finiteVolume
  domainBounded := T.domainBounded
  valueBounded := T.valueBounded
  rvForm := T.rvForm
  map := T.map.comp f
  special := .comp hf T.special
  labelMap := T.labelMap.comp f
  label_eq := fun p => T.label_eq (f p)
  form_preserves := fun p => (T.form_preserves (f p)).trans (hForm p)

end DiamondIntegral.Section6
