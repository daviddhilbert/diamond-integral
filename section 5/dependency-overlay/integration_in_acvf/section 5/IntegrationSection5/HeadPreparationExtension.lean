import IntegrationSection5.HeadPreparation
import IntegrationSection5.RelativeSpecialExtension

/-! Changing an internal real presentation preserves the actual preparation
and its contracted carrier. No smallness of either presentation is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S R : Set M} {n m l : ℕ}

theorem specialRelative_extendBase {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (f : Map A B) (hSR : S ⊆ R) {i : Fin n} (hf : SpecialRelative f i) :
    SpecialRelative (extendPointMap f hSR) i := by
  obtain ⟨hi,hT⟩ := hf
  have hiR : UnaryRelative (extendPointMap f hSR) i := fun a j hj => hi ⟨a.val,a.property⟩ j hj
  refine ⟨hiR,?_⟩
  intro u
  obtain ⟨T,hT⟩ := hT u
  let hAug : coordinateFibreBase S i u ⊆ coordinateFibreBase R i u :=
    Set.union_subset_union hSR (Set.Subset.refl _)
  refine ⟨T.extendBase hAug,?_⟩
  intro p
  apply Subtype.ext
  have hval := T.chain.extendBase_apply hAug p
  have he := congrArg (fun q : coordinateFibre B i u => q.val) (hT ⟨p.val,p.property⟩)
  exact hval.trans he

def HeadPreparation.extendBase {A : DefSet (M := M) S (n+1) m}
    (T : HeadPreparation A) (hSR : S ⊆ R) : HeadPreparation (SpecialTransformations.Section5.extendBase A hSR) where
  arity := T.arity
  target := SpecialTransformations.Section5.extendBase T.target hSR
  map := extendPointMap T.map hSR
  special := specialRelative_extendBase T.map hSR T.special
  saturated := T.saturated

theorem HeadPreparation.extendBase_contractedSet {A : DefSet (M := M) S (n+1) m}
    (T : HeadPreparation A) (hSR : S ⊆ R) :
    carrier (T.extendBase hSR).contractedSet = carrier T.contractedSet := by
  ext p
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,a.property⟩,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨⟨a.val,a.property⟩,ha⟩

def HeadPreparation.castSource {A A' : DefSet (M := M) S (n+1) m}
    (T : HeadPreparation A) (hA : A = A') : HeadPreparation A' := by
  cases hA
  exact T

end IntegrationInACVF.Section5
