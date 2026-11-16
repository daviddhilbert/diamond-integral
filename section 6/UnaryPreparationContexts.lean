import «section 6».PairedRVFocusComponents

/-! A unary base preparation inside an arbitrary VF ambient space.
The actual original-base projection, retained old labels and all
ambient geometry are explicit; no cylinder assumption is made on the
proper full-dimensional pieces that will be protected. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m : ℕ}

structure UnaryPreparationContext (A : DefSet (rawMixedSpace (M := M) 1 r) S) (i : Fin m) where
  arity : ℕ
  source : DefSet (rawMixedSpace (M := M) m arity) S
  labels : Fin r → Fin arity
  projection : Map source A
  projection_value : ∀ p : source,(projection p).val=(fun _ : Fin 1 => p.val.1 i,p.val.2 ∘ labels)
  proper : ProperInvariant S source.carrier
  doublyBounded : VFDoublyBounded source.carrier
  pullback : IsRVPullback source.carrier
  tagged : ∀ p ∈ source.carrier,∀ q ∈ source.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1

def UnaryPreparationContext.focusProjection
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {i : Fin m}
    (X : UnaryPreparationContext A i) (U : DefSet (rawRVSpace (M := M) r) S) :
    Map (focusActive X.source (selectedRVTagSet U X.labels)) (focusActive A U) := by
  let q : Map (focusActive X.source (selectedRVTagSet U X.labels)) A :=
    X.projection.comp (Map.inclusion (fun _ hp => hp.1))
  refine q.corestrict (fun p => ⟨(q p).property,?_⟩)
  change (X.projection ⟨p.val,p.property.1⟩).val.2 ∈ U.carrier
  rw [X.projection_value]
  exact p.property.2

def UnaryPreparationContext.focusData
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {i : Fin m}
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A) : RVFocusData X.source where
  coordinate := i
  activeTags := selectedRVTagSet D.activeTags X.labels
  focus u := D.focus (u ∘ X.labels)
  focusMap := D.focusMap.comp (X.focusProjection D.activeTags)
  focusMap_eq p := by
    change (D.focusMap (X.focusProjection D.activeTags p)).val 0=_
    rw [D.focusMap_eq]
    apply congrArg D.focus
    change (X.projection ⟨p.val,p.property.1⟩).val.2=p.val.2 ∘ X.labels
    exact congrArg Prod.snd (X.projection_value ⟨p.val,p.property.1⟩)
  sourceProper := X.proper
  sourceDoublyBounded := X.doublyBounded
  tagged := X.tagged
  focusRV p hp hu := by
    let q : X.source := ⟨p,hp⟩
    have hu' : (X.projection q).val.2 ∈ D.activeTags.carrier := by
      rw [X.projection_value]
      exact hu
    have h := D.focusRV (X.projection q).val (X.projection q).property hu'
    rw [X.projection_value] at h
    exact h

theorem UnaryPreparationContext.focusImage_subset
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {i : Fin m}
    (X : UnaryPreparationContext A i) (D : UnaryFocusData A) :
    scalarFocusImage (X.focusData D).focusMap ⊆ scalarFocusImage D.focusMap := by
  rintro _ ⟨p,rfl⟩
  exact ⟨X.focusProjection D.activeTags p,rfl⟩

end DiamondIntegral.Section6
