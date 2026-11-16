import «section 6».OriginalBaseOrdinaryFocus
import «section 6».PureRVDiscQuotients

/-! Ordinary focus loci pull back to whole current RV-label fibres.
The current source may have any additional retained labels and need
not be an old-or-empty fibre refinement of the ordinary ambient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}

structure OrdinaryUnaryFocusFrame
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) R 1 r)
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A)) (q : ℕ) where
  source : DefSet (rawMixedSpace (M := M) 1 q) S
  oldMap : Map source (originalBaseOrdinarySet hc A hA)
  labels : Fin r → Fin q
  point : ∀ p : source,(oldMap p).val=(p.val.1,p.val.2 ∘ labels)
  proper : ProperInvariant S source.carrier
  doublyBounded : VFDoublyBounded source.carrier
  tagged : ∀ p ∈ source.carrier,∀ z ∈ source.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1

namespace OrdinaryUnaryFocusFrame
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q) {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)

def active : DefSet (rawMixedSpace (M := M) 1 q) S :=
  ⟨{z | ∃ p : X.source,p.val=z ∧ (X.oldMap p).val ∈ D.locus},
    X.oldMap.definable_preimage (ordinary_named_gamma_set_definable hc D.locus hD.1)⟩

def activeTags : DefSet (rawRVSpace (M := M) q) S := pureRVTagDomain (X.active D hD)

theorem activeTags_at (p : X.source) : p.val.2 ∈ (X.activeTags D hD).carrier ↔ (X.oldMap p).val ∈ D.locus := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb,hLocus⟩ := a.property
    change a.val.2=p.val.2 at ha
    have hTags : b.val.2=p.val.2 := (congrArg Prod.snd hb).trans ha
    have hVF : tupleRV M (X.oldMap b).val.1=tupleRV M (X.oldMap p).val.1 := by
      rw [X.point b,X.point p]
      exact X.tagged b.val b.property p.val p.property hTags
    have hRV : (X.oldMap b).val.2=(X.oldMap p).val.2 := by
      rw [X.point b,X.point p,hTags]
    exact rvPullback_mem_of_sameRV ((ordinary_pullback_iff D.locus).mp D.locus_pullback) hLocus hVF hRV
  · intro hp
    exact ⟨⟨p.val,p,rfl,hp⟩,rfl⟩

def oldActiveMap : Map (focusActive X.source (X.activeTags D hD))
    (OriginalBaseOrdinaryFocus.active D hc hA hD) where
  toFun p := ⟨(X.oldMap ⟨p.val,p.property.1⟩).val,
    (X.oldMap ⟨p.val,p.property.1⟩).property,
    (X.activeTags_at D hD ⟨p.val,p.property.1⟩).mp p.property.2⟩
  graph_definable := (X.oldMap.restrict
    (show (focusActive X.source (X.activeTags D hD)).carrier ⊆ X.source.carrier from fun _ hp => hp.1)).graph_definable

def scalarMap : Map (focusActive X.source (X.activeTags D hD)) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (OriginalBaseOrdinaryFocus.scalarMap D hc hA hD).comp (X.oldActiveMap D hD)

theorem scalarMap_value (p : focusActive X.source (X.activeTags D hD)) :
    (X.scalarMap D hD p).val 0=D.center (X.oldMap ⟨p.val,p.property.1⟩).val := rfl

theorem scalarMap_same_labels (p z : focusActive X.source (X.activeTags D hD)) (hpz : p.val.2=z.val.2) :
    (X.scalarMap D hD p).val 0=(X.scalarMap D hD z).val 0 := by
  apply OriginalBaseOrdinaryFocus.center_same_labels D
    (X.oldMap ⟨p.val,p.property.1⟩).val (X.oldMap ⟨z.val,z.property.1⟩).val
    (X.oldActiveMap D hD p).property (X.oldActiveMap D hD z).property
  rw [X.point,X.point]
  exact congrArg (fun u : Fin q → RVInfinity M => u ∘ X.labels) hpz

end OrdinaryUnaryFocusFrame
end DiamondIntegral.Section6
