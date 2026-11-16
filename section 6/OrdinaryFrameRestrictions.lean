import «section 6».OrdinaryChainCovariantRealization
import «section 6».UnaryOffsetCoreComplements

/-! Restrict an actual ordinary focus frame to a proper current subset.
In particular the constructed offset-core complement retains the entire
old point map and every old RV selector. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q)

def restrict (H : DefSet (rawMixedSpace (M := M) 1 q) S)
    (hH : H.carrier ⊆ X.source.carrier) (hProper : ProperInvariant S H.carrier) :
    OrdinaryUnaryFocusFrame hc A hA q where
  source := H
  oldMap := X.oldMap.restrict hH
  labels := X.labels
  point p := X.point ⟨p.val,hH p.property⟩
  proper := hProper
  doublyBounded := by
    obtain ⟨γ,hγ⟩ := X.doublyBounded
    exact ⟨γ,fun p hp => hγ p (hH hp)⟩
  tagged p hp z hz := X.tagged p (hH hp) z (hH hz)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def outsideOffsetCoreFrame
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : UnaryFocusData X.source)
    (dMap : Map (focusActive X.source F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (d : (Fin q → RVInfinity M) → VF M)
    (hdMap : ∀ p : focusActive X.source F.activeTags,(dMap p).val 0=d p.val.2)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0) : OrdinaryUnaryFocusFrame hc A hA q :=
  X.restrict (F.offsetCoreComplement dMap) (F.offsetCoreComplement_subset dMap)
    (F.offsetCoreComplement_proper dMap d hdMap h00 hc hκ hs hv hd)

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
