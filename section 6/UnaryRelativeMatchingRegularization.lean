import «section 6».UnaryRelativePreparedMatching

/-! Add the literal leading RV coordinate to an actual auxiliary unary
matching. This is a permitted regularization on both sides; its global
conjugate still maps whole label fibres bijectively. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem regularization_tags_iff {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) (p q : A) :
    (regularization A p).val.2=(regularization A q).val.2 ↔ p.val.2=q.val.2 := by
  constructor
  · intro h
    change Fin.append (tupleRV M p.val.1) p.val.2=Fin.append (tupleRV M q.val.1) q.val.2 at h
    funext i
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd 1 i)
  · intro h
    change Fin.append (tupleRV M p.val.1) p.val.2=Fin.append (tupleRV M q.val.1) q.val.2
    rw [hTag p.val p.property q.val q.property h,h]

namespace UnaryRelativePreparedMatching
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} (H : UnaryRelativePreparedMatching (G := G) A B f)
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

def regularized : UnaryRelativePreparedMatching (G := G) A B f := by
  let α := regularization H.source
  let β := regularization H.target
  have hα := regularization_bijective H.source
  have hβ := regularization_bijective H.target
  have hInv : Function.Bijective (α.inverse hα) := by
    constructor
    · intro p q he
      have h := congrArg α he
      simpa only [Map.apply_inverse] using h
    · intro p
      exact ⟨α p,Map.inverse_apply α hα p⟩
  refine {
    sourceArity := 1+H.sourceArity
    targetArity := 1+H.targetArity
    source := (regularizeMap H.source).image
    target := (regularizeMap H.target).image
    sourceMap := α.comp H.sourceMap
    targetMap := β.comp H.targetMap
    sourceChain := .comp H.sourceChain (.original (.regularize H.source H.sourceProper H.sourceBounded))
    targetChain := .comp H.targetChain (.original (.regularize H.target H.targetProper H.targetBounded))
    sourceProper := regularization_properInvariant h00 hc hκ hs hv H.source H.sourceProper H.sourceBounded
    targetProper := regularization_properInvariant h00 hc hκ hs hv H.target H.targetProper H.targetBounded
    sourceBounded := regularized_vfDoublyBounded H.sourceBounded
    targetBounded := regularized_vfDoublyBounded H.targetBounded
    sourcePullback := regularization_rvPullback H.source H.sourcePullback
    targetPullback := regularization_rvPullback H.target H.targetPullback
    sourceTagged := ?_
    targetTagged := ?_
    map := β.comp (H.map.comp (α.inverse hα))
    bijective := hβ.comp (H.bijective.comp hInv)
    commutes := ?_
    wholeFibres := H.wholeFibres.conjugate H.map H.bijective α hα β hβ
      (regularization_tags_iff H.sourceTagged) (regularization_tags_iff H.targetTagged) }
  · rw [regularization_carrier]
    exact regularized_tagged _
  · rw [regularization_carrier]
    exact regularized_tagged _
  · intro a
    change β (H.map (α.inverse hα (α (H.sourceMap a))))=β (H.targetMap (f a))
    rw [Map.inverse_apply,H.commutes a]

theorem regularized_source_leading (p : Mixed M 1 (1+H.sourceArity))
    (hp : p ∈ (H.regularized h00 hc hκ hs hv).source.carrier) :
    rv M (p.1 0)=p.2 (Fin.castAdd H.sourceArity (0 : Fin 1)) := by
  change p ∈ (regularizeMap H.source).image.carrier at hp
  rw [regularization_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  rfl

theorem regularized_target_leading (p : Mixed M 1 (1+H.targetArity))
    (hp : p ∈ (H.regularized h00 hc hκ hs hv).target.carrier) :
    rv M (p.1 0)=p.2 (Fin.castAdd H.targetArity (0 : Fin 1)) := by
  change p ∈ (regularizeMap H.target).image.carrier at hp
  rw [regularization_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  rfl

end UnaryRelativePreparedMatching
end DiamondIntegral.Section6
