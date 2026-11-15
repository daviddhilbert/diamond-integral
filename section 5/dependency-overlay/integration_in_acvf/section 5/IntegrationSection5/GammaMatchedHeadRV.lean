import IntegrationSection5.MatchedHeadRV
import IntegrationSection5.GammaRVPresentations

/-! The RV[2] comparison from matched unary tails retains full
original-Gamma graphs, including the two constant volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 2 m} {B : DefSet (M := M) R 2 l}
variable {T : HeadPreparation A} {U : HeadPreparation B}

def MatchedHeadCompletion.gammaRVIso (Q : MatchedHeadCompletion (G := G) T U)
    (r t : RV (M := M)) (hrt : r.val = iRVZero ↔ t.val = iRVZero)
    (hr : ∀ a : T.contractedSet, a.val.2 0 = r)
    (ht : ∀ b : U.contractedSet, b.val.2 0 = t) : GammaRVIso G Q.objectA Q.objectB := by
  let u := rawRVProjectionMap Q.programA.volumeIndex (Map.image (rawKeyMap Q.targetA))
  let v := rawRVProjectionMap Q.programB.volumeIndex (Map.image (rawKeyMap Q.targetB))
  have hr' : ∀ a : (T.extendBase Q.containsA).contractedSet, a.val.2 0 = r := by
    intro a
    exact hr ⟨a.val,(Set.ext_iff.mp (T.extendBase_contractedSet Q.containsA) a.val).mp a.property⟩
  have ht' : ∀ b : (U.extendBase Q.containsB).contractedSet, b.val.2 0 = t := by
    intro b
    exact ht ⟨b.val,(Set.ext_iff.mp (U.extendBase_contractedSet Q.containsB) b.val).mp b.property⟩
  have hu : ∀ a, (u a).val = ![r,(rvObjectVolume (pullbackObject Q.targetA) a).val 0] :=
    unary_profile_projection Q.targetA _ r
      (special_target_constant_label Q.tailA 0 r hr') _ Q.volumeIndexA_zero Q.volumeIndexA_one
  have hv : ∀ b, (v b).val = ![t,(rvObjectVolume (pullbackObject Q.targetB) b).val 0] :=
    unary_profile_projection Q.targetB _ t
      (special_target_constant_label Q.tailB 0 t ht') _ Q.volumeIndexB_zero Q.volumeIndexB_one
  let e : GammaRVIso G (pullbackObject Q.targetA) (pullbackObject Q.targetB) :=
    ⟨Q.iso,Q.hom_graph,Q.inv_graph⟩
  exact (gammaUnaryHeadVolumeIso Q.targetA Q.targetA_gamma Q.programA.volumeIndex).trans
    ((gammaUnaryProfileIso e u v r t hrt hu hv).trans
      (gammaUnaryHeadVolumeIso Q.targetB Q.targetB_gamma Q.programB.volumeIndex).symm)

end IntegrationInACVF.Section5
