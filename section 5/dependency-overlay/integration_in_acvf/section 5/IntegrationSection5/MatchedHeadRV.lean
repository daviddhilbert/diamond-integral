import IntegrationSection5.MatchedHeadCompletion
import IntegrationSection5.UnaryHeadRVPresentation

/-! Compare the genuine two-stage contraction objects. Constant first
volume labels reduce the RV[2] obligations to the constructed RV[1] iso. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 2 m} {B : DefSet (M := M) R 2 l}
variable {T : HeadPreparation A} {U : HeadPreparation B}

namespace MatchedHeadCompletion

def objectA (Q : MatchedHeadCompletion (G := G) T U) :=
  selectedVolumeObject (Map.image (rawLabelMap (headImage Q.targetA))) Q.programA.volumeIndex

def objectB (Q : MatchedHeadCompletion (G := G) T U) :=
  selectedVolumeObject (Map.image (rawLabelMap (headImage Q.targetB))) Q.programB.volumeIndex

theorem volumeIndexA_zero (Q : MatchedHeadCompletion (G := G) T U) :
    Q.programA.volumeIndex 0 = Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le Q.tailA.chain) 0) := by
  apply Fin.ext
  change (1+Q.arityA)-(1+T.arity)+0 = 1+(Q.arityA-(1+T.arity)+0)
  have hle := special_chain_rvArity_le Q.tailA.chain
  change 1+T.arity ≤ Q.arityA at hle
  omega

theorem volumeIndexA_one (Q : MatchedHeadCompletion (G := G) T U) :
    Q.programA.volumeIndex 1 = 0 := by
  apply Fin.ext
  change (1+Q.arityA)-(1+Q.arityA)+0 = 0
  omega

theorem volumeIndexB_zero (Q : MatchedHeadCompletion (G := G) T U) :
    Q.programB.volumeIndex 0 = Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le Q.tailB.chain) 0) := by
  apply Fin.ext
  change (1+Q.arityB)-(1+U.arity)+0 = 1+(Q.arityB-(1+U.arity)+0)
  have hle := special_chain_rvArity_le Q.tailB.chain
  change 1+U.arity ≤ Q.arityB at hle
  omega

theorem volumeIndexB_one (Q : MatchedHeadCompletion (G := G) T U) :
    Q.programB.volumeIndex 1 = 0 := by
  apply Fin.ext
  change (1+Q.arityB)-(1+Q.arityB)+0 = 0
  omega

def rvIso (Q : MatchedHeadCompletion (G := G) T U)
    (r t : RV (M := M)) (hrt : r.val = iRVZero ↔ t.val = iRVZero)
    (hr : ∀ a : T.contractedSet, a.val.2 0 = r)
    (ht : ∀ b : U.contractedSet, b.val.2 0 = t) : Q.objectA ≅ Q.objectB := by
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
  let e := @rvUnaryProfileIso M (@CanonicalStructure.normalize M sM) Q.codes
    (pullbackObject Q.targetA) (pullbackObject Q.targetB) Q.iso u v r t hrt hu hv
  exact (unaryHeadVolumeIso Q.targetA Q.programA.volumeIndex).trans
    (e.trans (unaryHeadVolumeIso Q.targetB Q.programB.volumeIndex).symm)

end MatchedHeadCompletion
end IntegrationInACVF.Section5
