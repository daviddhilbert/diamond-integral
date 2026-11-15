import IntegrationSection5.FinalBranchCuts
import IntegrationSection5.GammaRVPartition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def leftNRawDomain (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) := Map.image (rawKeyMap (Q.leftNFinalImage N))
def leftRRawDomain (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) := Map.image (rawKeyMap (Q.leftRFinalImage N))
def leftWholeRawDomain (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) := Map.image (rawKeyMap (Q.leftTail N).target)
def leftWholeProfile (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  selectedVolumeObject (Q.leftWholeRawDomain N) (Q.leftProgram N).volumeIndex

theorem leftNRaw_cut (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (Q.leftNRawDomain N) = {q | q ∈ carrier (Q.leftWholeRawDomain N) ∧
      q ∘ (Fin.natAdd 1 ∘ Q.leftFinalCodeProjection N) ∈ oldNLabels (T := T)} :=
  rawKeyImage_rvSlice (Q.leftFinalCodeProjection N) (oldNLabels (T := T)) (Q.leftNFinal_slice N)

theorem leftRRaw_cut (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (Q.leftRRawDomain N) = {q | q ∈ carrier (Q.leftWholeRawDomain N) ∧
      q ∘ (Fin.natAdd 1 ∘ Q.leftFinalCodeProjection N) ∉ oldNLabels (T := T)} :=
  rawKeyImage_rvSlice (Q.leftFinalCodeProjection N) (oldNLabels (T := T))ᶜ (Q.leftRFinal_slice N)

theorem leftNRaw_sub (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (Q.leftNRawDomain N) ⊆ carrier (Q.leftWholeRawDomain N) :=
  fun q hq => ((Set.ext_iff.mp (Q.leftNRaw_cut N) q).mp hq).1

theorem leftRRaw_sub (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (Q.leftRRawDomain N) ⊆ carrier (Q.leftWholeRawDomain N) :=
  fun q hq => ((Set.ext_iff.mp (Q.leftRRaw_cut N) q).mp hq).1

theorem leftRaw_disjoint (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    Disjoint (carrier (Q.leftNRawDomain N)) (carrier (Q.leftRRawDomain N)) := by
  apply Set.disjoint_left.mpr
  intro q hn hr
  exact ((Set.ext_iff.mp (Q.leftRRaw_cut N) q).mp hr).2 (((Set.ext_iff.mp (Q.leftNRaw_cut N) q).mp hn).2)

theorem leftRaw_cover (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (normalizedRVUnionSet (Q.leftNRawDomain N) (Q.leftRRawDomain N)) = carrier (Q.leftWholeRawDomain N) := by
  ext q
  change (q ∈ carrier (Q.leftNRawDomain N) ∨ q ∈ carrier (Q.leftRRawDomain N)) ↔ _
  rw [Q.leftNRaw_cut N,Q.leftRRaw_cut N]
  change ((_ ∧ _) ∨ (_ ∧ _)) ↔ _
  tauto

theorem leftWholeProfile_gamma (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity (Q.leftWholeProfile N)) |
      p.2 ∈ carrier (rvObjectDomain (Q.leftWholeProfile N))} :=
  gamma_pullback_domain (gammaLogicInput G) (Q.leftTail N).target (Q.leftTail_target_gamma N)

def rightNRawDomain (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) := Map.image (rawKeyMap (Q.rightNFinalImage N))
def rightRRawDomain (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) := Map.image (rawKeyMap (Q.rightRFinalImage N))
def rightWholeRawDomain (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) := Map.image (rawKeyMap (Q.rightTail N).target)
def rightWholeProfile (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  selectedVolumeObject (Q.rightWholeRawDomain N) (Q.rightProgram N).volumeIndex

theorem rightNRaw_cut (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (Q.rightNRawDomain N) = {q | q ∈ carrier (Q.rightWholeRawDomain N) ∧
      q ∘ (Fin.natAdd 1 ∘ Q.rightFinalCodeProjection N) ∈ oldNLabels (T := T)} :=
  rawKeyImage_rvSlice (Q.rightFinalCodeProjection N) (oldNLabels (T := T)) (Q.rightNFinal_slice N)

theorem rightRRaw_cut (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (Q.rightRRawDomain N) = {q | q ∈ carrier (Q.rightWholeRawDomain N) ∧
      q ∘ (Fin.natAdd 1 ∘ Q.rightFinalCodeProjection N) ∉ oldNLabels (T := T)} :=
  rawKeyImage_rvSlice (Q.rightFinalCodeProjection N) (oldNLabels (T := T))ᶜ (Q.rightRFinal_slice N)

theorem rightNRaw_sub (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (Q.rightNRawDomain N) ⊆ carrier (Q.rightWholeRawDomain N) :=
  fun q hq => ((Set.ext_iff.mp (Q.rightNRaw_cut N) q).mp hq).1

theorem rightRRaw_sub (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (Q.rightRRawDomain N) ⊆ carrier (Q.rightWholeRawDomain N) :=
  fun q hq => ((Set.ext_iff.mp (Q.rightRRaw_cut N) q).mp hq).1

theorem rightRaw_disjoint (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    Disjoint (carrier (Q.rightNRawDomain N)) (carrier (Q.rightRRawDomain N)) := by
  apply Set.disjoint_left.mpr
  intro q hn hr
  exact ((Set.ext_iff.mp (Q.rightRRaw_cut N) q).mp hr).2 (((Set.ext_iff.mp (Q.rightNRaw_cut N) q).mp hn).2)

theorem rightRaw_cover (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (normalizedRVUnionSet (Q.rightNRawDomain N) (Q.rightRRawDomain N)) = carrier (Q.rightWholeRawDomain N) := by
  ext q
  change (q ∈ carrier (Q.rightNRawDomain N) ∨ q ∈ carrier (Q.rightRRawDomain N)) ↔ _
  rw [Q.rightNRaw_cut N,Q.rightRRaw_cut N]
  change ((_ ∧ _) ∨ (_ ∧ _)) ↔ _
  tauto

theorem rightWholeProfile_gamma (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    GammaSetDefinable G {p : Point (M := M) 0 (rvObjectArity (Q.rightWholeProfile N)) |
      p.2 ∈ carrier (rvObjectDomain (Q.rightWholeProfile N))} :=
  gamma_pullback_domain (gammaLogicInput G) (Q.rightTail N).target (Q.rightTail_target_gamma N)

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
