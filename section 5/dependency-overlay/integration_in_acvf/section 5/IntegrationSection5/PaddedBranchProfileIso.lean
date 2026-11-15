import IntegrationSection5.PaddingProfileIso
import IntegrationSection5.PaddedUnaryBranchLift
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.PaddedUnaryBranchLift
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {H : DefSet (M := M) S 1 l} {u : SpecialBijection A B}
variable {ρ : Fin a → Fin l} {E : Set (Fin a → RV (M := M))} {previous : Option Bool}

def profileIso (L : PaddedUnaryBranchLift (G := G) u H ρ E previous) (j : Fin a) :
    GammaRVIso G
      (selectedVolumeObject (Map.image (rawKeyMap L.active_image))
        ![Fin.natAdd 1 (suffixIndex L.arity_le (ρ j)),0])
      (selectedVolumeObject (Map.image (rawKeyMap B))
        ![Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le u.chain) j),0]) := by
  apply L.active_padding.profileIso
  intro i
  fin_cases i
  · change headPaddingProjection L.projection (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le u.chain) j)) =
      Fin.natAdd 1 (suffixIndex L.arity_le (ρ j))
    rw [headPaddingProjection,Fin.append_right]
    exact congrArg (Fin.natAdd 1) (L.suffix_compatibility j)
  · change headPaddingProjection L.projection (0 : Fin (1+b)) = 0
    exact Fin.append_left (fun _ : Fin 1 => 0) (Fin.natAdd 1 ∘ L.projection) (0 : Fin 1)

end IntegrationInACVF.Section5.PaddedUnaryBranchLift
