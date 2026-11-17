import «section 3».GammaRVFormConstraints
import Integration7.HKDensityLabelConstraints

/-! Arbitrary Gamma equality of retained RV forms is a sorted graph
constraint with any real/RV parameter block. This is the exact replacement
for a distinguished RV density coordinate in finite-row preparation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}
variable (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
variable (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)

def gammaFormConstraintIndices (p a b : ℕ) : Fin (a+b) → Fin ((p+a)+b) :=
  Fin.addCases (fun i => Fin.castAdd b (Fin.natAdd p i)) (fun j => Fin.natAdd (p+a) j)

def gammaParametricFormConstraint (sp : Fin p → SortTag) : Set (Fin ((p+a)+b) → M) :=
  {w | w ∘ gammaFormConstraintIndices p a b ∈ gammaRVFormRawConstraint A D ω π ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))}

theorem gammaParametricFormConstraint_definable (sp : Fin p → SortTag) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))
      (gammaParametricFormConstraint A D ω π sp) :=
  (gammaRVFormRawConstraint_definable A D ω π).preimage_real _ (gammaFormConstraintIndices p a b)

theorem gammaParametricFormConstraint_append (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) (u : A) (v : D) :
    Fin.append (Fin.append z (rvValues u.val)) (rvValues v.val) ∈
      gammaParametricFormConstraint A D ω π sp ↔ ω u = π v := by
  have hidx : Fin.append (Fin.append z (rvValues u.val)) (rvValues v.val) ∘ gammaFormConstraintIndices p a b =
      Fin.append (rvValues u.val) (rvValues v.val) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [gammaFormConstraintIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
  change (_ ∈ _ ∧ _) ↔ _
  rw [hidx,gammaRVFormRawConstraint_mem]
  exact ⟨And.left,fun h => ⟨h,sorted_append_RV _ _ (sorted_append_RV sp z hz u.val) v.val⟩⟩

end DiamondIntegral.Section3
