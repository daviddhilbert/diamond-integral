import «section 7».StageSlices
import «section 6».UnaryRelativeRetainedTags
import «section 6».UnaryRelativeApertureChains
import «section 6».DiamondSimultaneous

/-! Unary relative aperture chains as contraction stages (for Lemma 7.21).

A unary relative aperture chain `f : A → B` whose end set `B` is a proper
invariant, VF-doubly bounded RV pullback, with a label `k` recording the
leading term (`rv(x) = u_k` on `B`), is a stage of a standard contraction of the
unary set `A` (`chainStage`). The chain is a proper covariant homeomorphism with
almost everywhere unit derivative, it retains the original labels as its last
labels, and an RV pullback with a leading label is the full RV-disc bundle
over its contracted set (Section 6 `rvPullback_last_coordinate_bundle`).

In particular the two chains of Lemma 6.38 (`simul:special:dim:1`) for a
morphism `A → B` of `μVF^◇[1]` are stages of standard contractions of `A` and
of `B` (`sourceStage`, `targetStage`). The paper's proof of Lemma 7.21 uses
them ("Lemma 6.38 gives special covariant bijections `T_{A₁}`, `T_{A₂}` … This
gives standard contractions"). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ChainStages
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem rvTailIndex_injective {h : r ≤ s} : Function.Injective (rvTailIndex h) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  simp only [rvTailIndex] at this
  omega

/-- **A unary relative aperture chain onto a prepared set is a contraction
stage.** -/
def chainStage (f : Map A B) (hchain : UnaryRelativeApertureChain (G := G) A B f)
    (hB : ProperInvariant S B.carrier) (hBb : VFDoublyBounded B.carrier) (hBp : IsRVPullback B.carrier)
    (k : Fin s) (hlead : ∀ p ∈ B.carrier, rv M (p.1 0) = p.2 k) : StandardContractionStage (G := G) A :=
  haveI : CharZero (VF M) := vf_charZero_of_model00 h00
  { arity := s
    target := B
    lift := f
    home := hchain.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    proper := hB
    doublyBounded := hBb
    relative := fun _ i => i.elim0
    oldLabels := rvTailIndex hchain.retainsRV.choose
    oldLabels_injective := rvTailIndex_injective
    retained := hchain.retainsRV.choose_spec
    leading := k
    bundle := rvPullback_last_coordinate_bundle B hBp k (fun p hp => hlead p hp)
    exceptional := (hchain.unit_derivative_ae h00 hc hκ.le hs hsmall hv).choose
    exceptional_subset := (hchain.unit_derivative_ae h00 hc hκ.le hs hsmall hv).choose_spec.1
    exceptional_dim := (hchain.unit_derivative_ae h00 hc hκ.le hs hsmall hv).choose_spec.2.1
    unitDerivative := (hchain.unit_derivative_ae h00 hc hκ.le hs hsmall hv).choose_spec.2.2 }

theorem chainStage_lift (f : Map A B) (hchain : UnaryRelativeApertureChain (G := G) A B f)
    (hB : ProperInvariant S B.carrier) (hBb : VFDoublyBounded B.carrier) (hBp : IsRVPullback B.carrier)
    (k : Fin s) (hlead : ∀ p ∈ B.carrier, rv M (p.1 0) = p.2 k) :
    (chainStage h00 hc linear hκ hs hv hsmall hΓ f hchain hB hBb hBp k hlead).lift = f := rfl

theorem chainStage_target (f : Map A B) (hchain : UnaryRelativeApertureChain (G := G) A B f)
    (hB : ProperInvariant S B.carrier) (hBb : VFDoublyBounded B.carrier) (hBp : IsRVPullback B.carrier)
    (k : Fin s) (hlead : ∀ p ∈ B.carrier, rv M (p.1 0) = p.2 k) :
    (chainStage h00 hc linear hκ hs hv hsmall hΓ f hchain hB hBb hBp k hlead).target = B := rfl

/-! ### The two chains of Lemma 6.38 -/

section Matching
variable {f : Map A B} {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable {σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)}

/-- The source chain of a measured matching (Lemma 6.38) as a contraction
stage of `A`. -/
def sourceStage (H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ) : StandardContractionStage (G := G) A :=
  chainStage h00 hc linear hκ hs hv hsmall hΓ H.geometry.sourceMap H.geometry.sourceChain H.geometry.sourceProper
    H.geometry.sourceBounded H.geometry.sourcePullback H.sourceIndex H.sourceLeading

/-- The target chain of a measured matching (Lemma 6.38) as a contraction
stage of `B`. -/
def targetStage (H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ) : StandardContractionStage (G := G) B :=
  chainStage h00 hc linear hκ hs hv hsmall hΓ H.geometry.targetMap H.geometry.targetChain H.geometry.targetProper
    H.geometry.targetBounded H.geometry.targetPullback H.targetIndex H.targetLeading

end Matching

end DiamondIntegral.Section7.ChainStages
