import «section 6».MeasuredVFUnaryLiftChains

/-! Composition and actual intermediate double bounds for measured
VF unary lift chains. Every component and the full composite are proper
covariant homeomorphisms under those bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def MeasuredVFUnaryLiftChain.comp {U V W : MeasuredRVObject (M := M) S n} :
    MeasuredVFUnaryLiftChain S n U V → MeasuredVFUnaryLiftChain S n V W → MeasuredVFUnaryLiftChain S n U W
  | .identity _,L => L
  | .step i F h T,L => .step i F h (T.comp L)

theorem MeasuredVFUnaryLiftChain.comp_map {U V W : MeasuredRVObject (M := M) S n}
    (T : MeasuredVFUnaryLiftChain S n U V) (L : MeasuredVFUnaryLiftChain S n V W) (u : U.object.domain) :
    (T.comp L).iso.iso.hom.map u = L.iso.iso.hom.map (T.iso.iso.hom.map u) := by
  induction T with
  | identity U => rfl
  | step i F h T ih => exact ih L _

def MeasuredVFUnaryLiftChain.doublyBounded {U V : MeasuredRVObject (M := M) S n} :
    MeasuredVFUnaryLiftChain S n U V → Prop
  | .identity U => U.doublyBounded
  | .step _ _ _ T => U.doublyBounded ∧ T.doublyBounded

theorem MeasuredVFUnaryLiftChain.source_doublyBounded {U V : MeasuredRVObject (M := M) S n}
    (T : MeasuredVFUnaryLiftChain S n U V) (h : T.doublyBounded) : U.doublyBounded := by
  cases T with
  | identity U => exact h
  | step i F hu T => exact h.1

theorem MeasuredVFUnaryLiftChain.target_doublyBounded {U V : MeasuredRVObject (M := M) S n}
    (T : MeasuredVFUnaryLiftChain S n U V) (h : T.doublyBounded) : V.doublyBounded := by
  induction T with
  | identity U => exact h
  | step i F hu T ih => exact ih h.2

theorem MeasuredVFUnaryLiftChain.comp_doublyBounded {U V W : MeasuredRVObject (M := M) S n}
    (T : MeasuredVFUnaryLiftChain S n U V) (L : MeasuredVFUnaryLiftChain S n V W)
    (hT : T.doublyBounded) (hL : L.doublyBounded) : (T.comp L).doublyBounded := by
  induction T with
  | identity U => exact hL
  | step i F hu T ih => exact ⟨hT.1,ih L hT.2 hL⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem MeasuredVFUnaryLiftChain.properComponents_of_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) S n} (T : MeasuredVFUnaryLiftChain S n U V) :
    T.doublyBounded → T.properComponents := by
  induction T with
  | identity U =>
    intro hU
    let F := EverywhereMeasuredRVLift.identity U
    exact properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ (.identity U)
      hU hU F.map F.bijective F.labels (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩)
  | @step U V W i e F hu T ih =>
    intro hT
    exact ⟨properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ e
      hT.1 (T.source_doublyBounded hT.2) F.map F.bijective F.labels
      (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩),ih hT.2⟩

end DiamondIntegral.Section6
