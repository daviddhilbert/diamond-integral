import «section 6».EverywhereMeasuredRVLiftData
import «section 6».MeasuredRVChainForgetting

/-! Actual relatively unary VF lift chains. Each component has its
complete definable map, is bijective and satisfies the everywhere total
measure identity. The composite retains those certificates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

inductive MeasuredVFUnaryLiftChain (S : Set M) (n : ℕ) :
    MeasuredRVObject (M := M) S n → MeasuredRVObject (M := M) S n → Type where
  | identity (U : MeasuredRVObject (M := M) S n) : MeasuredVFUnaryLiftChain S n U U
  | step {U V W : MeasuredRVObject (M := M) S n} (i : Fin n) {e : MeasuredRVIso U V}
      (F : EverywhereMeasuredRVLift e) (unary : VFUnaryRelativeAt F.map i)
      (tail : MeasuredVFUnaryLiftChain S n V W) : MeasuredVFUnaryLiftChain S n U W

def MeasuredVFUnaryLiftChain.iso {U V : MeasuredRVObject (M := M) S n} :
    MeasuredVFUnaryLiftChain S n U V → MeasuredRVIso U V
  | .identity U => .identity U
  | .step _ (e := e) _ _ T => e.comp T.iso

def MeasuredVFUnaryLiftChain.lift {U V : MeasuredRVObject (M := M) S n} :
    (T : MeasuredVFUnaryLiftChain S n U V) → EverywhereMeasuredRVLift T.iso
  | .identity U => .identity U
  | .step _ F _ T => F.comp T.lift

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def MeasuredVFUnaryLiftChain.properComponents {U V : MeasuredRVObject (M := M) S n} :
    (T : MeasuredVFUnaryLiftChain S n U V) → Prop
  | .identity U => ProperCovariantHomeomorphism (Map.id (rvLift U.object))
  | .step _ F _ T => ProperCovariantHomeomorphism F.map ∧ T.properComponents

theorem rvIso_finite_target_domain {U V : RVObject (M := M) S n} (e : U ≅ V)
    (hU : U.domain.carrier.Finite) : V.domain.carrier.Finite := by
  letI : Finite U.domain := hU.to_subtype
  apply (Set.finite_range (fun u : U.domain => (e.hom.map u).val)).subset
  intro v hv
  exact ⟨e.inv.map ⟨v,hv⟩,congrArg Subtype.val (rvIso_apply_inv e ⟨v,hv⟩)⟩

theorem MeasuredRVUnaryChain.source_doublyBounded {U V : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n U V) (hT : T.doublyBounded) : U.doublyBounded := by
  cases T with
  | identity U => exact hT
  | step i e h T => exact hT.1

end DiamondIntegral.Section6
