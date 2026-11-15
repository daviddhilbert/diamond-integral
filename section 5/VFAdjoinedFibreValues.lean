import «section 5».VFAdjoinedParameterTransfer
import «section 5».VFBoundedGroundNaturality
import «section 5».OriginalFibreIntegralVanishing

/-! Actual fibre values over the genuine F(b) field presentation imply
the exact raw-parameter value used by native Fubini. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {n : ℕ} (b : Fin n → M) (hb : ∀ i,iVF (b i))
variable (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1)
variable (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)

def vfAdjoinedFiniteObject (A : GammaGroundFiniteVFObject hc (vfRawParameterBase G b)) :
    GammaGroundFiniteVFObject hc (vfAdjoinedContext hc G b hnt).base :=
  sortedTransferFiniteVFObject (raw_to_vfAdjoinedContext hc G b hb hnt hγ) A

theorem vfAdjoinedFibreValue_to_raw
    (I : YinGammaGroundUnmeasuredLiftInput (vfAdjoinedContext hc G b hnt) hc)
    (A : GammaGroundFiniteVFObject hc (vfRawParameterBase G b))
    (h : nativeVFBoundedValue linear I (nativeVFClass (vfAdjoinedFiniteObject b hb hnt hγ A)) = 0) :
    originalBaseVFBoundedValue (hc := hc) (B := vfRawParameterBase G b) G.model00 linear G.uncountable.le G.saturated
      (small_union_range_carrier G.uncountable.le G.base.real G.small_real b) G.small_gamma
      (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl)
      (vfRawParameterLiftInput hc G b hb hnt hγ I) (nativeVFClass A) = 0 := by
  let C := vfAdjoinedContext hc G b hnt
  let H : ∀ {d : ℕ} (sn : Fin d → SortTag) (D : Set (Fin d → M)),
      DefinableOverBase C.base sn D → DefinableOverBase (vfRawParameterBase G b) sn D :=
    vfAdjoinedContext_to_raw hc G b hnt
  let K : ∀ {d : ℕ} (sn : Fin d → SortTag) (D : Set (Fin d → M)),
      DefinableOverBase (vfRawParameterBase G b) sn D → DefinableOverBase C.base sn D :=
    raw_to_vfAdjoinedContext hc G b hb hnt hγ
  let J := vfRawParameterLiftInput hc G b hb hnt hγ I
  have he := originalBaseVFBoundedValue_parameter_naturality H G.model00 linear G.uncountable.le G.saturated
    C.small_real C.small_gamma C.nontrivial_definable_gamma
    (small_union_range_carrier G.uncountable.le G.base.real G.small_real b) G.small_gamma
    (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl)
    (originalBaseLiftInputOfContext I) J (nativeVFClass (sortedTransferFiniteVFObject K A))
  have hclass : sortedTransferVFRing H (nativeVFClass (sortedTransferFiniteVFObject K A)) = nativeVFClass A := by
    change sortedTransferVFRing H (of (gammaGroundVFSemiringClass (sortedTransferFiniteVFObject K A))) = of (gammaGroundVFSemiringClass A)
    rw [sortedTransferVFRing_class]
    exact congrArg of (nativePositiveVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl))
  change resGroundTransferReduced H (nativeVFBoundedValue linear I (nativeVFClass (vfAdjoinedFiniteObject b hb hnt hγ A))) = _ at he
  rw [h,map_zero,hclass] at he
  exact he.symm

end DiamondIntegral.Section5
