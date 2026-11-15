import «section 5».NativeMapParameterTransfer
import «section 5».OriginalFibreIntegralVanishing
import «section 5».VFBoundedGroundNaturality
import «section 5».VFAdjoinedParameterTransfer

/-! A definable change of target coordinates transports the literal
fibre and its intrinsic bounded integral across equivalent raw bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3
open DiamondIntegral.Section4 Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}
variable {p q u v : ℕ} (A : GammaGroundFiniteVFObject hc G.base)
variable {C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q)}
variable {D : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) u v)}
variable (f : GammaGroundMap A.domain C) (g : GammaGroundMap A.domain D)
variable (T : GammaGroundBijection C D) (h : ∀ a,g a = T.map (f a)) (b : C)

def nativeTargetChangedFibreBijection :
    GammaGroundBijection (nativeMixedMapFibreAt f (nativeMixedCode b.val))
      (sortedTransferMixedDomain (nativeMixedMap_parameter_transfer T.map b)
        (nativeMixedMapFibreAt g (nativeMixedCode (T.map b).val))) := by
  apply GammaGroundBijection.ofCarrierEq
  ext x
  change x ∈ (nativeMixedMapFibreAt f (nativeMixedCode b.val)).carrier ↔
    x ∈ (nativeMixedMapFibreAt g (nativeMixedCode (T.map b).val)).carrier
  rw [nativeMixedMapFibreAt_mem,nativeMixedMapFibreAt_mem]
  constructor
  · rintro ⟨a,ha,hb⟩
    have he : f a = b := Subtype.ext (nativeMixedCode_injective hb)
    exact ⟨a,ha,by rw [h,he]⟩
  · rintro ⟨a,ha,hb⟩
    have he : g a = T.map b := Subtype.ext (nativeMixedCode_injective hb)
    rw [h] at he
    have hf : f a = b := T.bijective.injective he
    exact ⟨a,ha,congrArg (fun x : C => nativeMixedCode x.val) hf⟩

include h in
theorem originalBaseTargetFibre_zero
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (I : OriginalBaseUnmeasuredLiftInput hc (vfRawParameterBase G (nativeMixedCode b.val)))
    (J : OriginalBaseUnmeasuredLiftInput hc (vfRawParameterBase G (nativeMixedCode (T.map b).val)))
    (hz : originalBaseVFBoundedValue (hc := hc) (B := vfRawParameterBase G (nativeMixedCode (T.map b).val)) G.model00 linear G.uncountable.le G.saturated
      (small_union_range_carrier G.uncountable.le G.base.real G.small_real (nativeMixedCode (T.map b).val))
      G.small_gamma (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) J
      (nativeVFClass (nativeFiniteMixedMapFibre A g (nativeMixedCode (T.map b).val))) = 0) :
    originalBaseVFBoundedValue (hc := hc) (B := vfRawParameterBase G (nativeMixedCode b.val)) G.model00 linear G.uncountable.le G.saturated
      (small_union_range_carrier G.uncountable.le G.base.real G.small_real (nativeMixedCode b.val))
      G.small_gamma (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) I
      (nativeVFClass (nativeFiniteMixedMapFibre A f (nativeMixedCode b.val))) = 0 := by
  let H : ∀ {d : ℕ} (sn : Fin d → SortTag) (E : Set (Fin d → M)),
      DefinableOverBase (vfRawParameterBase G (nativeMixedCode (T.map b).val)) sn E →
        DefinableOverBase (vfRawParameterBase G (nativeMixedCode b.val)) sn E :=
    nativeMixedMap_parameter_transfer T.map b
  have he := originalBaseVFBoundedValue_parameter_naturality H G.model00 linear G.uncountable.le G.saturated
    (small_union_range_carrier G.uncountable.le G.base.real G.small_real (nativeMixedCode (T.map b).val))
    G.small_gamma (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl)
    (small_union_range_carrier G.uncountable.le G.base.real G.small_real (nativeMixedCode b.val))
    G.small_gamma (G.nontrivial_definable_gamma.mono Set.subset_union_left Set.Subset.rfl) J I
    (nativeVFClass (nativeFiniteMixedMapFibre A g (nativeMixedCode (T.map b).val)))
  have hc' : sortedTransferVFRing H (nativeVFClass (nativeFiniteMixedMapFibre A g
      (nativeMixedCode (T.map b).val))) = nativeVFClass (nativeFiniteMixedMapFibre A f (nativeMixedCode b.val)) := by
    change sortedTransferVFRing H (of (gammaGroundVFSemiringClass _)) = of (gammaGroundVFSemiringClass _)
    rw [sortedTransferVFRing_class]
    exact congrArg of (nativePositiveVFClass_bijection (nativeTargetChangedFibreBijection A f g T h b).symm)
  rw [hz,map_zero,hc'] at he
  exact he.symm

end DiamondIntegral.Section5
