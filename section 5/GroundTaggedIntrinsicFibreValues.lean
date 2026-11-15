import «section 5».PuiseuxGroundTaggedVanishing

/-! Intrinsic fibre values as a reusable, exact field-context predicate.
An actual point equivalence may index the hypothesis without changing it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

def GroundTaggedFieldLiftInputs
    (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1) (p q : ℕ) :=
  ∀ z : Fin (p+q) → M, (∀ i,iRV (z i) → z i ∈ G.base.real) →
    YinGammaGroundUnmeasuredLiftInput (vfAdjoinedContext hc G z hnt) hc

def GroundTaggedIntrinsicFibreVanishes
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1)
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (hC : NativeGroundRVLabels C) (f : GammaGroundMap A.domain C)
    (I : GroundTaggedFieldLiftInputs (hc := hc) hnt p q) (b : C) : Prop :=
  let z := nativeMixedCode b.val
  let hz : z ∈ nativeMixedDomain C := ⟨b.val,b.property,rfl⟩
  nativeVFBoundedValue linear (I z (nativeGroundRVLabels_raw C hC z hz))
    (nativeVFClass (vfAdjoinedMixedFiniteObject z (nativeGroundRVLabels_raw C hC z hz)
      hnt hγ (nativeFiniteMixedMapFibre A f z))) = 0

end DiamondIntegral.Section5

namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3
local instance indexedFibreSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance indexedFibreSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := N)} {G : GammaGroundContext N}

theorem ambientBoundedVFVolume_point_indexed_fibres
    (e : Carrier ↪ₑ[LRV] N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := N))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (A : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := N) p q)) (hC : NativeGroundRVLabels C)
    (f : GammaGroundMap A.domain C)
    (I : GroundTaggedFieldLiftInputs (hc := hc) (ambientLaurentField_nontrivial e G hB) p q)
    {P : Type} (E : P ≃ C)
    (h : ∀ b : P,GroundTaggedIntrinsicFibreVanishes linear (ambientLaurentField_nontrivial e G hB)
      hγ A C hC f I (E b)) :
    ambientBoundedVFVolume e hB hγ linear H (nativeVFClass A) = 0 := by
  apply ambientBoundedVFVolume_ground_tagged_fibres e hB hγ linear H A C hC f I
  intro z hz
  obtain ⟨y,hy,he⟩ := hz
  let b : C := ⟨y,hy⟩
  obtain ⟨a,ha⟩ := E.surjective b
  have hz' : z = nativeMixedCode (E a).val :=
    he.symm.trans (congrArg (fun x : C => nativeMixedCode x.val) ha).symm
  cases hz'
  exact h a

end DiamondIntegral.Section5.PuiseuxOriginal
