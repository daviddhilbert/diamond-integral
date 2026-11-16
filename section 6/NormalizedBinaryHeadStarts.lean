import «section 6».NormalizedBinaryMeasuredContractions

/-! Binary measured contractions carry every head start directly from
the original source, including its permitted preliminary normalization.
The finite-volume hypothesis is imposed on that original source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 2 r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin 2)}
namespace NormalizedBinaryMeasuredContraction

def oldIndex (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (j : Fin r) :=
  F.preparedContraction.data.program.oldLabels (Fin.natAdd 2 j)

theorem retained (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (p : A) (j : Fin r) :
    (F.map p).val.2 (F.oldIndex j)=p.val.2 j := by
  have h := F.preparedContraction.lift.retained
    (vfRelabeling F.normalization.map.image e (F.normalization.bijection p)) (Fin.natAdd 2 j)
  change (F.map p).val.2 (F.oldIndex j)=
    F.normalization.tags p.val.2 (F.normalization.core p.val) (Fin.natAdd 2 j) at h
  simpa only [ZeroCenteredData.tags,Fin.append_right] using h

theorem target_tagged (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) :
    ∀ p ∈ F.target.carrier,∀ z ∈ F.target.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 :=
  reindexedVFSet_tagged _ e.symm F.preparedContraction.lift.target_tagged

def headStartObject (F : NormalizedBinaryMeasuredContraction (G := G) A ω e)
    (k : ℕ) (π : Fin k → Fin r) : RVObject (M := M) S (2+k) :=
  preparedHeadStartRVObject F.target k (F.oldIndex ∘ π) F.target_tagged

def headStartBijection
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r) :
    HeadStartCarriedBijection F.map k π (F.oldIndex ∘ π) :=
  carryHeadStartBijection F.map (F.homeomorphism h00 hc linear hκ hs hv hsmall hΓ).bijective k π _
    (fun p i => F.retained p (π i))

theorem headStartObject_finite_volume
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin 2 → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) :
    (F.headStartObject k π).volume.FiniteFibres :=
  prepared_head_start_finite_volume_of_bijective hc h00 hκ.le hs hsmall F.map
    (F.homeomorphism h00 hc linear hκ hs hv hsmall hΓ).bijective k π _
    (fun p i => F.retained p (π i)) F.preparedContraction.lift.originalTarget_pullback F.target_tagged hFin

theorem headStartObject_doublyBounded
    (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r) :
    RVValueDoublyBounded (F.headStartObject k π).domain.carrier ∧
      RVValueDoublyBounded (Set.range (F.headStartObject k π).value) :=
  preparedHeadStartRVObject_doublyBounded F.target k _ F.target_tagged
    F.preparedContraction.lift.originalTarget_doublyBounded F.preparedContraction.lift.originalTarget_proper.rvBounded

def headStartMeasuredObject
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin 2 → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) : MeasuredRVObject (M := M) S (2+k) where
  object := F.headStartObject k π
  finiteVolume := F.headStartObject_finite_volume h00 hc linear hκ hs hv hsmall hΓ k π hFin
  nonzero := preparedRVObject_nonzero _ _
    (rvHeadStartBundle_doublyBounded F.target k _ F.preparedContraction.lift.originalTarget_doublyBounded
      F.preparedContraction.lift.originalTarget_proper.rvBounded)
  form := headStartRVForm F.target k _ F.form F.form_same_tags

end NormalizedBinaryMeasuredContraction
end DiamondIntegral.Section6
