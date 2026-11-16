import «section 6».FiniteProgramFusion

/-! An arbitrary finite program tree normalizes with exactly the
same complete data and is fused by the checked sequential induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t q k : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def UniformProgramFamily.sequential
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {T : CentripetalProgramTemplate (M := M) S 1 n s t}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    (U : UniformProgramFamily η T A P) : UniformProgramFamily η T.toSequence.toProgram A P where
  geometry := U.geometry
  pullback := U.pullback
  prepared b := (Set.ext_iff.mp (T.toSequence_sameData.preparedGood A P) _).mp (U.prepared b)
  rows D hD := U.rows D (by rw [T.toSequence_sameData.rvTrace]; exact hD)
  radius := U.radius
  named := U.named
  bound D hD := U.bound D (by rw [T.toSequence_sameData.rvTrace]; exact hD)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem synchronized_preparation_of_uniform_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hIH : SynchronizedPreparationInDimension (G := G) S n k)
    (hB : ProperInvariant S B.carrier) (hBRP : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {T : CentripetalProgramTemplate (M := M) S 1 n s t}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
    (U : UniformProgramFamily η T A P) (X : SelectedProgramContext η A P C π σ) :
    Nonempty (PreparedSynchronizedFamily (G := G) C
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (fun i => rvLabelPullback_subset C _ _)) :=
  synchronized_preparation_of_uniform_sequence h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hIH
    hB hBRP hBTag T.toSequence A P C π σ U.sequential X

end DiamondIntegral.Section6
