import «section 6».UniformMeasuredProgramFamilies
import «section 6».MeasuredProgramPrefixLoci
import «section 6».ExactGammaTransport

/-! Removing an actual program prefix constructs the remaining local
Gamma maps through its actual inverse. Full graphs, open levels, all
remaining component guards and the complete measured row bound survive. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformMeasuredProgramFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t v k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def afterPrefix
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {F : CentripetalProgramTemplate (M := M) S 1 n s t}
    {H : CentripetalProgramTemplate (M := M) S 1 n t v}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {W : GammaFormParameterTemplate (M := M) S 1 n s}
    (U : UniformMeasuredProgramFamily (G := G) η (F.comp H) A P W) :
    UniformMeasuredProgramFamily (G := G) η H (F.target A) (fun i => F.pieceTarget A (P i)) (W.transport (F.transition A)) := by
  have hGuard (b : B) := (Set.ext_iff.mp (F.measuredFormGood_comp H A P W) _).mp (U.admissible b)
  have hReal (b : B) := F.exists_realization h00 hc hκ hs hv A P _ (hGuard b).1.1
    (U.geometry b).proper (U.geometry b).doublyBounded (U.geometry b).subset (U.geometry b).piecesProper
  let R (b : B) := Classical.choice (hReal b)
  let ζ (b : B) := (U.forms b).comp ((R b).map.inverse ((R b).chain.toChain.toSpecial.bijective h00))
  have hTransport (b : B) (p : A.fibre (unaryFamilyParameter η b)) :
      (ζ b ((R b).map p)).val=(U.forms b p).val := by
    change (U.forms b ((R b).map.inverse _ ((R b).map p))).val=(U.forms b p).val
    rw [Map.inverse_apply]
  refine {
    toUniformProgramFamily := U.toUniformProgramFamily.afterPrefix (G := G) h00 hc hκ hs hv
    forms := ζ
    graphs := ?_
    levels := ?_
    admissible := fun b => (hGuard b).2
    measuredRows := fun D hD => U.measuredRows D (F.measuredRVTrace_afterPrefix_subset H A P W D hD)
    measuredBound := fun D hD => U.measuredBound D (F.measuredRVTrace_afterPrefix_subset H A P W D hD) }
  · intro b
    exact gammaTransitionImage_at (unaryFamilyParameter η b) (F.transition A).graph W.graph (R b).map
      ((R b).chain.toChain.toSpecial.bijective h00) (U.forms b) (R b).graph (U.graphs b)
  · intro b
    exact (R b).chain.toChain.toSpecial.exact_gamma_levels_open h00 hc linear hκ hs hv
      (small_union_range hκ.le S hsmall (unaryFamilyParameter η b))
      (hΓ.mono Set.subset_union_left (Set.Subset.rfl)) (U.forms b) (U.levels b) (ζ b) (hTransport b)

end DiamondIntegral.Section6.UniformMeasuredProgramFamily
