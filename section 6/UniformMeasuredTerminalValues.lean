import «section 6».UniformMeasuredProgramFamilies
import «section 6».GammaTransitionSemantics

/-! Full terminal Gamma rows compare actual form values across different
VF parameters with the same retained base labels. Separate local terminal
constancy alone would not establish this cross-parameter conclusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformMeasuredProgramFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplate (M := M) S 1 n s}

theorem values_eq_of_transition_labels
    (U : UniformMeasuredProgramFamily (G := G) η T A P W)
    (b c : B) (hBase : b.val.2=c.val.2)
    {Zb : DefSet (rawMixedSpace (M := M) n t) (S ∪ Set.range (unaryFamilyParameter η b))}
    {Zc : DefSet (rawMixedSpace (M := M) n t) (S ∪ Set.range (unaryFamilyParameter η c))}
    (f : Map (A.fibre (unaryFamilyParameter η b)) Zb) (hf : Function.Bijective f)
    (g : Map (A.fibre (unaryFamilyParameter η c)) Zc) (hg : Function.Bijective g)
    (hfb : {z | Sum.elim (unaryFamilyParameter η b) z ∈ (T.transition A).graph}=
      (rawMixedSpace n s).relation (rawMixedSpace n t) f.graph)
    (hgc : {z | Sum.elim (unaryFamilyParameter η c) z ∈ (T.transition A).graph}=
      (rawMixedSpace n s).relation (rawMixedSpace n t) g.graph)
    (x : A.fibre (unaryFamilyParameter η b)) (y : A.fibre (unaryFamilyParameter η c))
    (hTags : (f x).val.2=(g y).val.2) : (U.forms b x).val=(U.forms c y).val := by
  let ζb := (U.forms b).comp (f.inverse hf)
  let ζc := (U.forms c).comp (g.inverse hg)
  have hGraphb := gammaTransitionImage_at (unaryFamilyParameter η b) (T.transition A).graph W.graph f hf (U.forms b) hfb (U.graphs b)
  have hGraphc := gammaTransitionImage_at (unaryFamilyParameter η c) (T.transition A).graph W.graph g hg (U.forms c) hgc (U.graphs c)
  have hConstSource := (gammaTransitionConstantParameterLocus_iff (unaryFamilyParameter η c)
    (T.transition A).graph W.graph g (U.forms c) hgc (U.graphs c)).mp (U.admissible c).1.2
  have hConst (v w : Zc) (he : v.val.2=w.val.2) : (ζc v).val=(ζc w).val := by
    apply hConstSource (g.inverse hg v) (g.inverse hg w)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact he
  have hRows := U.measuredRows _ (T.gammaRVTrace_mem A P W) b c hBase
  have h := (W.transport (T.transition A)).values_eq_of_rvTrace_eq _ _ ζb ζc hGraphb hGraphc hRows hConst (f x) (g y) hTags
  change (U.forms b (f.inverse hf (f x))).val=(U.forms c (g.inverse hg (g y))).val at h
  rw [Map.inverse_apply,Map.inverse_apply] at h
  exact h

end DiamondIntegral.Section6.UniformMeasuredProgramFamily
