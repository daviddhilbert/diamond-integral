import «section 3».GammaDensityCodeRows
import IntegrationSection6.GammaVFFieldClosureBases
import IntegrationSection6.GammaFieldBaseReduction

/-! Arbitrary Gamma densities are determined by old RV labels and a
finite tuple of VF tests. The test graph descends to the original Gamma
ground, even when the Gamma density itself has no definable RV lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def gammaDensityVFPoint (B : Base (M := M)) (x : Fin n → Section2.VF M) :
    SpecialTransformations.Section5.PresentedSet.univ
      (SpecialTransformations.Section5.pointSpace (M := M) n 0) B.real :=
  ⟨(x,Fin.elim0),Set.mem_univ _⟩

theorem gammaDensity_finite_RV_data
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    (ω : GammaGroundVolumeForm hc B A) :
    ∃ d : ℕ, ∃ g : SpecialTransformations.Section5.Map
      (SpecialTransformations.Section5.PresentedSet.univ
        (SpecialTransformations.Section5.pointSpace (M := M) n 0) (vfFieldNamedBase B).real)
      (SpecialTransformations.Section5.PresentedSet.univ
        (SpecialTransformations.Section5.pointSpace (M := M) 0 d) (vfFieldNamedBase B).real),
      SpecialTransformations.Section5.GammaGraphDefinable B (SpecialTransformations.Section5.pointMapGraph g) ∧
      ∀ a b : A, a.val.2 = b.val.2 →
        g (gammaDensityVFPoint (vfFieldNamedBase B) a.val.1) =
          g (gammaDensityVFPoint (vfFieldNamedBase B) b.val.1) → (ω a).val = (ω b).val := by
  let D : GammaDomainFormula B n (r+1) (fun _ => .vf) :=
    ⟨gammaDensityCodeRows ω,gammaDensityCodeRows_definable ω⟩
  let H : GammaFormulaBaseChange B (vfFieldNamedBase B) :=
    ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  obtain ⟨d,g,hg,hrows⟩ := gamma_domain_vf_code_in_base H (vfFieldNamedBase_field B) D
  refine ⟨d,g,vfFieldNamedBase_eliminate hg,?_⟩
  intro a b hab hgab
  obtain ⟨c,hc⟩ := (volumeGammaSpace hc).onto (ω a).val
  have hrow := hrows (gammaDensityVFPoint (vfFieldNamedBase B) a.val.1)
    (gammaDensityVFPoint (vfFieldNamedBase B) b.val.1) hgab
  have hrow' : Fin.append (vfValues a.val.1) (Fin.append (rvValues a.val.2) c.val) ∈ gammaDensityCodeRows ω ↔
      Fin.append (vfValues b.val.1) (Fin.append (rvValues a.val.2) c.val) ∈ gammaDensityCodeRows ω :=
    hrow (Fin.append (rvValues a.val.2) c.val)
  have ha := (gammaDensityCodeRows_mem ω a.val c).mpr ⟨a,rfl,hc.symm⟩
  have hb := hrow'.mp ha
  rw [hab] at hb
  obtain ⟨t,ht,hw⟩ := (gammaDensityCodeRows_mem ω b.val c).mp hb
  have he : t = b := Subtype.ext ht
  exact hc.symm.trans ((congrArg (fun z : A => (ω z).val) he).symm.trans hw).symm

end DiamondIntegral.Section3
