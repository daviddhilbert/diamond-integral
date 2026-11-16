import «section 6».VariableFocusCutoffs
import «section 6».CentripetalCoefficientRefinement

/-! One original-base named coefficient dominates both the constructed
joint component and every coefficient in a uniformly bounded old family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m t : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem exists_named_coefficient_dominating
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (D : CentripetalData (G := G) A)
    (δ : Gamma M) (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    {B : DefSet (rawMixedSpace (M := M) m t) S}
    (f : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hBound : ∀ b : B,vfValue ((f b).val 0) ≤ δ.val) :
    ∃ c : VF M,c ≠ 0 ∧ S.Definable₁ LRV {c.val} ∧ vfValue D.coefficient ≤ vfValue c ∧
      ∀ b : B,vfValue ((f b).val 0) ≤ vfValue c := by
  let γ := finiteValue D.coefficient D.coefficient_nonzero
  let ε := max (1 : Gamma M) (max δ γ)
  have hγ := finiteValue_named D.coefficient D.coefficient_nonzero D.coefficient_definable
  have hε := gamma_max_named (1 : Gamma M) (max δ γ) (gamma_one_named hc) (gamma_max_named δ γ hδ hγ)
  have hε1 : 1 ≤ ε := le_max_left _ _
  obtain ⟨c,hc0,hcDef,hεc⟩ := exists_named_vf_above_radius Valued.v hv hc h00
    V S hV hVS hSV hnt ε hε1 hε
  refine ⟨c,hc0,hcDef,?_,?_⟩
  · have h : γ ≤ ε := (le_max_right δ γ).trans (le_max_right 1 (max δ γ))
    exact (show vfValue D.coefficient ≤ ε.val from h).trans hεc.le
  · intro b
    have h : δ ≤ ε := (le_max_left δ γ).trans (le_max_right 1 (max δ γ))
    exact (hBound b).trans ((show δ.val ≤ ε.val from h).trans hεc.le)

end DiamondIntegral.Section6.CentripetalData
