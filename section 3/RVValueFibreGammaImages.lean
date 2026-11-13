import «section 3».GammaRVBaseColumns
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- A definable Gamma-valued function on an actual RV value fibre has
finite image over the original real/Gamma base. -/
theorem rv_value_fibre_gamma_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (δ : Values.Gamma (M := M))
    (hδ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = δ.val)
    (f : D → Values.Gamma (M := M))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ ∃ d : D, d.val = z 1 ∧ f d = codeValue (z 0)}) :
    (Set.range f).Finite := by
  let R (γ : Values.Gamma (M := M)) (t : M) := ∃ d : D, d.val = t ∧ f d = γ
  have hsort (γ : Values.Gamma (M := M)) (t : M) (ht : R γ t) : iRV t := by
    obtain ⟨d,rfl,_⟩ := ht
    exact hD.proper d.val d.property
  have hsub (γ : Values.Gamma (M := M)) (t : M) (ht : R γ t) : t ∈ D := by
    obtain ⟨d,rfl,_⟩ := ht
    exact d.property
  have hC := gammaRVBase_finite_columns hκ hs h00 B hsmall R hsort hf D hD δ hδ hsub
  have hcol (d : D) : relationColumn R d.val = {f d} := by
    ext γ
    constructor
    · rintro ⟨e,he,hf⟩
      have hed : e = d := Subtype.ext he
      subst e
      exact hf.symm
    · intro hγ
      exact ⟨d,rfl,hγ.symm⟩
  have hsubC : (fun γ : Values.Gamma (M := M) => ({γ} : Set (Values.Gamma (M := M)))) '' Set.range f ⊆
      relationColumn R '' D := by
    rintro _ ⟨_,⟨d,rfl⟩,rfl⟩
    exact ⟨d.val,d.property,hcol d⟩
  exact (hC.subset hsubC).of_finite_image Set.singleton_injective.injOn
end DiamondIntegral.Section3
