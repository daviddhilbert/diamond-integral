import «section 3».RVValueFibreGammaImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rv_mem_value_fibre_iff (δ : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M) :
    t.val ∈ Values.gammaPullback {δ} ↔ Values.vrv t = δ.val := by
  constructor
  · rintro ⟨hr,h0,hmem⟩
    have he : Values.gammaOf ⟨t.val,hr⟩ h0 = δ := Set.mem_singleton_iff.mp hmem
    exact congrArg Subtype.val he
  · intro he
    have hn : t.val ≠ iRVZero := by
      intro hz
      exact δ.property (he.symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz))
    refine ⟨t.property,hn,?_⟩
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact he

/-- A temporary representative is used only to prove finiteness of the
image on a value slice. It is not adjoined to the conclusion's ground. -/
theorem rv_value_slice_gamma_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (f : D → Values.Gamma (M := M))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ ∃ d : D, d.val = z 1 ∧ f d = codeValue (z 0)})
    (δ : Values.Gamma (M := M)) :
    (Set.range (fun d : ↥(D ∩ Values.gammaPullback {δ}) => f ⟨d.val,d.property.1⟩)).Finite := by
  let a := raw (representative δ)
  let C : GammaParameters.Base (M := M) := ⟨insert a B.real,B.gamma⟩
  let V := Values.gammaPullback {δ}
  let E := D ∩ V
  let g (d : E) := f ⟨d.val,d.property.1⟩
  have hV : GammaParameters.DefinableAtBase C .rv V :=
    real_definableAtBase C .rv V (value_fibre_domain_definable B.real δ)
  have hDC : GammaParameters.DefinableAtBase C .rv D := hD.mono (Set.subset_insert a _) Set.Subset.rfl
  have hE : GammaParameters.DefinableAtBase C .rv E := hDC.inter hV
  have hfC := hf.mono (C := C) (Set.subset_insert a _) Set.Subset.rfl
  have hv2 := hV.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (1 : Fin 2))
  have hg : GammaParameters.DefinableOverBase C (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ ∃ d : E, d.val = z 1 ∧ g d = codeValue (z 0)} := by
    have hi := hfC.inter hv2
    convert hi using 1
    ext z
    constructor
    · rintro ⟨hn,d,hd,hg⟩
      have hold : NonzeroRV (z 0) ∧ ∃ d : D, d.val = z 1 ∧ f d = codeValue (z 0) :=
        ⟨hn,⟨d.val,d.property.1⟩,hd,hg⟩
      refine ⟨hold,?_,hfC.proper z hold⟩
      change z 1 ∈ V
      exact hd ▸ d.property.2
    · rintro ⟨⟨hn,d,hd,hf⟩,hv,_⟩
      have hv' : z 1 ∈ V := hv
      have hdV : d.val ∈ V := hd.symm ▸ hv'
      exact ⟨hn,⟨d.val,d.property,hdV⟩,hd,hf⟩
  exact rv_value_fibre_gamma_image_finite hκ hs h00 C (small_insert hκ B.real hsmall a)
    E hE δ (fun t ht => (rv_mem_value_fibre_iff δ t).mp ht.2) g hg

/-- Finite value support makes every definable Gamma-valued unary RV
function have finite image, including its possible zero RV argument. -/
theorem rv_finite_value_support_gamma_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite)
    (f : D → Values.Gamma (M := M))
    (hf : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ ∃ d : D, d.val = z 1 ∧ f d = codeValue (z 0)}) :
    (Set.range f).Finite := by
  let G : Set (Values.Gamma (M := M)) := {δ | δ.val ∈ Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}}
  have hG : G.Finite := hvalues.preimage Subtype.val_injective.injOn
  let H (δ : Values.Gamma (M := M)) := Set.range (fun d : ↥(D ∩ Values.gammaPullback {δ}) => f ⟨d.val,d.property.1⟩)
  have hH (δ : Values.Gamma (M := M)) : (H δ).Finite :=
    rv_value_slice_gamma_image_finite hκ hs h00 B hsmall D hD f hf δ
  let Z : Set D := {d | d.val = iRVZero}
  have hZ : Z.Finite := (Set.finite_singleton iRVZero).preimage Subtype.val_injective.injOn
  apply ((hG.biUnion (fun δ _ => hH δ)).union (hZ.image f)).subset
  rintro _ ⟨d,rfl⟩
  let t : CanonicalRV.RVSort M := ⟨d.val,hD.proper d.val d.property⟩
  by_cases hz : d.val = iRVZero
  · exact Or.inr ⟨d,hz,rfl⟩
  · have hval : Values.vrv t ≠ Values.infinity := fun he => hz ((Values.vrv_eq_infinity_iff t).mp he)
    let δ : Values.Gamma (M := M) := ⟨Values.vrv t,hval⟩
    have hδG : δ ∈ G := ⟨t,d.property,rfl⟩
    have hdδ : d.val ∈ Values.gammaPullback {δ} := (rv_mem_value_fibre_iff δ t).mpr rfl
    exact Or.inl (Set.mem_iUnion.mpr ⟨δ,Set.mem_iUnion.mpr ⟨hδG,⟨⟨d.val,d.property,hdδ⟩,rfl⟩⟩⟩)
end DiamondIntegral.Section3
