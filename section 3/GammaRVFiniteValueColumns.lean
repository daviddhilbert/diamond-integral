import «section 3».GammaRVBaseColumns
import «section 3».RVFiniteValueGammaImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gammaRVBase_value_slice_finite_columns {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (R : Values.Gamma (M := M) → M → Prop) (hsort : ∀ γ t, R γ t → iRV t)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (δ : Values.Gamma (M := M)) :
    (relationColumn R '' (D ∩ Values.gammaPullback {δ})).Finite := by
  let a := raw (representative δ)
  let C : GammaParameters.Base (M := M) := ⟨insert a B.real,B.gamma⟩
  let V := Values.gammaPullback {δ}
  let E := D ∩ V
  let R' (γ : Values.Gamma (M := M)) (t : M) := t ∈ E ∧ R γ t
  have hV : GammaParameters.DefinableAtBase C .rv V :=
    real_definableAtBase C .rv V (value_fibre_domain_definable B.real δ)
  have hE : GammaParameters.DefinableAtBase C .rv E :=
    (hD.mono (C := C) (Set.subset_insert a _) Set.Subset.rfl).inter hV
  have hRC := hR.mono (C := C) (Set.subset_insert a _) Set.Subset.rfl
  have he2 := hE.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (1 : Fin 2))
  have hR' : GammaParameters.DefinableOverBase C (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R' (codeValue (z 0)) (z 1)} := by
    have hi := hRC.inter he2
    convert hi using 1
    ext z
    constructor
    · rintro ⟨hn,hE,hR⟩
      exact ⟨⟨hn,hR⟩,hE,hRC.proper z ⟨hn,hR⟩⟩
    · rintro ⟨⟨hn,hR⟩,hE,_⟩
      exact ⟨hn,hE,hR⟩
  have hfin := gammaRVBase_finite_columns hκ hs h00 C (small_insert hκ B.real hsmall a)
    R' (fun γ t h => hsort γ t h.2) hR' E hE δ
    (fun t ht => (rv_mem_value_fibre_iff δ t).mp ht.2) (fun _ _ h => h.1)
  have he : relationColumn R '' E = relationColumn R' '' E := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t,ht,rfl⟩
      exact ⟨t,ht,Set.ext (fun γ => and_iff_right ht)⟩
    · rintro _ ⟨t,ht,rfl⟩
      exact ⟨t,ht,(Set.ext (fun γ => and_iff_right ht)).symm⟩
  exact he.symm ▸ hfin

/-- Unary finite-value-support RV sets have finitely many Gamma columns.
Temporary names used in finiteness proofs do not enter this conclusion. -/
theorem gammaRVBase_finite_value_columns {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (R : Values.Gamma (M := M) → M → Prop) (hsort : ∀ γ t, R γ t → iRV t)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (hvalues : (Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}).Finite) :
    (relationColumn R '' D).Finite := by
  let G : Set (Values.Gamma (M := M)) := {δ | δ.val ∈ Values.vrv '' {t : CanonicalRV.RVSort M | t.val ∈ D}}
  have hG : G.Finite := hvalues.preimage Subtype.val_injective.injOn
  let H (δ : Values.Gamma (M := M)) := relationColumn R '' (D ∩ Values.gammaPullback {δ})
  have hH (δ : Values.Gamma (M := M)) : (H δ).Finite :=
    gammaRVBase_value_slice_finite_columns hκ hs h00 B hsmall R hsort hR D hD δ
  let Z : Set M := D ∩ {iRVZero}
  have hZ : Z.Finite := (Set.finite_singleton iRVZero).subset (fun _ h => h.2)
  apply ((hG.biUnion (fun δ _ => hH δ)).union (hZ.image (relationColumn R))).subset
  rintro _ ⟨x,hx,rfl⟩
  let t : CanonicalRV.RVSort M := ⟨x,hD.proper x hx⟩
  by_cases hz : x = iRVZero
  · exact Or.inr ⟨x,⟨hx,hz⟩,rfl⟩
  · have hn : Values.vrv t ≠ Values.infinity := fun he => hz ((Values.vrv_eq_infinity_iff t).mp he)
    let δ : Values.Gamma (M := M) := ⟨Values.vrv t,hn⟩
    have hd : δ ∈ G := ⟨t,hx,rfl⟩
    have hxδ : x ∈ Values.gammaPullback {δ} := (rv_mem_value_fibre_iff δ t).mpr rfl
    exact Or.inl (Set.mem_iUnion.mpr ⟨δ,Set.mem_iUnion.mpr ⟨hd,⟨x,⟨hx,hxδ⟩,rfl⟩⟩⟩)
end DiamondIntegral.Section3
