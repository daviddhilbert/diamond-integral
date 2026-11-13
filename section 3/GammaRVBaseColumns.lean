import «section 3».GammaRVFiniteColumns
import «section 3».IntegrationGammaParameters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gammaRVBase_finite_columns {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (R : Values.Gamma (M := M) → M → Prop)
    (hsort : ∀ γ t, R γ t → iRV t)
    (hR : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | NonzeroRV (z 0) ∧ R (codeValue (z 0)) (z 1)})
    (D : Set M) (hD : GammaParameters.DefinableAtBase B .rv D)
    (δ : Values.Gamma (M := M))
    (hδ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = δ.val)
    (hsub : ∀ γ t, R γ t → t ∈ D) : (relationColumn R '' D).Finite := by
  obtain ⟨n,t,hrt⟩ := hR.specialize
  have hDtuple : GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ D} := hD
  obtain ⟨m,u,hdu⟩ := hDtuple.specialize
  let S := (B.real ∪ Set.range (rawTuple t)) ∪ Set.range (rawTuple u)
  have hST : B.real ∪ Set.range (rawTuple t) ⊆ S := Set.subset_union_left
  have hSU : B.real ∪ Set.range (rawTuple u) ⊆ S :=
    Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right
  have hS : Cardinal.mk S < κ :=
    small_union_range hκ _ (small_union_range hκ B.real hsmall (rawTuple t)) (rawTuple u)
  have hr := (definableOver_iff_normalized_raw _ (fun _ : Fin 2 => .rv) _).mp hrt |>.1
  have hd := (definableOver_iff_normalized_raw _ (fun _ : Fin 1 => .rv) _).mp hdu |>.1
  have hrS : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | NonzeroRV p.1 ∧ R (codeValue p.1) p.2} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hr.mono hST
  have hdS : @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M)) D := by
    letI := CanonicalStructure.normalize (M := M)
    exact hd.mono hSU
  let F : GammaRVFamily (M := M) S := ⟨R,hsort,hrS⟩
  have hDreal : DefinableAt S .rv D :=
    (definableAt_iff_normalized_raw S .rv D).mpr ⟨hdS,hD.proper⟩
  exact gammaRV_value_fibre_finite_columns hκ hs h00 hS F D hDreal δ hδ hsub
end DiamondIntegral.Section3
