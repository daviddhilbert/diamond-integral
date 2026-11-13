import Section3.GammaRVSeparation
import Section3.RVFibreGeometry
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem gammaRV_row_definable (F : GammaRVFamily (M := M) S) (γ : Values.Gamma (M := M)) :
    DefinableAt (insert (raw (representative γ)) S) .rv {t | F.relation γ t} := by
  let a := raw (representative γ)
  let T := insert a S
  let R : Set M := {t | F.relation γ t}
  have ha : NonzeroRV a := ⟨raw_rv _,raw_ne_zero _⟩
  have hv : codeValue a = γ := (codeValue_raw _).trans (representative_value γ)
  have he : {t | F.rawRelation a t} = R := by
    ext t
    change (NonzeroRV a ∧ F.relation (codeValue a) t) ↔ F.relation γ t
    rw [hv,and_iff_right ha]
  have hfd := F.definable
  have hd : @Set.Definable₁ M T LRV (CanonicalStructure.normalize (M := M)) {t | F.rawRelation a t} := by
    letI := CanonicalStructure.normalize (M := M)
    have hmap : T.DefinableMap LRV (fun z : Fin 1 → M => ![a,z 0]) := by
      intro i
      fin_cases i
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert a S)
      · exact Set.DefinableFun.proj LRV
    exact (hfd.mono (Set.subset_insert a S)).preimage_map hmap
  apply (definableAt_iff_normalized_raw T .rv R).mpr
  exact ⟨he ▸ hd,fun _ h => F.sorted γ _ h⟩

/-- A Gamma-indexed definable cut of one actual RV value fibre has a
finite side. This is checked strong minimality of that fibre in ACVF. -/
theorem gammaRV_value_fibre_dichotomy (F : GammaRVFamily (M := M) S) (D : Set M)
    (hD : DefinableAt S .rv D) (δ : Values.Gamma (M := M))
    (hδ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = δ.val)
    (hsub : ∀ γ t, F.relation γ t → t ∈ D) :
    ∀ γ, {t | F.relation γ t}.Finite ∨ {t | t ∈ D ∧ ¬ F.relation γ t}.Finite := by
  intro γ
  have hr := gammaRV_row_definable F γ
  rcases rv_value_fibre_finite_or_cofinite _ _ hr δ with h | h
  · left
    apply (h.image Subtype.val).subset
    intro t ht
    exact ⟨⟨t,F.sorted γ t ht⟩,⟨hδ _ (hsub γ t ht),ht⟩,rfl⟩
  · right
    apply (h.image Subtype.val).subset
    rintro t ⟨ht,hn⟩
    exact ⟨⟨t,hD.2 ht⟩,⟨hδ _ ht,hn⟩,rfl⟩
end DiamondIntegral.Section3
