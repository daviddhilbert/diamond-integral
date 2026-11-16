import «section 6».GammaNameParameterTemplates
import Section3.GammaBaseTools
import Section3.TupleCompactness

/-! Named Gamma values promote to actual original-base templates with
definable admissibility. Compactness selects finitely many complete
names without adjoining a real representative of any Gamma value. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

theorem GammaNameParameterTemplate.good_of_name
    (T : GammaNameParameterTemplate (M := M) S p) (a : Fin p → M) (γ : Gamma M)
    (hSection : {z : Fin 1 → M | Sum.elim a z ∈ T.graph}=
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) : a ∈ T.good := by
  obtain ⟨t,ht,hγ⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
  refine ⟨⟨fun _ => t,(Set.ext_iff.mp hSection _).mpr
    ((GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr hγ)⟩,?_⟩
  intro x y hx hy
  have hx' := (Set.ext_iff.mp hSection x).mp hx
  have hy' := (Set.ext_iff.mp hSection y).mp hy
  have hxnz := T.proper _ hx
  have hynz := T.proper _ hy
  have hEq : GammaParameters.codeValue (x 0)=GammaParameters.codeValue (y 0) :=
    ((GammaParameters.gammaPullback_mem_codeValue_iff _ _ hxnz).mp hx').trans
      ((GammaParameters.gammaPullback_mem_codeValue_iff _ _ hynz).mp hy').symm
  exact ⟨hxnz,hynz,(GammaParameters.original_le_codeValue_iff _ _ hxnz hynz).mpr hEq.le,
    (GammaParameters.original_le_codeValue_iff _ _ hynz hxnz).mpr hEq.ge⟩

theorem GammaNameParameterTemplate.value_of_name
    (T : GammaNameParameterTemplate (M := M) S p) (a : Fin p → M) (ha : a ∈ T.good) (γ : Gamma M)
    (hSection : {z : Fin 1 → M | Sum.elim a z ∈ T.graph}=
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) : T.value a ha=γ := by
  have hx := (Set.ext_iff.mp hSection _).mp ha.1.choose_spec
  exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ (T.proper _ ha.1.choose_spec)).mp hx

theorem exists_promoted_gamma_name_template (a : Fin p → M) (γ : Gamma M)
    (hγ : (S ∪ Set.range a).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    ∃ T : GammaNameParameterTemplate (M := M) S p,a ∈ T.good ∧
      {z : Fin 1 → M | Sum.elim a z ∈ T.graph}={z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}} := by
  obtain ⟨R,hR,hSection⟩ := SpecialTransformations.ModelTheory.promote_definable_tuple_fibre LRV S a
    {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}} hγ
  let H : Set (Fin p ⊕ Fin 1 → M) := {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}
  let W := H ∩ {z | GammaParameters.NonzeroRV (z (.inr 0))}
  have hW : S.Definable LRV W := hR.inter
    ((GammaParameters.nonzero_rv_definable S).preimage_comp (Sum.inr : Fin 1 → Fin p ⊕ Fin 1))
  let T : GammaNameParameterTemplate (M := M) S p := ⟨W,hW,fun _ h => h.2⟩
  have hT : {z : Fin 1 → M | Sum.elim a z ∈ T.graph}=
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}} := by
    ext z
    have hAt : (a,z) ∈ R ↔ z 0 ∈ Values.gammaPullback {γ} := Set.ext_iff.mp hSection z
    constructor
    · intro hz
      exact hAt.mp hz.1
    · intro hz
      exact ⟨hAt.mpr hz,hz.1,hz.2.1⟩
  exact ⟨T,T.good_of_name a γ hT,hT⟩

theorem exists_finite_gamma_name_templates
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin p → M)) (hA : S.Definable LRV A)
    (hLocal : ∀ a ∈ A,∃ γ : Gamma M,(S ∪ Set.range a).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    ∃ k : ℕ,∃ T : Fin k → GammaNameParameterTemplate (M := M) S p,∀ a ∈ A,∃ i,a ∈ (T i).good := by
  let C := Set.range (fun T : GammaNameParameterTemplate (M := M) S p => T.good)
  have hC : ∀ c ∈ C,S.Definable LRV c := by rintro c ⟨T,rfl⟩; exact T.good_definable
  have hCover (a) (ha : a ∈ A) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨γ,hγ⟩ := hLocal a ha
    obtain ⟨T,hT,_⟩ := exists_promoted_gamma_name_template a γ hγ
    exact ⟨T.good,⟨T,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall A hA C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).good=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => chooseT (e.symm i),?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).good
  rw [e.symm_apply_apply,hT]
  exact hac

end DiamondIntegral.Section6
