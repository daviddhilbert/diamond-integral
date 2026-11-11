import «section 2».GammaFamilyProjections
import «section 2».GammaDomainSuprema

/-! A unary RV map grouped by its input value. The value-domain and
output family have full original-base graphs containing all Gamma codes. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem sameScalar_iff_codeValue_eq (a b : M) (ha : GammaParameters.NonzeroRV a)
    (hb : GammaParameters.NonzeroRV b) :
    GammaParameters.SameScalar a b ↔ GammaParameters.codeValue a = GammaParameters.codeValue b := by
  constructor
  · intro h
    exact le_antisymm ((GammaParameters.original_le_codeValue_iff a b ha hb).mp h.2.2.1)
      ((GammaParameters.original_le_codeValue_iff b a hb ha).mp h.2.2.2)
  · intro he
    refine ⟨ha,hb,?_,?_⟩
    · exact (GammaParameters.original_le_codeValue_iff a b ha hb).mpr he.le
    · exact (GammaParameters.original_le_codeValue_iff b a hb ha).mpr he.ge

def rvValueDomain (D : Set M) : Set (Gamma M) :=
  {γ | ∃ t ∈ D, GammaParameters.NonzeroRV t ∧ GammaParameters.codeValue t = γ}

def rvValueFamily (D : Set M) (f : M → Gamma M) (γ : Gamma M) : Set (Gamma M) :=
  f '' {t | t ∈ D ∧ GammaParameters.NonzeroRV t ∧ GammaParameters.codeValue t = γ}

def rvValueSource (D : Set M) : Set (Fin 2 → M) :=
  {x | x 1 ∈ D ∧ GammaParameters.SameScalar (x 0) (x 1)}

theorem rvValueSource_definable (S D : Set M) (hD : S.Definable₁ LRV D) :
    S.Definable LRV (rvValueSource D) :=
  (hD.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))).inter (GammaParameters.same_scalar_definable S)

theorem rvValueSource_projection (D : Set M) :
    (fun x : Fin 2 → M => x ∘ (fun _ : Fin 1 => (0 : Fin 2))) '' rvValueSource D =
      gammaDomainCodes (rvValueDomain D) := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    have h0 : x 0 = y 0 := congrFun hxy 0
    refine ⟨h0 ▸ hx.2.1,x 1,hx.1,hx.2.2.1,?_⟩
    rw [← h0]
    exact ((sameScalar_iff_codeValue_eq (x 0) (x 1) hx.2.1 hx.2.2.1).mp hx.2).symm
  · rintro ⟨hyNZ,t,htD,htNZ,hty⟩
    refine ⟨![y 0,t],⟨htD,(sameScalar_iff_codeValue_eq (y 0) t hyNZ htNZ).mpr hty.symm⟩,?_⟩
    funext j
    fin_cases j
    rfl

theorem rvValueDomain_codes_definable (S D : Set M) (hD : S.Definable₁ LRV D) :
    S.Definable LRV (gammaDomainCodes (rvValueDomain D)) := by
  rw [← rvValueSource_projection]
  exact (rvValueSource_definable S D hD).image_comp (fun _ : Fin 1 => (0 : Fin 2))

theorem rvValueSource_graph_definable (S D : Set M) (f : M → Gamma M)
    (hf : S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ D} (fun x => {f (x 0)}))) :
    S.Definable LRV (rawGammaFamilyGraph (rvValueSource D) (fun x => {f (x 1)})) := by
  let idx : Fin 1 ⊕ Fin 1 → Fin 2 ⊕ Fin 1 := Sum.elim (fun _ => .inl 1) Sum.inr
  have hSame := (GammaParameters.same_scalar_definable S).preimage_comp (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 1)
  convert (hf.preimage_comp idx).inter hSame using 1
  ext z
  change ((_ ∧ _) ∧ _ ∧ _) ↔ ((_ ∧ _ ∧ _) ∧ _)
  tauto

theorem projectedGammaFamily_value_eq (D : Set M) (f : M → Gamma M) (y : Fin 1 → M)
    (hy : y ∈ gammaDomainCodes (rvValueDomain D)) :
    projectedGammaFamily (rvValueSource D) (fun x => {f (x 1)}) (fun _ : Fin 1 => (0 : Fin 2)) y =
      rvValueFamily D f (GammaParameters.codeValue (y 0)) := by
  ext γ
  constructor
  · rintro ⟨x,hx,hxy,hfγ⟩
    have h0 : x 0 = y 0 := congrFun hxy 0
    have he := ((sameScalar_iff_codeValue_eq (x 0) (x 1) hx.2.1 hx.2.2.1).mp hx.2).symm
    refine ⟨x 1,⟨hx.1,hx.2.2.1,?_⟩,hfγ.symm⟩
    rwa [h0] at he
  · rintro ⟨t,⟨htD,htNZ,hty⟩,hfγ⟩
    refine ⟨![y 0,t],⟨htD,(sameScalar_iff_codeValue_eq (y 0) t hy.1 htNZ).mpr hty.symm⟩,?_,hfγ.symm⟩
    funext j
    fin_cases j
    rfl

theorem rvValueFamily_graph_definable (S D : Set M) (f : M → Gamma M)
    (hf : S.Definable LRV (rawGammaFamilyGraph {x : Fin 1 → M | x 0 ∈ D} (fun x => {f (x 0)}))) :
    S.Definable LRV (rawGammaFamilyGraph (gammaDomainCodes (rvValueDomain D))
      (fun x => rvValueFamily D f (GammaParameters.codeValue (x 0)))) := by
  have h := rawGammaFamilyGraph_source_projection_definable S (rvValueSource D) (fun x => {f (x 1)})
    (rvValueSource_graph_definable S D f hf) (fun _ : Fin 1 => (0 : Fin 2))
  rw [rvValueSource_projection] at h
  convert h using 1
  ext z
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  by_cases hz : z ∘ Sum.inl ∈ gammaDomainCodes (rvValueDomain D)
  · rw [projectedGammaFamily_value_eq D f (z ∘ Sum.inl) hz]
  · simp only [hz,false_and]

end DiamondIntegral.Section2
