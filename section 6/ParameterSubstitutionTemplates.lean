import «section 6».FocusComponentParameterTemplates

/-! Definable substitution of the real parameter tuple in complete
family formulas. This permits freezing an entire remaining program at
once, retaining its domains, focus formulas and named metadata. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r m k : ℕ}
variable {ι : Type} [Finite ι]

structure DefinableParameterSubstitution (S : Set M) (p q : ℕ) where
  value : (Fin q → M) → Fin p → M
  definable : S.DefinableMap LRV value

def parameterSubstitutionCode (h : DefinableParameterSubstitution (M := M) S p q)
    (z : Fin q ⊕ ι → M) : Fin p ⊕ ι → M := Sum.elim (h.value (z ∘ Sum.inl)) (z ∘ Sum.inr)

theorem parameterSubstitutionCode_definable (h : DefinableParameterSubstitution (M := M) S p q) :
    S.DefinableMap LRV (parameterSubstitutionCode (ι := ι) h) := by
  rintro (i | i)
  · exact (h.definable i).comp (fun _ => Set.DefinableFun.proj LRV)
  · exact Set.DefinableFun.proj LRV

def parameterSubstitution (h : DefinableParameterSubstitution (M := M) S p q)
    (R : Set (Fin p ⊕ ι → M)) : Set (Fin q ⊕ ι → M) := parameterSubstitutionCode h ⁻¹' R

theorem parameterSubstitution_definable (h : DefinableParameterSubstitution (M := M) S p q)
    (R : Set (Fin p ⊕ ι → M)) (hR : S.Definable LRV R) : S.Definable LRV (parameterSubstitution h R) :=
  hR.preimage_map (parameterSubstitutionCode_definable h)

theorem parameterSubstitution_at (h : DefinableParameterSubstitution (M := M) S p q)
    (R : Set (Fin p ⊕ ι → M)) (a : Fin q → M) :
    {z | Sum.elim a z ∈ parameterSubstitution h R}={z | Sum.elim (h.value a) z ∈ R} := rfl

def MixedSetParameterTemplate.substitute (T : MixedSetParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) : MixedSetParameterTemplate (M := M) S q n r :=
  ⟨parameterSubstitution h T.graph,parameterSubstitution_definable h _ T.definable⟩

theorem MixedSetParameterTemplate.substitute_carrier (T : MixedSetParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) (a : Fin q → M) :
    ((T.substitute h).fibre a).carrier=(T.fibre (h.value a)).carrier := rfl

def RVSetParameterTemplate.substitute (T : RVSetParameterTemplate (M := M) S p r)
    (h : DefinableParameterSubstitution (M := M) S p q) : RVSetParameterTemplate (M := M) S q r :=
  ⟨parameterSubstitution h T.graph,parameterSubstitution_definable h _ T.definable⟩

def ContinuousVFGraphTemplate.substitute (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (h : DefinableParameterSubstitution (M := M) S p q) : ContinuousVFGraphTemplate (M := M) S q n m :=
  ⟨parameterSubstitution h T.graph,parameterSubstitution_definable h _ T.definable,
    fun z hz => T.sorted (parameterSubstitutionCode h z) hz⟩

def ContinuousRVGraphTemplate.substitute (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (h : DefinableParameterSubstitution (M := M) S p q) : ContinuousRVGraphTemplate (M := M) S q r n m :=
  ⟨parameterSubstitution h T.graph,parameterSubstitution_definable h _ T.definable,
    fun z hz => T.sorted (parameterSubstitutionCode h z) hz⟩

def GammaNameParameterTemplate.substitute (T : GammaNameParameterTemplate (M := M) S p)
    (h : DefinableParameterSubstitution (M := M) S p q) : GammaNameParameterTemplate (M := M) S q :=
  ⟨parameterSubstitution h T.graph,parameterSubstitution_definable h _ T.definable,
    fun z hz => T.proper (parameterSubstitutionCode h z) hz⟩

theorem ContinuousVFGraphTemplate.substitute_good (T : ContinuousVFGraphTemplate (M := M) S p n m)
    (h : DefinableParameterSubstitution (M := M) S p q) : (T.substitute h).good=h.value ⁻¹' T.good := by
  ext a
  rfl

theorem ContinuousRVGraphTemplate.substitute_good (T : ContinuousRVGraphTemplate (M := M) S p r n m)
    (h : DefinableParameterSubstitution (M := M) S p q) : (T.substitute h).good=h.value ⁻¹' T.good := by
  ext a
  rfl

theorem GammaNameParameterTemplate.substitute_good (T : GammaNameParameterTemplate (M := M) S p)
    (h : DefinableParameterSubstitution (M := M) S p q) : (T.substitute h).good=h.value ⁻¹' T.good := by
  ext a
  rfl

def FocusComponentParameterTemplate.substitute (T : FocusComponentParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q) : FocusComponentParameterTemplate (M := M) S q n r :=
  ⟨T.coordinate,T.active.substitute h,T.focus.substitute h,T.coefficient.substitute h,T.radius.substitute h⟩

theorem FocusComponentParameterTemplate.substitute_good (T : FocusComponentParameterTemplate (M := M) S p n r)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (T.substitute h).good (A.substitute h) (fun i => (P i).substitute h)=h.value ⁻¹' T.good A P := by
  ext a
  simp only [FocusComponentParameterTemplate.good, FocusComponentParameterTemplate.geometricLocus,
    FocusComponentParameterTemplate.substitute, focusMetadataParameterLocus,
    Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage]
  rfl

end DiamondIntegral.Section6
