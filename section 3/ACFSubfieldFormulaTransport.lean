import «section 3».ACFDefinableRelationFields
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CompatibleRing K]

/-- Pure-field formulas over E are preserved by embeddings of an
intermediate field into the same algebraically closed ambient field.
The embedding need not extend to an automorphism of the ambient field. -/
theorem acf_formula_intermediate_embedding (E : Subfield K)
    (F : IntermediateField E K) (σ : F →ₐ[E] K) {ι : Type}
    (φ : Language.ring.Formula (E ⊕ ι)) (x : ι → F) :
    φ.Realize (Sum.elim E.subtype (fun i => (x i : K))) ↔
      φ.Realize (Sum.elim E.subtype (fun i => σ (x i))) := by
  obtain ⟨ψ,hψ,he⟩ := ProvedACFExtension.fullQE (E ⊕ ι) 0 φ
  let v : E ⊕ ι → ProvedACFExtension.subfieldSubstructure F.toSubfield :=
    Sum.elim (fun e => algebraMap E F e) x
  let inc := ProvedACFExtension.subfieldEmbedding F.toSubfield F.toSubfield.subtype
  let emb := ProvedACFExtension.subfieldEmbedding F.toSubfield σ.toRingHom
  have hinc : inc ∘ v = Sum.elim E.subtype (fun i => (x i : K)) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => rfl
  have hemb : emb ∘ v = Sum.elim E.subtype (fun i => σ (x i)) := by
    funext i
    cases i with
    | inl i => exact σ.commutes i
    | inr i => rfl
  have hz₁ : inc ∘ (default : Fin 0 → ProvedACFExtension.subfieldSubstructure F.toSubfield) =
      (default : Fin 0 → K) := Subsingleton.elim _ _
  have hz₂ : emb ∘ (default : Fin 0 → ProvedACFExtension.subfieldSubstructure F.toSubfield) =
      (default : Fin 0 → K) := Subsingleton.elim _ _
  have hi := hψ.realize_embedding inc (v := v)
    (xs := (default : Fin 0 → ProvedACFExtension.subfieldSubstructure F.toSubfield))
  have hs := hψ.realize_embedding emb (v := v)
    (xs := (default : Fin 0 → ProvedACFExtension.subfieldSubstructure F.toSubfield))
  rw [hinc,hz₁] at hi
  rw [hemb,hz₂] at hs
  exact (he K inferInstance _ _).trans ((hi.trans hs.symm).trans (he K inferInstance _ _).symm)

/-- The corresponding relation-level transport uses the actual checked
field QE theorem and fixes every coefficient in E. -/
theorem acf_definable_intermediate_embedding (E : Subfield K)
    (F : IntermediateField E K) (σ : F →ₐ[E] K) {ι : Type}
    (R : Set (ι → K)) (hR : (E : Set K).Definable Language.ring R) (x : ι → F) :
    (fun i => (x i : K)) ∈ R ↔ (fun i => σ (x i)) ∈ R := by
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hR
  exact (Set.ext_iff.mp hφ _).trans
    ((acf_formula_intermediate_embedding E F σ φ x).trans (Set.ext_iff.mp hφ _).symm)

end DiamondIntegral.Section3
