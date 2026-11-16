import «section 6».MixedSetParameterTemplates

/-! Intermediate source and protected-piece images are computed by
first-order existential projection of complete transition relations.
The specialization is the literal image of the actual restricted map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι τ σ : Type} [Finite ι] [Finite τ] [Finite σ]

def parameterRelationImage (A : Set (ι ⊕ τ → M)) (R : Set (ι ⊕ (τ ⊕ σ) → M)) : Set (ι ⊕ σ → M) :=
  {z | ∃ x : τ → M,Sum.elim (z ∘ Sum.inl) (Sum.elim x (z ∘ Sum.inr)) ∈ R ∧
    Sum.elim (z ∘ Sum.inl) x ∈ A}

theorem parameterRelationImage_definable (A : Set (ι ⊕ τ → M)) (R : Set (ι ⊕ (τ ⊕ σ) → M))
    (hA : S.Definable LRV A) (hR : S.Definable LRV R) : S.Definable LRV (parameterRelationImage A R) := by
  let Z := (ι ⊕ σ) ⊕ τ
  have hRCode : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (z ∘ Sum.inr) (fun j => z (.inl (.inr j))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have hACode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i))) (z ∘ Sum.inr)) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  exact ((hR.preimage_map hRCode).inter (hA.preimage_map hACode)).exists_of_finite

theorem parameterRelationImage_at_restriction
    {P Q : SpecialTransformations.DefinableGeometry.Space LRV M} (a : ι → M)
    (C₀ : Set (ι ⊕ P.Index → M)) (R : Set (ι ⊕ (P.Index ⊕ Q.Index) → M))
    {A B : DefSet P (S ∪ Set.range a)} {D : DefSet Q (S ∪ Set.range a)}
    (f : Map A D) (hBA : B.carrier ⊆ A.carrier)
    (hSource : {z | Sum.elim a z ∈ C₀}=P.preimage B.carrier)
    (hGraph : {z | Sum.elim a z ∈ R}=P.relation Q f.graph) :
    {z : Q.Index → M | Sum.elim a z ∈ parameterRelationImage C₀ R}=
      Q.preimage (f.restrict hBA).image.carrier := by
  ext z
  constructor
  · rintro ⟨x,hR,hC⟩
    obtain ⟨hx,hy,p,hp,hf⟩ := (Set.ext_iff.mp hGraph _).mp hR
    obtain ⟨hx',hB⟩ := (Set.ext_iff.mp hSource _).mp hC
    have hpB : p.val ∈ B.carrier := hp.symm ▸ hB
    exact ⟨hy,⟨⟨p.val,hpB⟩,hf⟩⟩
  · rintro ⟨hz,q,hq⟩
    obtain ⟨c,hc⟩ := P.onto q.val
    have hRel : Sum.elim c.val z ∈ P.relation Q f.graph :=
      (P.relation_decode Q f.graph c ⟨z,hz⟩).mpr ⟨⟨q.val,hBA q.property⟩,hc.symm,hq⟩
    have hC : c.val ∈ P.preimage B.carrier := (P.preimage_decode B.carrier c).mpr (hc.symm ▸ q.property)
    exact ⟨c.val,(Set.ext_iff.mp hGraph _).mpr hRel,(Set.ext_iff.mp hSource _).mpr hC⟩

end DiamondIntegral.Section6
