import «section 6».ParameterRelationImages

/-! Complete transition templates compose by quantifying the actual
intermediate real codes. Specialization is the exact graph of the
composite map, retaining every representative of the intermediate point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι τ σ υ : Type} [Finite ι] [Finite τ] [Finite σ] [Finite υ]

def parameterRelationComp (F : Set (ι ⊕ (τ ⊕ σ) → M)) (H : Set (ι ⊕ (σ ⊕ υ) → M)) :
    Set (ι ⊕ (τ ⊕ υ) → M) :=
  {z | ∃ y : σ → M,Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i))) y) ∈ F ∧
    Sum.elim (z ∘ Sum.inl) (Sum.elim y (fun i => z (.inr (.inr i)))) ∈ H}

theorem parameterRelationComp_definable (F : Set (ι ⊕ (τ ⊕ σ) → M))
    (H : Set (ι ⊕ (σ ⊕ υ) → M)) (hF : S.Definable LRV F) (hH : S.Definable LRV H) :
    S.Definable LRV (parameterRelationComp F H) := by
  let Z := (ι ⊕ (τ ⊕ υ)) ⊕ σ
  have hLeft : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (fun i => z (.inl (.inr (.inl i)))) (z ∘ Sum.inr))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have hRight : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (z ∘ Sum.inr) (fun i => z (.inl (.inr (.inr i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  exact ((hF.preimage_map hLeft).inter (hH.preimage_map hRight)).exists_of_finite

theorem parameterRelationComp_at
    {P Q R : SpecialTransformations.DefinableGeometry.Space LRV M} (a : ι → M)
    (F : Set (ι ⊕ (P.Index ⊕ Q.Index) → M)) (H : Set (ι ⊕ (Q.Index ⊕ R.Index) → M))
    {A : DefSet P (S ∪ Set.range a)} {B : DefSet Q (S ∪ Set.range a)} {C : DefSet R (S ∪ Set.range a)}
    (f : Map A B) (g : Map B C)
    (hF : {z | Sum.elim a z ∈ F}=P.relation Q f.graph)
    (hH : {z | Sum.elim a z ∈ H}=Q.relation R g.graph) :
    {z | Sum.elim a z ∈ parameterRelationComp F H}=P.relation R (g.comp f).graph := by
  ext z
  constructor
  · rintro ⟨y,hyF,hyH⟩
    obtain ⟨hx,hm,p,hp,hfp⟩ := (Set.ext_iff.mp hF _).mp hyF
    obtain ⟨hm',hz,q,hq,hgq⟩ := (Set.ext_iff.mp hH _).mp hyH
    have hEq : f p=q := Subtype.ext (hfp.trans hq.symm)
    exact ⟨hx,hz,p,hp,(congrArg (fun b : B => (g b).val) hEq).trans hgq⟩
  · rintro ⟨hx,hz,p,hp,hTarget⟩
    obtain ⟨c,hc⟩ := Q.onto (f p).val
    have hLeft : Sum.elim (z ∘ Sum.inl) c.val ∈ P.relation Q f.graph :=
      (P.relation_decode Q f.graph ⟨z ∘ Sum.inl,hx⟩ c).mpr ⟨p,hp,hc.symm⟩
    have hRight : Sum.elim c.val (z ∘ Sum.inr) ∈ Q.relation R g.graph :=
      (Q.relation_decode R g.graph c ⟨z ∘ Sum.inr,hz⟩).mpr ⟨f p,hc.symm,hTarget⟩
    exact ⟨c.val,(Set.ext_iff.mp hF _).mpr hLeft,(Set.ext_iff.mp hH _).mpr hRight⟩

end DiamondIntegral.Section6
