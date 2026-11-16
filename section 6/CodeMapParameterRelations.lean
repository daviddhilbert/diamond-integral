import «section 6».MixedRelationImageTemplates

/-! Complete first-order transition relations for explicit finite
code maps. The source is the exact current parameterized mixed domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

def codeMapParameterRelation (A : MixedSetParameterTemplate (M := M) S p n r)
    (F : (Fin p ⊕ (Fin n ⊕ Fin r) → M) → Fin n ⊕ Fin s → M) :
    Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M) :=
  {z | Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i))) ∈ A.typedGraph ∧
    F (Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i))))=(fun i => z (.inr (.inr i)))}

theorem codeMapParameterRelation_definable (A : MixedSetParameterTemplate (M := M) S p n r)
    (F : (Fin p ⊕ (Fin n ⊕ Fin r) → M) → Fin n ⊕ Fin s → M) (hF : S.DefinableMap LRV F) :
    S.Definable LRV (codeMapParameterRelation A F) := by
  let Z := Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s))
  have hArg : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hEach (i : Fin n ⊕ Fin s) : S.Definable LRV {z : Z → M |
      F (Sum.elim (z ∘ Sum.inl) (fun j => z (.inr (.inl j)))) i=z (.inr (.inr i))} :=
    ((hF i).comp hArg).ofPred_eq (Set.DefinableFun.proj LRV)
  have hEq : S.Definable LRV {z : Z → M |
      F (Sum.elim (z ∘ Sum.inl) (fun j => z (.inr (.inl j))))=(fun i => z (.inr (.inr i)))} := by
    convert Set.definable_iInter_of_finite hEach using 1
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,funext_iff]
  exact (A.typedGraph_definable.preimage_map hArg).inter hEq

theorem codeMapParameterRelation_at (A : MixedSetParameterTemplate (M := M) S p n r)
    (F : (Fin p ⊕ (Fin n ⊕ Fin r) → M) → Fin n ⊕ Fin s → M) (a : Fin p → M)
    {B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a)} (f : Map (A.fibre a) B)
    (hCode : ∀ x : A.fibre a,F (Sum.elim a (mixedValues x.val))=mixedValues (f x).val) :
    {z | Sum.elim a z ∈ codeMapParameterRelation A F}=
      (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n s
  have hAcode := (A.fibre_code a).symm
  ext z
  constructor
  · rintro ⟨hSource,hOut⟩
    obtain ⟨hx,hxA⟩ := (Set.ext_iff.mp hAcode _).mp hSource
    let x : A.fibre a := ⟨P.decode ⟨z ∘ Sum.inl,hx⟩,hxA⟩
    have hX : mixedValues x.val=z ∘ Sum.inl := mixedValues_decode (⟨z ∘ Sum.inl,hx⟩ : P.domain)
    change F (Sum.elim a (z ∘ Sum.inl))=z ∘ Sum.inr at hOut
    rw [← hX,hCode x] at hOut
    have hy : z ∘ Sum.inr ∈ Q.domain := hOut ▸ mixedValues_mem_domain (f x).val
    have hDecode := mixedValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    exact ⟨hx,hy,x,rfl,mixedValues_injective (hOut.trans hDecode.symm)⟩
  · rintro ⟨hx,hy,x,hSource,hTarget⟩
    have hX : mixedValues x.val=z ∘ Sum.inl := by rw [hSource]; exact mixedValues_decode _
    have hY : mixedValues (f x).val=z ∘ Sum.inr :=
      (congrArg mixedValues hTarget).trans (mixedValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain))
    refine ⟨(Set.ext_iff.mp hAcode _).mpr ⟨hx,hSource ▸ x.property⟩,?_⟩
    change F (Sum.elim a (z ∘ Sum.inl))=z ∘ Sum.inr
    rw [← hX,hCode x]
    exact hY

end DiamondIntegral.Section6
