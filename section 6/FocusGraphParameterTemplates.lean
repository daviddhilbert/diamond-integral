import «section 6».RVSetParameterTemplates
import «section 6».RVFamilyMapGraphCodes

/-! The complete partial focus graph is computed uniformly from the
current mixed domain, its active old-label locus and one whole-family
template. Its specialization is the literal actual focus-map graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

def focusGraphParameterCode (A : MixedSetParameterTemplate (M := M) S p n r)
    (U : RVSetParameterTemplate (M := M) S p r) (F : ContinuousRVGraphTemplate (M := M) S p r n 1) :
    Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) → M) :=
  {z | Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i))) ∈ (focusActiveParameterTemplate A U).typedGraph ∧
    Sum.elim (z ∘ Sum.inl) (Sum.elim (fun j => z (.inr (.inl (.inr j))))
      (Sum.elim (fun i => z (.inr (.inl (.inl i)))) (fun k => z (.inr (.inr k))))) ∈ F.graph}

theorem focusGraphParameterCode_definable (A : MixedSetParameterTemplate (M := M) S p n r)
    (U : RVSetParameterTemplate (M := M) S p r) (F : ContinuousRVGraphTemplate (M := M) S p r n 1) :
    S.Definable LRV (focusGraphParameterCode A U F) := by
  let Z := Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1)
  have hSourceCode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hFamilyCode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun j => z (.inr (.inl (.inr j))))
        (Sum.elim (fun i => z (.inr (.inl (.inl i)))) (fun k => z (.inr (.inr k)))))) := by
    rintro (i | (i | (i | i))) <;> exact Set.DefinableFun.proj LRV
  exact ((focusActiveParameterTemplate A U).typedGraph_definable.preimage_map hSourceCode).inter
    (F.definable.preimage_map hFamilyCode)

theorem focusGraphParameterCode_at (A : MixedSetParameterTemplate (M := M) S p n r)
    (U : RVSetParameterTemplate (M := M) S p r) (F : ContinuousRVGraphTemplate (M := M) S p r n 1)
    (a : Fin p → M) (ha : a ∈ F.good) :
    {z | Sum.elim a z ∈ focusGraphParameterCode A U F}=
      (rawMixedSpace n r).relation (rawVFSpace 1)
        (rvFamilyMap (focusActive (A.fibre a) (U.fibre a)) (F.value a ha) (F.family_graph_definable a ha)).graph := by
  let P := rawMixedSpace (M := M) n r
  let active := focusActiveParameterTemplate A U
  have hSourceEq : P.preimage (focusActive (A.fibre a) (U.fibre a)).carrier=
      {z | Sum.elim a z ∈ active.typedGraph} := by
    rw [← focusActiveParameterTemplate_fibre A U a]
    exact active.fibre_code a
  rw [rvFamilyMap_graph_code]
  ext z
  have hCode : Sum.elim a (z ∘ rvFamilyGraphIndex n r 1)=
      Sum.elim a (Sum.elim (fun j => z (.inl (.inr j)))
        (Sum.elim (fun i => z (.inl (.inl i))) (fun k => z (.inr k)))) := by
    funext i
    rcases i with i | (i | (i | i)) <;> rfl
  change (Sum.elim a (z ∘ Sum.inl) ∈ active.typedGraph ∧ _) ↔
    (z ∘ Sum.inl ∈ P.preimage (focusActive (A.fibre a) (U.fibre a)).carrier ∧ _)
  have hSourceAt : z ∘ Sum.inl ∈ P.preimage (focusActive (A.fibre a) (U.fibre a)).carrier ↔
      Sum.elim a (z ∘ Sum.inl) ∈ active.typedGraph := Set.ext_iff.mp hSourceEq _
  rw [← hSourceAt]
  apply and_congr_right
  intro hSource
  rw [F.family_graph a ha]
  change _ ∈ F.graph ↔ ((z ∘ rvFamilyGraphIndex n r 1) ∘ Sum.inl ∈ Set.range rvValues ∧
    Sum.elim a (z ∘ rvFamilyGraphIndex n r 1) ∈ F.graph)
  rw [hCode]
  exact ⟨fun h => ⟨hSource.choose.2,h⟩,fun h => h.2⟩

end DiamondIntegral.Section6
