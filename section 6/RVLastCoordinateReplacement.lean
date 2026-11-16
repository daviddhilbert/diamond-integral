import «section 6».RVCoordinateInverseRelations

/-! Actual last-coordinate replacement maps and their original-base
finite-obstacle loci. All old domain labels remain unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvLastReplacementMap {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1)) :
    Map U.domain (DefSet.univ (rawRVSpace (M := M) (n+1)) S) :=
  rvTupleAssembleMap U.domain (n+1) (fun i => Fin.lastCases
    ((rvTupleSelectMap S (fun _ : Fin 1 => j)).comp (V.volume.comp F.map))
    (fun k => (rvTupleSelectMap S (fun _ : Fin 1 => k.castSucc)).comp U.volume) i)

theorem rvLastReplacementMap_value {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (u : U.domain) : (rvLastReplacementMap F j u).val = Fin.snoc (Fin.init (U.value u)) (V.value (F.map u) j) := by
  change (rvTupleAssembleMap U.domain (n+1) _ u).val = _
  rw [rvTupleAssembleMap_value]
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Fin.lastCases_last,Fin.snoc_last]
    rfl
  · simp only [Fin.lastCases_castSucc,Fin.snoc_castSucc]
    rfl

theorem rvLastReplacementMap_codes {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (u : U.domain) : rvValues (rvLastReplacementMap F j u).val =
      Fin.snoc (Fin.init (rvValues (U.value u))) (V.value (F.map u) j).val := by
  rw [rvLastReplacementMap_value]
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [rvValues,Fin.snoc_last]
  · simp only [rvValues,Fin.snoc_castSucc]
    rfl

def rvFiniteRelationLocus (E : RawClosure.Tuple.GoodRelation (n := n) S) :
    DefSet (rawRVSpace (M := M) (n+1)) S where
  carrier := {t | rvValues t ∈ finiteRelationGraph E}
  definable := by
    have h := ((rawRVSpace (M := M) (n+1)).definable_domain S).inter (finiteRelationGraph_definable E)
    change S.Definable LRV ((rawRVSpace (M := M) (n+1)).preimage {t | rvValues t ∈ finiteRelationGraph E})
    convert h using 1 <;> try rfl
    apply Set.ext
    intro (z : Fin (n+1) → M)
    constructor
    · rintro ⟨hz,hzE⟩
      change rvValues ((rawRVSpace (M := M) (n+1)).decode ⟨z,hz⟩) ∈ finiteRelationGraph E at hzE
      have he : rvValues ((rawRVSpace (M := M) (n+1)).decode ⟨z,hz⟩) = z := rvValues_decode _
      exact ⟨hz,he ▸ hzE⟩
    · rintro ⟨hz,hzE⟩
      refine ⟨hz,?_⟩
      change rvValues ((rawRVSpace (M := M) (n+1)).decode ⟨z,hz⟩) ∈ finiteRelationGraph E
      rw [rvValues_decode]
      exact hzE

def rvGoodReplacementDomain {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S) : DefSet (rawRVSpace (M := M) U.arity) S where
  carrier := {t | ∃ u : U.domain, u.val = t ∧ (rvLastReplacementMap F j u).val ∉ (rvFiniteRelationLocus E).carrier}
  definable := (rvLastReplacementMap F j).definable_preimage
    ((rvFiniteRelationLocus E).definable.compl (rawRVSpace (M := M) (n+1)))

theorem rvGoodReplacementDomain_subset {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S) :
    (rvGoodReplacementDomain F j E).carrier ⊆ U.domain.carrier := by
  rintro t ⟨u,rfl,_⟩
  exact u.property

theorem rvGoodReplacementDomain_mem {U V : RVObject (M := M) S (n+1)} (F : RVHom U V) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S) (u : U.domain) :
    u.val ∈ (rvGoodReplacementDomain F j E).carrier ↔
      (Fin.init (rvValues (U.value u)),(V.value (F.map u) j).val) ∉ E.val := by
  have hmem : (rvLastReplacementMap F j u).val ∈ (rvFiniteRelationLocus E).carrier ↔
      (Fin.init (rvValues (U.value u)),(V.value (F.map u) j).val) ∈ E.val := by
    change rvValues (rvLastReplacementMap F j u).val ∈ finiteRelationGraph E ↔ _
    rw [rvLastReplacementMap_codes]
    simp only [finiteRelationGraph,Fin.init_snoc,Fin.snoc_last,Set.mem_setOf_eq]
  constructor
  · rintro ⟨v,hv,hnot⟩
    have he : v = u := Subtype.ext hv
    exact hmem.not.mp (he ▸ hnot)
  · intro hnot
    exact ⟨u,rfl,hmem.not.mpr hnot⟩

end DiamondIntegral.Section6
