import «section 6».UncurriedMixedTemplates
import «section 6».ContinuousRVFamilyMaps
import Section4.FunctionalRelations

/-! Admissible continuous family formulas assemble into actual maps
on the mixed domain retaining their VF parameter. The whole graph is
definable over the original base, with every RV representative retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m : ℕ}

theorem ContinuousRVGraphTemplate.value_graph_at
    (F : ContinuousRVGraphTemplate (M := M) S 1 r n m) (a : Fin 1 → M) (ha : a ∈ F.good)
    (u : Fin r → RVInfinity M) (x : Fin n → VF M) (y : Fin m → VF M) :
    Sum.elim a (Sum.elim (rvValues u) (Sum.elim (vfValues x) (vfValues y))) ∈ F.graph ↔
      F.value a ha u x=y := by
  constructor
  · intro hy
    have he := (F.rowGood a ha u).1.2 (vfValues x) (vfValues y) (vfValues (F.value a ha u x))
      hy (F.value_mem a ha u x)
    exact (vfValues_injective he).symm
  · intro he
    rw [← he]
    exact F.value_mem a ha u x

def uncurriedFamilyGraphIndex :
    Fin 1 ⊕ (Fin r ⊕ (Fin n ⊕ Fin m)) → ((Fin (n+1) ⊕ Fin r) ⊕ Fin m) :=
  Sum.elim (fun _ => .inl (.inl 0))
    (Sum.elim (fun i => .inl (.inr i)) (Sum.elim (fun i => .inl (.inl i.succ)) Sum.inr))

def uncurriedFamilyRelation (F : ContinuousRVGraphTemplate (M := M) S 1 r n m)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (x : Mixed M (n+1) r) (y : Fin m → VF M) : Prop :=
  x ∈ A.carrier ∧ Sum.elim (fun _ : Fin 1 => (x.1 0).val)
    (Sum.elim (rvValues x.2) (Sum.elim (vfValues (Fin.tail x.1)) (vfValues y))) ∈ F.graph

theorem uncurriedFamilyRelation_definable
    (F : ContinuousRVGraphTemplate (M := M) S 1 r n m)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    (rawMixedSpace (n+1) r).RelationDefinable (rawVFSpace m) S (uncurriedFamilyRelation F A) := by
  let P := rawMixedSpace (M := M) (n+1) r
  let Q := rawVFSpace (M := M) m
  have hSource := A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
  have hTarget := (Q.definable_domain S).preimage_comp (Sum.inr : Q.Index → P.Index ⊕ Q.Index)
  have hFamily := F.definable.preimage_comp uncurriedFamilyGraphIndex
  change S.Definable LRV (P.relation Q (uncurriedFamilyRelation F A))
  convert (hSource.inter hTarget).inter hFamily using 1
  ext z
  constructor
  · rintro ⟨hx,hy,hA,hF⟩
    refine ⟨⟨⟨hx,hA⟩,hy⟩,?_⟩
    have hX := mixedValues_decode (⟨z ∘ Sum.inl,hx⟩ : P.domain)
    have hY := vfValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    have he : Sum.elim (fun _ : Fin 1 => ((P.decode ⟨z ∘ Sum.inl,hx⟩).1 0).val)
        (Sum.elim (rvValues (P.decode ⟨z ∘ Sum.inl,hx⟩).2)
          (Sum.elim (vfValues (Fin.tail (P.decode ⟨z ∘ Sum.inl,hx⟩).1))
            (vfValues (Q.decode ⟨z ∘ Sum.inr,hy⟩))))=z ∘ uncurriedFamilyGraphIndex := by
      funext i
      rcases i with i | (i | (i | i))
      · exact congrFun hX (.inl 0)
      · exact congrFun hX (.inr i)
      · exact congrFun hX (.inl i.succ)
      · exact congrFun hY i
    change z ∘ uncurriedFamilyGraphIndex ∈ F.graph
    exact he ▸ hF
  · rintro ⟨⟨⟨hx,hA⟩,hy⟩,hF⟩
    refine ⟨hx,hy,hA,?_⟩
    have hX := mixedValues_decode (⟨z ∘ Sum.inl,hx⟩ : P.domain)
    have hY := vfValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    have he : Sum.elim (fun _ : Fin 1 => ((P.decode ⟨z ∘ Sum.inl,hx⟩).1 0).val)
        (Sum.elim (rvValues (P.decode ⟨z ∘ Sum.inl,hx⟩).2)
          (Sum.elim (vfValues (Fin.tail (P.decode ⟨z ∘ Sum.inl,hx⟩).1))
            (vfValues (Q.decode ⟨z ∘ Sum.inr,hy⟩))))=z ∘ uncurriedFamilyGraphIndex := by
      funext i
      rcases i with i | (i | (i | i))
      · exact congrFun hX (.inl 0)
      · exact congrFun hX (.inr i)
      · exact congrFun hX (.inl i.succ)
      · exact congrFun hY i
    exact he.symm ▸ hF

def uncurriedFamilyMap
    (F : ContinuousRVGraphTemplate (M := M) S 1 r n m)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hGood : ∀ x ∈ A.carrier,(fun _ : Fin 1 => (x.1 0).val) ∈ F.good) :
    Map A (DefSet.univ (rawVFSpace (M := M) m) S) := by
  have hDom : ∀ x y,uncurriedFamilyRelation F A x y → x ∈ A.carrier ∧ y ∈ (Set.univ : Set (Fin m → VF M)) :=
    fun _ _ h => ⟨h.1,Set.mem_univ _⟩
  have hTotal (x : A) : ∃ y,uncurriedFamilyRelation F A x.val y :=
    ⟨F.value _ (hGood x.val x.property) x.val.2 (Fin.tail x.val.1),
      x.property,F.value_mem _ (hGood x.val x.property) x.val.2 (Fin.tail x.val.1)⟩
  have hUnique (x y z) (hy : uncurriedFamilyRelation F A x y) (hz : uncurriedFamilyRelation F A x z) : y=z :=
    ((F.value_graph_at _ (hGood x hy.1) x.2 (Fin.tail x.1) y).mp hy.2).symm.trans
      ((F.value_graph_at _ (hGood x hy.1) x.2 (Fin.tail x.1) z).mp hz.2)
  exact Map.ofFunctionalRelation (uncurriedFamilyRelation_definable F A) hDom hTotal hUnique

end DiamondIntegral.Section6
