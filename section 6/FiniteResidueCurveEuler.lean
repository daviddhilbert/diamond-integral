import «section 6».FiniteCurveExcisions
import «section 6».ResidueCurveConservation

/-! Definable bijections preserve the Euler count of finite disjoint
unions of residue affine lines with finitely many holes and finitely
many isolated points. The finite-point contribution is proved using
actual finite excisions; it is not an additional Euler axiom. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Set Classical FirstOrder FirstOrder.Language
open IntegrationInACVF.Section3

namespace DiamondIntegral.Section6

theorem finite_curve_euler_conservation {K : Type*} [Field K] [IsAlgClosed K]
    [FirstOrder.Ring.CompatibleRing K]
    (P Q : Finset K) (F E G D : Finset (Fin 2 → K))
    (hF : (F : Set (Fin 2 → K)) ⊆ TaggedLineMaps.space P)
    (hG : (G : Set (Fin 2 → K)) ⊆ TaggedLineMaps.space Q)
    (hE : Disjoint (TaggedLineMaps.space P) (E : Set (Fin 2 → K)))
    (hD : Disjoint (TaggedLineMaps.space Q) (D : Set (Fin 2 → K)))
    (f : (Fin 2 → K) → (Fin 2 → K))
    (hGraph : (Set.univ : Set K).Definable Language.ring
      (FiniteTupleGraphs.graph ((TaggedLineMaps.space P \ F) ∪ E) f))
    (hBij : Set.BijOn f ((TaggedLineMaps.space P \ F) ∪ E)
      ((TaggedLineMaps.space Q \ G) ∪ D)) :
    (P.card : ℤ) - F.card + E.card = (Q.card : ℤ) - G.card + D.card := by
  obtain ⟨C,L,hC,hL,hCore,hPatch⟩ := finite_curve_excisions
    (TaggedLineMaps.space P) (TaggedLineMaps.space Q) F E G D hE hD f hBij
  have hFC : Disjoint F C := Finset.disjoint_left.mpr (fun x hxF hxC => (hC hxC).2 hxF)
  have hGL : Disjoint G L := Finset.disjoint_left.mpr (fun x hxG hxL => (hL hxL).2 hxG)
  have hF' : ((F ∪ C : Finset (Fin 2 → K)) : Set (Fin 2 → K)) ⊆ TaggedLineMaps.space P := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hF h
    · exact (hC h).1
  have hG' : ((G ∪ L : Finset (Fin 2 → K)) : Set (Fin 2 → K)) ⊆ TaggedLineMaps.space Q := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hG h
    · exact (hL h).1
  have hDrop := (FiniteDefinablePatching.finite_univ Language.ring (E ∪ C).finite_toSet).preimage_comp
    (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)
  have hRestricted : (Set.univ : Set K).Definable Language.ring
      (FiniteTupleGraphs.graph (TaggedLineMaps.space P \ (F ∪ C : Finset (Fin 2 → K))) f) := by
    convert hGraph.inter hDrop.compl using 1
    ext z
    simp only [FiniteTupleGraphs.graph,Set.mem_setOf_eq,Set.mem_diff,Set.mem_union,
      Finset.coe_union,Set.mem_preimage,Set.mem_inter_iff,Set.mem_compl_iff]
    have hDis : z ∘ Sum.inl ∈ TaggedLineMaps.space P → z ∘ Sum.inl ∉ (E : Set (Fin 2 → K)) :=
      fun h => Set.disjoint_left.mp hE h
    tauto
  obtain ⟨hComponents,hHoles⟩ := TaggedCofiniteConservation.components_and_holes
    Set.univ P Q (F ∪ C) (G ∪ L) hF' hG' f hRestricted
      (by simpa only [Finset.coe_union] using hCore)
  rw [Finset.card_union_of_disjoint hFC,Finset.card_union_of_disjoint hGL] at hHoles
  omega

end DiamondIntegral.Section6
