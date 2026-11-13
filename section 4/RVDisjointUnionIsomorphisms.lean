import «section 4».RVChartDisjointUnion
import «section 4».RVMeasuredIsomorphisms

/-! Measured isomorphisms on disjoint definable pieces glue to an actual
original-base measured isomorphism of their union objects. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDisjointUnionIsomorphisms
open RVMeasuredCharts RVChartDisjointUnion RVMeasuredIsomorphisms
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem piecewise_bijOn {n m : ℕ} (A B : Set (Fin n → M)) (C D : Set (Fin m → M))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (f g : (Fin n → M) → (Fin m → M)) (hf : Set.BijOn f A C) (hg : Set.BijOn g B D) :
    Set.BijOn (piecewise A f g) (A ∪ B) (C ∪ D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases ha : x ∈ A
    · exact Or.inl (by simpa only [piecewise, ite_eq_left ha] using hf.1 ha)
    · exact Or.inr (by simpa only [piecewise, ite_eq_right ha] using hg.1 (hx.resolve_left ha))
  · intro x hx y hy he
    by_cases ha : x ∈ A <;> by_cases hb : y ∈ A
    · apply hf.2.1 ha hb
      simpa only [piecewise, ite_eq_left ha, ite_eq_left hb] using he
    · have hyB := hy.resolve_left hb
      have he' : f x = g y := by simpa only [piecewise, ite_eq_left ha, ite_eq_right hb] using he
      exact False.elim (Set.disjoint_left.mp hCD (Set.mem_of_eq_of_mem he'.symm (hf.1 ha)) (hg.1 hyB))
    · have hxB := hx.resolve_left ha
      have he' : g x = f y := by simpa only [piecewise, ite_eq_right ha, ite_eq_left hb] using he
      exact False.elim (Set.disjoint_left.mp hCD (Set.mem_of_eq_of_mem he' (hf.1 hb)) (hg.1 hxB))
    · apply hg.2.1 (hx.resolve_left ha) (hy.resolve_left hb)
      simpa only [piecewise, ite_eq_right ha, ite_eq_right hb] using he
  · intro y hy
    rcases hy with hyC | hyD
    · obtain ⟨x, hx, he⟩ := hf.2.2 hyC
      exact ⟨x, Or.inl hx, by simpa only [piecewise, ite_eq_left hx] using he⟩
    · obtain ⟨x, hx, he⟩ := hg.2.2 hyD
      have ha : x ∉ A := fun ha => Set.disjoint_left.mp hAB ha hx
      exact ⟨x, Or.inr hx, by simpa only [piecewise, ite_eq_right ha] using he⟩

def unionIso {B : Base (M := M)} {n m k : ℕ} (a b : Data B n k) (c d : Data B m k)
    (hab : Disjoint a.domain b.domain) (hcd : Disjoint c.domain d.domain)
    (F : Iso a.toChart c.toChart) (G : Iso b.toChart d.toChart) :
    Iso (disjointUnion a b hab).toChart (disjointUnion c d hcd).toChart := by
  let f := underlying F
  let g := underlying G
  let ff : (Fin n → M) → (Fin m → M) := f.extension
  let gg : (Fin n → M) → (Fin m → M) := g.extension
  let h : (Fin n → M) → (Fin m → M) := piecewise a.domain ff gg
  have hgraph : DefinableOverBase B (fun _ : Fin (m + n) => .rv)
      (graphOn (a.domain ∪ b.domain) h) := by
    change DefinableOverBase B _ (graphOn (a.domain ∪ b.domain) (piecewise a.domain ff gg))
    rw [graphOn_piecewise _ _ hab ff gg]
    have hf : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn a.domain ff) := f.extension_graph
    have hg : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn b.domain gg) := g.extension_graph
    exact hf.union hg
  have hbij : Set.BijOn h (a.domain ∪ b.domain) (c.domain ∪ d.domain) :=
    piecewise_bijOn _ _ _ _ hab hcd f.extension g.extension f.extension_bijOn g.extension_bijOn
  let H := RVUnderlyingIsomorphisms.ofMap (disjointUnion a b hab).toChart
    (disjointUnion c d hcd).toChart h hgraph hbij
  refine ⟨H.equiv, H.graph_definable, ?_⟩
  intro u
  let x : Fin n → M := u.val
  change (disjointUnion a b hab).toChart.correctedWeight x =
    (disjointUnion c d hcd).toChart.correctedWeight (h x)
  rcases u.property with ha | hb
  · have ha' : x ∈ a.domain := ha
    let v : a.toChart.domain := ⟨x, ha'⟩
    have he : h x = (F.equiv v).val := by
      change piecewise a.domain ff gg x = _
      simp only [RVChartDisjointUnion.piecewise, ite_eq_left ha']
      exact f.extension_on v
    exact (disjointUnion_weight_left a b hab x ha).trans
      ((F.weight_eq v).trans ((disjointUnion_weight_left c d hcd (F.equiv v).val (F.equiv v).property).symm.trans
        (congrArg (disjointUnion c d hcd).toChart.correctedWeight he.symm)))
  · let v : b.toChart.domain := ⟨x, hb⟩
    have ha : x ∉ a.domain := fun ha => Set.disjoint_left.mp hab ha hb
    have he : h x = (G.equiv v).val := by
      change piecewise a.domain ff gg x = _
      simp only [RVChartDisjointUnion.piecewise, ite_eq_right ha]
      exact g.extension_on v
    exact (disjointUnion_weight_right a b hab x hb).trans
      ((G.weight_eq v).trans ((disjointUnion_weight_right c d hcd (G.equiv v).val (G.equiv v).property).symm.trans
        (congrArg (disjointUnion c d hcd).toChart.correctedWeight he.symm)))

end DiamondIntegral.Section4.RVDisjointUnionIsomorphisms
