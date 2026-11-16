import «section 6».GammaFormMaps

/-! For an actual bijection retaining the old RV labels, each fixed
target-label fiber of its inverse has exactly one possible input label.
Its full graph-fiber source is the entire target VF fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

theorem retained_inverse_tags (f : Map A B) (hf : Function.Bijective f) (h : r ≤ s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (rvTailIndex h i) = p.val.2 i) (q : B) :
    (f.inverse hf q).val.2 = fun i => q.val.2 (rvTailIndex h i) := by
  funext i
  have he := congrArg (fun z : B => z.val.2 (rvTailIndex h i)) (Map.apply_inverse f hf q)
  exact (hRetain (f.inverse hf q) i).symm.trans he

theorem retained_inverse_fiber_source (f : Map A B) (hf : Function.Bijective f) (h : r ≤ s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (rvTailIndex h i) = p.val.2 i)
    (v : Fin s → RVInfinity M) :
    graphFibreSource (f.inverse hf) v (fun i => v (rvTailIndex h i)) = vfFibre B.carrier v := by
  ext x
  constructor
  · rintro ⟨a,q,hqx,_⟩
    change (x,v) ∈ B.carrier
    rw [← hqx]
    exact q.property
  · intro hx
    let q : B := ⟨(x,v),hx⟩
    exact ⟨(f.inverse hf q).val.1,q,rfl,Prod.ext rfl (retained_inverse_tags f hf h hRetain q)⟩

theorem retained_inverse_point (f : Map A B) (hf : Function.Bijective f) (h : r ≤ s)
    (hRetain : ∀ p : A, ∀ i : Fin r, (f p).val.2 (rvTailIndex h i) = p.val.2 i)
    (v : Fin s → RVInfinity M) (x : Fin m → VF M) (hx : (x,v) ∈ B.carrier) :
    (f.inverse hf ⟨(x,v),hx⟩).val =
      (graphFibreMap (f.inverse hf) v (fun i => v (rvTailIndex h i)) x,fun i => v (rvTailIndex h i)) := by
  let q : B := ⟨(x,v),hx⟩
  have hTags := retained_inverse_tags f hf h hRetain q
  have hSource : x ∈ graphFibreSource (f.inverse hf) v (fun i => v (rvTailIndex h i)) := by
    rw [retained_inverse_fiber_source f hf h hRetain]
    exact hx
  have hGraph : graphFibre (f.inverse hf) v (fun i => v (rvTailIndex h i)) x (f.inverse hf q).val.1 :=
    ⟨q,rfl,Prod.ext rfl hTags⟩
  exact Prod.ext (graphFibre_functional (f.inverse hf) v _ hGraph
    (graphFibreMap_graph (f.inverse hf) v _ hSource)) hTags

end DiamondIntegral.Section6
