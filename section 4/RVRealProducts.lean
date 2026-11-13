import «section 4».FiniteTupleGraphProduct
import «section 4».RVMeasuredCharts
import «section 4».GammaBoundedProducts

/-! Products of actual RV domains and partial real-coordinate map graphs
are definable over the original real/Gamma base. Graphs are rearranged by
the explicit finite-coordinate shuffle; no RV or Gamma section is named. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVRealProducts
open RVMeasuredCharts FiniteTupleBlocks FiniteTupleGraphProduct

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def productSet {a b : ℕ} (I : Set (Fin a → M)) (J : Set (Fin b → M)) : Set (Fin (b + a) → M) :=
  {z | z ∘ headIndex b a ∈ I ∧ z ∘ tailIndex b a ∈ J}

theorem productSet_join {a b : ℕ} (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (x : Fin a → M) (y : Fin b → M) : join b a x y ∈ productSet I J ↔ x ∈ I ∧ y ∈ J := by
  have hh : join b a x y ∘ headIndex b a = x := funext (join_head b a x y)
  have ht : join b a x y ∘ tailIndex b a = y := funext (join_tail b a x y)
  change (join b a x y ∘ headIndex b a ∈ I ∧ join b a x y ∘ tailIndex b a ∈ J) ↔ _
  rw [hh, ht]

theorem productSet_exists {a b : ℕ} (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (z : Fin (b + a) → M) :
    z ∈ productSet I J ↔ ∃ x ∈ I, ∃ y ∈ J, z = join b a x y := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨z ∘ headIndex b a, hx, z ∘ tailIndex b a, hy, (join_reconstruct b a z).symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact (productSet_join I J x y).mpr ⟨hx, hy⟩

theorem productSet_definable (B : Base (M := M)) {a b : ℕ} (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (hI : DefinableOverBase B (fun _ : Fin a => .rv) I)
    (hJ : DefinableOverBase B (fun _ : Fin b => .rv) J) :
    DefinableOverBase B (fun _ : Fin (b + a) => .rv) (productSet I J) := by
  have hi := hI.preimage_real (fun _ : Fin (b + a) => .rv) (headIndex b a)
  have hj := hJ.preimage_real (fun _ : Fin (b + a) => .rv) (tailIndex b a)
  have h := hi.inter hj
  convert h using 1
  ext z
  change (z ∘ headIndex b a ∈ I ∧ z ∘ tailIndex b a ∈ J) ↔
    ((z ∘ headIndex b a ∈ I ∧ z ∈ sortedUniverse (fun _ => .rv)) ∧
      (z ∘ tailIndex b a ∈ J ∧ z ∈ sortedUniverse (fun _ => .rv)))
  constructor
  · rintro ⟨hx, hy⟩
    have hz : z ∈ sortedUniverse (fun _ => .rv) := GammaBoundedProducts.all_coordinates b a iRV z
      (fun i => hI.proper _ hx i) (fun i => hJ.proper _ hy i)
    exact ⟨⟨hx, hz⟩, hy, hz⟩
  · exact fun h => ⟨h.1.1, h.2.1⟩

def productMap {a b k l : ℕ} (F : (Fin a → M) → (Fin k → M)) (G : (Fin b → M) → (Fin l → M))
    (z : Fin (b + a) → M) : Fin (l + k) → M :=
  join l k (F (z ∘ headIndex b a)) (G (z ∘ tailIndex b a))

theorem productMap_join {a b k l : ℕ} (F : (Fin a → M) → (Fin k → M))
    (G : (Fin b → M) → (Fin l → M)) (x : Fin a → M) (y : Fin b → M) :
    productMap F G (join b a x y) = join l k (F x) (G y) := by
  have hh : join b a x y ∘ headIndex b a = x := funext (join_head b a x y)
  have ht : join b a x y ∘ tailIndex b a = y := funext (join_tail b a x y)
  unfold productMap
  rw [hh, ht]

theorem graphOn_exists {a k : ℕ} (I : Set (Fin a → M)) (F : (Fin a → M) → (Fin k → M))
    (w : Fin (k + a) → M) : w ∈ graphOn I F ↔ ∃ x ∈ I, w = join k a x (F x) := by
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨w ∘ headIndex k a, hx, (join_reconstruct k a w).symm.trans
      (congrArg (join k a (w ∘ headIndex k a)) he.symm)⟩
  · rintro ⟨x, hx, rfl⟩
    have hh : join k a x (F x) ∘ headIndex k a = x := funext (join_head k a x (F x))
    have ht : join k a x (F x) ∘ tailIndex k a = F x := funext (join_tail k a x (F x))
    change (join k a x (F x) ∘ headIndex k a ∈ I ∧
      F (join k a x (F x) ∘ headIndex k a) = join k a x (F x) ∘ tailIndex k a)
    rw [hh, ht]
    exact ⟨hx, rfl⟩

theorem product_graph_eq_image {a b k l : ℕ} (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (F : (Fin a → M) → (Fin k → M)) (G : (Fin b → M) → (Fin l → M)) :
    graphOn (productSet I J) (productMap F G) =
      (fun w => w ∘ graphShuffle a b k l) '' productSet (graphOn I F) (graphOn J G) := by
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := (graphOn_exists _ _ w).mp hw
    let x := z ∘ headIndex b a
    let y := z ∘ tailIndex b a
    refine ⟨join (l + b) (k + a) (join k a x (F x)) (join l b y (G y)),
      (productSet_join _ _ _ _).mpr ⟨(graphOn_exists _ _ _).mpr ⟨x, hz.1, rfl⟩,
        (graphOn_exists _ _ _).mpr ⟨y, hz.2, rfl⟩⟩, ?_⟩
    have h := graphShuffle_join a b k l x (F x) y (G y)
    have he : join b a x y = z := join_reconstruct b a z
    rw [he] at h
    exact h
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨vF, hF, vG, hG, rfl⟩ := (productSet_exists _ _ v).mp hv
    obtain ⟨x, hx, rfl⟩ := (graphOn_exists _ _ vF).mp hF
    obtain ⟨y, hy, rfl⟩ := (graphOn_exists _ _ vG).mp hG
    change (join (l + b) (k + a) (join k a x (F x)) (join l b y (G y)) ∘ graphShuffle a b k l) ∈
      graphOn (productSet I J) (productMap F G)
    rw [graphShuffle_join]
    apply (graphOn_exists _ _ _).mpr
    refine ⟨join b a x y, (productSet_join I J x y).mpr ⟨hx, hy⟩, ?_⟩
    rw [productMap_join]

theorem product_graph_definable (B : Base (M := M)) {a b k l : ℕ}
    (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (F : (Fin a → M) → (Fin k → M)) (G : (Fin b → M) → (Fin l → M))
    (hF : DefinableOverBase B (fun _ : Fin (k + a) => .rv) (graphOn I F))
    (hG : DefinableOverBase B (fun _ : Fin (l + b) => .rv) (graphOn J G)) :
    DefinableOverBase B (fun _ : Fin ((l + k) + (b + a)) => .rv)
      (graphOn (productSet I J) (productMap F G)) := by
  have h : DefinableOverBase B (fun _ : Fin ((l + k) + (b + a)) => .rv)
      ((fun w => w ∘ graphShuffle a b k l) '' productSet (graphOn I F) (graphOn J G)) :=
    (productSet_definable B _ _ hF hG).image_real (graphShuffle a b k l)
  rw [product_graph_eq_image]
  exact h

end DiamondIntegral.Section4.RVRealProducts
