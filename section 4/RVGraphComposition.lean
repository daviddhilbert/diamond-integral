import «section 4».RVRealProducts

/-! Composition of original-base partial RV graphs, retaining genuine
Gamma parameters through coordinate pullback and real-coordinate image.
No RV representatives are named. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVGraphComposition
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks FiniteTupleGraphProduct
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pack {a b c : ℕ} (x : Fin a → M) (y : Fin b → M) (z : Fin c → M) : Fin (c + (b + a)) → M :=
  join c (b + a) (join b a x y) z

def lastTwo (a b c : ℕ) : Fin (c + b) → Fin (c + (b + a)) :=
  join c b (fun i => headIndex c (b + a) (tailIndex b a i)) (tailIndex c (b + a))

def outerTwo (a b c : ℕ) : Fin (c + a) → Fin (c + (b + a)) :=
  join c a (fun i => headIndex c (b + a) (headIndex b a i)) (tailIndex c (b + a))

theorem pack_first {a b c : ℕ} (x : Fin a → M) (y : Fin b → M) (z : Fin c → M) :
    pack x y z ∘ headIndex c (b + a) = join b a x y := funext (join_head c (b + a) _ _)

theorem pack_lastTwo {a b c : ℕ} (x : Fin a → M) (y : Fin b → M) (z : Fin c → M) :
    pack x y z ∘ lastTwo a b c = join c b y z := by
  apply block_ext c b
  · funext i
    simp [lastTwo, pack, Function.comp_apply]
  · funext i
    simp [lastTwo, pack, Function.comp_apply]

theorem pack_outerTwo {a b c : ℕ} (x : Fin a → M) (y : Fin b → M) (z : Fin c → M) :
    pack x y z ∘ outerTwo a b c = join c a x z := by
  apply block_ext c a
  · funext i
    simp [outerTwo, pack, Function.comp_apply]
  · funext i
    simp [outerTwo, pack, Function.comp_apply]

theorem reconstruct {a b c : ℕ} (w : Fin (c + (b + a)) → M) :
    pack ((w ∘ headIndex c (b + a)) ∘ headIndex b a)
      ((w ∘ headIndex c (b + a)) ∘ tailIndex b a) (w ∘ tailIndex c (b + a)) = w := by
  unfold pack
  rw [join_reconstruct, join_reconstruct]

theorem graph_compose_definable (B : Base (M := M)) {a b c : ℕ}
    (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (F : (Fin a → M) → (Fin b → M)) (G : (Fin b → M) → (Fin c → M))
    (hF : DefinableOverBase B (fun _ : Fin (b + a) => .rv) (graphOn I F))
    (hG : DefinableOverBase B (fun _ : Fin (c + b) => .rv) (graphOn J G))
    (hmap : Set.MapsTo F I J) :
    DefinableOverBase B (fun _ : Fin (c + a) => .rv) (graphOn I (G ∘ F)) := by
  let S : Set (Fin (c + (b + a)) → M) :=
    {w | w ∘ headIndex c (b + a) ∈ graphOn I F ∧ w ∘ lastTwo a b c ∈ graphOn J G ∧
      ∀ i, iRV (w i)}
  have hS : DefinableOverBase B (fun _ : Fin (c + (b + a)) => .rv) S := by
    have h := (hF.preimage_real (fun _ : Fin (c + (b + a)) => .rv) (headIndex c (b + a))).inter
      (hG.preimage_real (fun _ : Fin (c + (b + a)) => .rv) (lastTwo a b c))
    convert h using 1
    ext w
    change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    tauto
  have h := hS.image_real (outerTwo a b c)
  have he : graphOn I (G ∘ F) = (fun w => w ∘ outerTwo a b c) '' S := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (graphOn_exists _ _ v).mp hv
      let w := pack x (F x) (G (F x))
      have hFp : join b a x (F x) ∈ graphOn I F := (graphOn_exists _ _ _).mpr ⟨x, hx, rfl⟩
      have hGp : join c b (F x) (G (F x)) ∈ graphOn J G :=
        (graphOn_exists _ _ _).mpr ⟨F x, hmap hx, rfl⟩
      refine ⟨w, ⟨?_, ?_, ?_⟩, pack_outerTwo x (F x) (G (F x))⟩
      · change pack x (F x) (G (F x)) ∘ headIndex c (b + a) ∈ _
        rw [pack_first]
        exact hFp
      · change pack x (F x) (G (F x)) ∘ lastTwo a b c ∈ _
        rw [pack_lastTwo]
        exact hGp
      · apply GammaBoundedProducts.all_coordinates c (b + a) iRV w
        · intro i
          change iRV (pack x (F x) (G (F x)) (headIndex c (b + a) i))
          have hi : iRV (join b a x (F x) i) := hF.proper _ hFp i
          simpa only [pack, join_head] using hi
        · intro i
          change iRV (pack x (F x) (G (F x)) (tailIndex c (b + a) i))
          have hi : iRV (join c b (F x) (G (F x)) (tailIndex c b i)) := hG.proper _ hGp (tailIndex c b i)
          simpa only [pack, join_tail] using hi
    · rintro ⟨w, hw, rfl⟩
      let x := (w ∘ headIndex c (b + a)) ∘ headIndex b a
      let y := (w ∘ headIndex c (b + a)) ∘ tailIndex b a
      let z := w ∘ tailIndex c (b + a)
      have hr : pack x y z = w := reconstruct w
      have hxy : join b a x y ∈ graphOn I F := by
        have hh := hw.1
        rw [← hr, pack_first] at hh
        exact hh
      have hyz : join c b y z ∈ graphOn J G := by
        have hh := hw.2.1
        rw [← hr, pack_lastTwo] at hh
        exact hh
      have hFx : F x = y := by
        have hh := hxy.2
        simpa only [show join b a x y ∘ headIndex b a = x from funext (join_head b a x y),
          show join b a x y ∘ tailIndex b a = y from funext (join_tail b a x y)] using hh
      have hGz : G y = z := by
        have hh := hyz.2
        simpa only [show join c b y z ∘ headIndex c b = y from funext (join_head c b y z),
          show join c b y z ∘ tailIndex c b = z from funext (join_tail c b y z)] using hh
      apply (graphOn_exists _ _ _).mpr
      refine ⟨x, ?_, ?_⟩
      · simpa only [show join b a x y ∘ headIndex b a = x from funext (join_head b a x y)] using hxy.1
      · change w ∘ outerTwo a b c = join c a x (G (F x))
        rw [← hr, pack_outerTwo]
        exact congrArg (join c a x) (hGz.symm.trans (congrArg G hFx.symm))
  rw [he]
  exact h

end DiamondIntegral.Section4.RVGraphComposition
