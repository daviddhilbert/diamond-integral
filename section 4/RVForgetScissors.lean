import «section 4».RVMeasuredGroup
import «section 4».RVCoordinateMaps

/-! Forgetting the Gamma volume form on actual RV charts. A weighted
scissor square gives an ordinary scissor square: the projection forgetting
weight is injective on the packed graph of the union object. This keeps
finite RV coefficients intact and does not split them into points. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVForgetScissors
open RVMeasuredCharts RVMeasuredGroup RVRealProducts FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forgetPacked (p : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)) : Σ m : ℕ, (Fin m → M) :=
  ⟨p.1, p.2.1⟩

def packedDomain {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Set (Σ m : ℕ, (Fin m → M)) :=
  Set.range (fun u : a.domain => ⟨a.arity, u.val⟩)

theorem packedDomain_eq_image {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    packedDomain a = forgetPacked '' packed a := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨a.arity, u.val, a.correctedWeight u.val⟩, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

theorem forgetPacked_injOn {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Set.InjOn forgetPacked (packed a) := by
  rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩ h
  change (⟨a.arity, u.val⟩ : Σ m : ℕ, (Fin m → M)) = ⟨a.arity, v.val⟩ at h
  have huv : u.val = v.val := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have he : u = v := Subtype.ext huv
  subst v
  rfl

def Scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k) : Prop :=
  a.arity = b.arity ∧ a.arity = c.arity ∧ a.arity = d.arity ∧
    packedDomain c = packedDomain a ∪ packedDomain b ∧ packedDomain d = packedDomain a ∩ packedDomain b

theorem measured_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k)
    (h : RVMeasuredGroup.Scissor a b c d) : Scissor a b c d := by
  obtain ⟨hab, hac, had, hc, hd⟩ := h
  refine ⟨hab, hac, had, ?_, ?_⟩
  · rw [packedDomain_eq_image c, hc, Set.image_union, ← packedDomain_eq_image a, ← packedDomain_eq_image b]
  · have ha : packed a ⊆ packed c := by rw [hc]; exact Set.subset_union_left
    have hb : packed b ⊆ packed c := by rw [hc]; exact Set.subset_union_right
    rw [packedDomain_eq_image d, hd, (forgetPacked_injOn c).image_inter ha hb,
      ← packedDomain_eq_image a, ← packedDomain_eq_image b]

structure UnderlyingIso {B : Base (M := M)} {k : ℕ} (a b : Chart B k) where
  equiv : a.domain ≃ b.domain
  graph_definable : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv)
    {w | ∃ u : a.domain, w = join b.arity a.arity u.val (equiv u).val}

def ofMeasured {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) : UnderlyingIso a b :=
  ⟨F.equiv, F.graph_definable⟩

def ofMap {B : Base (M := M)} {k : ℕ} (a b : Chart B k)
    (F : (Fin a.arity → M) → (Fin b.arity → M))
    (hF : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain F))
    (hbij : Set.BijOn F a.domain b.domain) : UnderlyingIso a b where
  equiv := Set.BijOn.equiv F hbij
  graph_definable := by
    change DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv)
      {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F u.val)}
    have he : {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F u.val)} = graphOn a.domain F := by
      ext w
      rw [graphOn_exists]
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨u.val, u.property, hu⟩
      · rintro ⟨u, hu, he⟩
        exact ⟨⟨u, hu⟩, he⟩
    rw [he]
    exact hF

end DiamondIntegral.Section4.RVForgetScissors
