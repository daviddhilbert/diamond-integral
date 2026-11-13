import «section 4».RVForgetScissors
import «section 4».RVCoordinateMaps
import «section 4».RVSharpCharts
import «section 4».FiniteTupleSwap

/-! Actual definable underlying RV bijections between charts of possibly
different degrees. Coordinates and volume forms are forgotten, while the
original parameter base and the full graph are retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVUnderlyingIsomorphisms
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Iso {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l) where
  equiv : a.domain ≃ b.domain
  graph_definable : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv)
    {w | ∃ u : a.domain, w = join b.arity a.arity u.val (equiv u).val}

def ofFixed {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : RVForgetScissors.UnderlyingIso a b) : Iso a b :=
  ⟨F.equiv, F.graph_definable⟩

def toFixed {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) : RVForgetScissors.UnderlyingIso a b :=
  ⟨F.equiv, F.graph_definable⟩

def ofMap {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (F : (Fin a.arity → M) → (Fin b.arity → M))
    (hF : DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain F))
    (hbij : Set.BijOn F a.domain b.domain) : Iso a b where
  equiv := Set.BijOn.equiv F hbij
  graph_definable := by
    have he : {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F u.val)} = graphOn a.domain F := by
      ext w
      rw [graphOn_exists]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u.val, u.property, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hu⟩, rfl⟩
    change DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv)
      {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F u.val)}
    rw [he]
    exact hF

def refl {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Iso a a :=
  ofMap a a id (RVSharpCharts.identity_graph_definable B a.domain a.domain_definable)
    (Set.bijOn_id a.domain)

def symm {B : Base (M := M)} {k l : ℕ} {a : Chart B k} {b : Chart B l} (F : Iso a b) : Iso b a where
  equiv := F.equiv.symm
  graph_definable := by
    have h := F.graph_definable.image_real (blockSwap a.arity b.arity)
    have he : {w | ∃ v : b.domain, w = join a.arity b.arity v.val (F.equiv.symm v).val} =
        (fun w => w ∘ blockSwap a.arity b.arity) ''
          {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F.equiv u).val} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨join b.arity a.arity (F.equiv.symm v).val v.val, ⟨F.equiv.symm v, ?_⟩, ?_⟩
        · rw [F.equiv.apply_symm_apply]
        · exact join_blockSwap a.arity b.arity v.val (F.equiv.symm v).val
      · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
        refine ⟨F.equiv u, ?_⟩
        rw [F.equiv.symm_apply_apply]
        exact join_blockSwap a.arity b.arity (F.equiv u).val u.val
    rw [he]
    exact h

def Iso.extension {B : Base (M := M)} {k l : ℕ} {a : Chart B k} {b : Chart B l} (F : Iso a b)
    (u : Fin a.arity → M) : Fin b.arity → M :=
  if hu : u ∈ a.domain then (F.equiv ⟨u, hu⟩).val else fun _ => iRVZero

theorem Iso.extension_on {B : Base (M := M)} {k l : ℕ} {a : Chart B k} {b : Chart B l} (F : Iso a b)
    (u : a.domain) : F.extension u.val = (F.equiv u).val := by
  simp only [Iso.extension, dite_eq_left u.property]

theorem Iso.extension_graph {B : Base (M := M)} {k l : ℕ} {a : Chart B k} {b : Chart B l} (F : Iso a b) :
    DefinableOverBase B (fun _ : Fin (b.arity + a.arity) => .rv) (graphOn a.domain F.extension) := by
  have he : graphOn a.domain F.extension = {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F.equiv u).val} := by
    ext w
    rw [graphOn_exists]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, congrArg (join b.arity a.arity u) (F.extension_on ⟨u, hu⟩)⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, congrArg (join b.arity a.arity u.val) (F.extension_on u).symm⟩
  rw [he]
  exact F.graph_definable

end DiamondIntegral.Section4.RVUnderlyingIsomorphisms
