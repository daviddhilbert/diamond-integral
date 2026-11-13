import «section 4».RVGraphComposition
import «section 4».RVUnderlyingProducts

/-! Original-base RV isomorphisms compose, and measured isomorphisms
retain their corrected-weight equation under inverse, composition and
products. These are actual definable graph constructions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVUnderlyingIsomorphisms
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem Iso.extension_bijOn {B : Base (M := M)} {k l : ℕ} {a : Chart B k} {b : Chart B l} (F : Iso a b) :
    Set.BijOn F.extension a.domain b.domain := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Set.mem_of_eq_of_mem (F.extension_on ⟨x, hx⟩) (F.equiv ⟨x, hx⟩).property
  · intro x hx y hy h
    have he : F.equiv ⟨x, hx⟩ = F.equiv ⟨y, hy⟩ := Subtype.ext
      ((F.extension_on ⟨x, hx⟩).symm.trans (h.trans (F.extension_on ⟨y, hy⟩)))
    exact congrArg Subtype.val (F.equiv.injective he)
  · intro y hy
    let v : b.domain := ⟨y, hy⟩
    let u := F.equiv.symm v
    refine ⟨u.val, u.property, ?_⟩
    exact (F.extension_on u).trans (congrArg Subtype.val (F.equiv.apply_symm_apply v))

def trans {B : Base (M := M)} {k l m : ℕ} {a : Chart B k} {b : Chart B l} {c : Chart B m}
    (F : Iso a b) (G : Iso b c) : Iso a c :=
  ofMap a c (G.extension ∘ F.extension)
    (RVGraphComposition.graph_compose_definable B a.domain b.domain F.extension G.extension
      F.extension_graph G.extension_graph F.extension_bijOn.1)
    (G.extension_bijOn.comp F.extension_bijOn)

theorem trans_equiv_coe {B : Base (M := M)} {k l m : ℕ} {a : Chart B k} {b : Chart B l} {c : Chart B m}
    (F : Iso a b) (G : Iso b c) (u : a.domain) :
    ((trans F G).equiv u).val = (G.equiv (F.equiv u)).val := by
  change G.extension (F.extension u.val) = _
  rw [F.extension_on, G.extension_on]

end DiamondIntegral.Section4.RVUnderlyingIsomorphisms

namespace DiamondIntegral.Section4.RVMeasuredIsomorphisms
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def underlying {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) : RVUnderlyingIsomorphisms.Iso a b :=
  ⟨F.equiv, F.graph_definable⟩

def refl {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Iso a a where
  equiv := (RVUnderlyingIsomorphisms.refl a).equiv
  graph_definable := (RVUnderlyingIsomorphisms.refl a).graph_definable
  weight_eq _ := rfl

def symm {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) : Iso b a where
  equiv := F.equiv.symm
  graph_definable := (RVUnderlyingIsomorphisms.symm (underlying F)).graph_definable
  weight_eq u := by
    have h := F.weight_eq (F.equiv.symm u)
    rw [F.equiv.apply_symm_apply] at h
    exact h.symm

def trans {B : Base (M := M)} {k : ℕ} {a b c : Chart B k} (F : Iso a b) (G : Iso b c) : Iso a c where
  equiv := (RVUnderlyingIsomorphisms.trans (underlying F) (underlying G)).equiv
  graph_definable := (RVUnderlyingIsomorphisms.trans (underlying F) (underlying G)).graph_definable
  weight_eq u :=
    (F.weight_eq u).trans ((G.weight_eq (F.equiv u)).trans
      (congrArg c.correctedWeight (RVUnderlyingIsomorphisms.trans_equiv_coe (underlying F) (underlying G) u)).symm)

def productIso {B : Base (M := M)} {k l : ℕ} {a b : Chart B k} {c d : Chart B l}
    (F : Iso a b) (G : Iso c d) : Iso (product a c) (product b d) where
  equiv := (RVUnderlyingProducts.productIso (underlying F) (underlying G)).equiv
  graph_definable := (RVUnderlyingProducts.productIso (underlying F) (underlying G)).graph_definable
  weight_eq u := by
    let x : a.domain := ⟨u.val ∘ headIndex c.arity a.arity, u.property.1⟩
    let y : c.domain := ⟨u.val ∘ tailIndex c.arity a.arity, u.property.2⟩
    change (product a c).correctedWeight u.val =
      (product b d).correctedWeight (join d.arity b.arity (F.equiv x).val (G.equiv y).val)
    calc
      (product a c).correctedWeight u.val =
          (product a c).correctedWeight (join c.arity a.arity x.val y.val) :=
        congrArg (product a c).correctedWeight (join_reconstruct c.arity a.arity u.val).symm
      _ = a.correctedWeight x.val * c.correctedWeight y.val := product_weight_join a c x.val y.val
      _ = b.correctedWeight (F.equiv x).val * d.correctedWeight (G.equiv y).val :=
        congrArg₂ (· * ·) (F.weight_eq x) (G.weight_eq y)
      _ = (product b d).correctedWeight (join d.arity b.arity (F.equiv x).val (G.equiv y).val) :=
        (product_weight_join b d (F.equiv x).val (G.equiv y).val).symm

end DiamondIntegral.Section4.RVMeasuredIsomorphisms
