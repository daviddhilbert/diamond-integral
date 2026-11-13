import «section 4».RVMeasuredCharts

/-! The actual full RV preimage of a weighted Gamma chart, with its
partial volume form over the same base. An actual RV-induced Gamma
isomorphism gives an isomorphism of these measured RV objects. This is
the object/isomorphism bridge, not a Grothendieck tensor theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVSharpCharts
open FiniteTupleBlocks GammaRVChartPresentation RVMeasuredCharts

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def duplicate (n : ℕ) : Fin (n + n) → Fin n := join n n id id

theorem duplicate_head {α : Type*} (n : ℕ) (z : Fin n → α) :
    (z ∘ duplicate n) ∘ headIndex n n = z := by
  funext i
  simp [duplicate, Function.comp_apply]

theorem duplicate_tail {α : Type*} (n : ℕ) (z : Fin n → α) :
    (z ∘ duplicate n) ∘ tailIndex n n = z := by
  funext i
  simp [duplicate, Function.comp_apply]

theorem duplicate_tuple {α : Type*} (n : ℕ) (z : Fin n → α) :
    z ∘ duplicate n = join n n z z := by
  have h := join_reconstruct n n (z ∘ duplicate n)
  rw [duplicate_head, duplicate_tail] at h
  exact h.symm

theorem identity_graph_definable (B : Base (M := M)) {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) :
    DefinableOverBase B (fun _ : Fin (n + n) => .rv) (RVMeasuredCharts.graphOn I id) := by
  have h : DefinableOverBase B (fun _ : Fin (n + n) => .rv)
      ((fun z : Fin n → M => z ∘ duplicate n) '' I) := hI.image_real (duplicate n)
  have he : RVMeasuredCharts.graphOn I id = (fun z : Fin n → M => z ∘ duplicate n) '' I := by
    ext w
    change (w ∘ headIndex n n ∈ I ∧ w ∘ headIndex n n = w ∘ tailIndex n n) ↔
      ∃ z ∈ I, z ∘ duplicate n = w
    constructor
    · rintro ⟨hw, he⟩
      refine ⟨w ∘ headIndex n n, hw, ?_⟩
      rw [duplicate_tuple]
      exact (congrArg (join n n (w ∘ headIndex n n)) he).trans (join_reconstruct n n w)
    · rintro ⟨z, hz, rfl⟩
      rw [duplicate_head, duplicate_tail]
      exact ⟨hz, rfl⟩
  rw [he]
  exact h

def sharpChart {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n) : Chart B n where
  arity := n
  domain := sharp a.support
  domain_definable := sharp_definable a.support a.support_definable
  coordinate := id
  coordinate_definable := identity_graph_definable B _ (sharp_definable a.support a.support_definable)
  coordinate_proper := fun _ hu => hu.1
  finite_fibres := by
    intro t
    exact (Set.finite_singleton t).subset (fun _ h => h.2)
  volume := fun z => a.volume (codeValues z)
  volume_definable := by
    have h : DefinableOverBase B (fun _ : Fin (n + 1) => .rv)
        {w | Proper w ∧ Fin.tail (codeValues w) ∈ a.support ∧
          codeValue (w 0) = a.volume (Fin.tail (codeValues w))} := a.volume_definable
    convert h using 1
    ext w
    change (Fin.tail w ∈ sharp a.support ∧ NonzeroRV (w 0) ∧
      codeValue (w 0) = a.volume (codeValues (Fin.tail w))) ↔
      Proper w ∧ Fin.tail (codeValues w) ∈ a.support ∧
        codeValue (w 0) = a.volume (Fin.tail (codeValues w))
    constructor
    · rintro ⟨⟨hp, hI⟩, h0, he⟩
      exact ⟨(fun i => Fin.cases h0 (fun j => hp j) i), hI, he⟩
    · rintro ⟨hp, hI, he⟩
      exact ⟨⟨(fun i => hp i.succ), hI⟩, hp 0, he⟩

theorem sharpChart_weight {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (z : Fin n → M) :
    (sharpChart a).correctedWeight z = GammaWeightProfiles.correctedWeight a.volume (codeValues z) := rfl

def sharpIso {B : Base (M := M)} {n : ℕ} {a b : GammaWeightedCharts.Chart B n}
    (F : RVVolumeIso a b) : Iso (sharpChart a) (sharpChart b) where
  equiv := Set.BijOn.equiv F.lift F.lift_bijective
  graph_definable := by
    change DefinableOverBase B (fun _ : Fin (n + n) => .rv)
      {w | ∃ u : sharp a.support, w = join n n u.val (F.lift u.val)}
    convert F.lift_definable using 1
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      change join n n u.val (F.lift u.val) ∘ headIndex n n ∈ sharp a.support ∧
        join n n u.val (F.lift u.val) ∘ tailIndex n n =
          F.lift (join n n u.val (F.lift u.val) ∘ headIndex n n)
      have hh : join n n u.val (F.lift u.val) ∘ headIndex n n = u.val :=
        funext (join_head n n u.val (F.lift u.val))
      have ht : join n n u.val (F.lift u.val) ∘ tailIndex n n = F.lift u.val :=
        funext (join_tail n n u.val (F.lift u.val))
      rw [hh, ht]
      exact ⟨u.property, rfl⟩
    · rintro ⟨hu, he⟩
      exact ⟨⟨w ∘ headIndex n n, hu⟩, (join_reconstruct n n w).symm.trans
        (congrArg (join n n (w ∘ headIndex n n)) he)⟩
  weight_eq := by
    intro u
    let v : sharp a.support := u
    change a.volume (codeValues v.val) * (∏ i, codeValues v.val i) =
      b.volume (codeValues (F.lift v.val)) * ∏ i, codeValues (F.lift v.val) i
    rw [F.contraction v.val v.property, F.volume_eq (codeValues v.val) v.property.2]
    exact div_mul_cancel _ _

end DiamondIntegral.Section4.RVSharpCharts
