import «section 4».RVResiduePullback

/-! Finite descriptions of residue-field decoders by scaled coordinate
maps. Every actual RV-definable relation pulls back to a pure-field
definable relation on such a cover. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueScaledCovers
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure Piece (α : Type) (n : ℕ) where
  guard : Set (α → ModelResidue M)
  definable : PureDef guard
  scale : Fin n → CanonicalRV.RVSort M
  coord : Fin n → α

def Piece.value {α : Type} {n : ℕ} (p : Piece (M := M) α n) (x : α → ModelResidue M) :
    Fin n → CanonicalRV.RVSort M := residueScale p.scale (x ∘ p.coord)

structure Cover {α : Type} {n : ℕ} (D : Set (α → ModelResidue M))
    (decode : (α → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)) where
  Index : Type
  finite : Finite Index
  piece : Index → Piece (M := M) α n
  covers : ∀ x ∈ D, ∃ i, x ∈ (piece i).guard
  agrees : ∀ i x, x ∈ D → x ∈ (piece i).guard → decode x = (piece i).value x

theorem pullback_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {α : Type} {n : ℕ} {D : Set (α → ModelResidue M)} (hD : PureDef D)
    {decode : (α → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)} (C : Cover D decode)
    {B : Base (M := M)} (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ : Fin n => .rv) A) :
    PureDef {x | x ∈ D ∧ rvValues (decode x) ∈ A} := by
  letI : Finite C.Index := C.finite
  have hi (i : C.Index) : PureDef {x | x ∈ D ∧ x ∈ (C.piece i).guard ∧
      rvValues ((C.piece i).value x) ∈ A} :=
    hD.inter ((C.piece i).definable.inter
      (RVResiduePullback.scaled_coordinates_definable hc A hA
        (C.piece i).scale (C.piece i).coord))
  have h := Set.definable_iUnion_of_finite hi
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hx, ha⟩
    obtain ⟨i, hi⟩ := C.covers x hx
    exact ⟨i, hx, hi, (C.agrees i x hx hi) ▸ ha⟩
  · rintro ⟨i, hx, hi, ha⟩
    exact ⟨hx, (C.agrees i x hx hi).symm ▸ ha⟩

def Piece.reindex {α β : Type} {n : ℕ} (p : Piece (M := M) α n) (π : α → β) :
    Piece (M := M) β n where
  guard := {x | x ∘ π ∈ p.guard}
  definable := p.definable.preimage_comp π
  scale := p.scale
  coord := π ∘ p.coord

def Cover.reindex {α β : Type} {n : ℕ} {D : Set (α → ModelResidue M)}
    {decode : (α → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)}
    (C : Cover D decode) (π : α → β) :
    Cover {x : β → ModelResidue M | x ∘ π ∈ D} (fun x => decode (x ∘ π)) where
  Index := C.Index
  finite := C.finite
  piece i := (C.piece i).reindex π
  covers x hx := C.covers (x ∘ π) hx
  agrees i x hx hi := C.agrees i (x ∘ π) hx hi

def Piece.prod {α β : Type} {n m : ℕ} (p : Piece (M := M) α n)
    (q : Piece (M := M) β m) : Piece (M := M) (α ⊕ β) (n + m) where
  guard := {x | x ∘ Sum.inl ∈ p.guard ∧ x ∘ Sum.inr ∈ q.guard}
  definable := (p.definable.preimage_comp Sum.inl).inter (q.definable.preimage_comp Sum.inr)
  scale := Fin.addCases p.scale q.scale
  coord := Fin.addCases (Sum.inl ∘ p.coord) (Sum.inr ∘ q.coord)

def Cover.prod {α β : Type} {n m : ℕ} {D : Set (α → ModelResidue M)}
    {E : Set (β → ModelResidue M)}
    {decode : (α → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)}
    {decode' : (β → ModelResidue M) → (Fin m → CanonicalRV.RVSort M)}
    (C : Cover D decode) (C' : Cover E decode') :
    Cover {x : α ⊕ β → ModelResidue M | x ∘ Sum.inl ∈ D ∧ x ∘ Sum.inr ∈ E}
      (fun x => Fin.addCases (decode (x ∘ Sum.inl)) (decode' (x ∘ Sum.inr))) where
  Index := C.Index × C'.Index
  finite := by letI := C.finite; letI := C'.finite; infer_instance
  piece i := (C.piece i.1).prod (C'.piece i.2)
  covers x hx := by
    obtain ⟨i, hi⟩ := C.covers _ hx.1
    obtain ⟨j, hj⟩ := C'.covers _ hx.2
    exact ⟨(i, j), hi, hj⟩
  agrees i x hx hi := by
    rw [C.agrees i.1 _ hx.1 hi.1, C'.agrees i.2 _ hx.2 hi.2]
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [Piece.value, Piece.prod, residueScale, Function.comp_apply,
        Fin.addCases_left, Fin.addCases_right]

end DiamondIntegral.Section4.RVResidueScaledCovers
