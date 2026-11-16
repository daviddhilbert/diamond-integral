import «section 6».ZeroExtendedScalarGraphTemplates

/-! A zero-extended parameter graph gives exactly the actual complete
scalar code extension, including all codes outside the current domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

theorem scalarGraphDomain_at
    (R : Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) → M)) (a : ι → M)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
    (f : Map A B) (hSection : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawVFSpace 1) f.graph)
    (x : Fin n ⊕ Fin r → M) : Sum.elim a x ∈ scalarGraphDomain R ↔
      x ∈ (rawMixedSpace n r).preimage A.carrier := by
  constructor
  · rintro ⟨y,hy⟩
    have hEta : y=(fun _ : Fin 1 => y 0) := by funext i; fin_cases i; rfl
    rw [hEta] at hy
    exact ((scalarCodeExtension_graph f x (y 0)).mp ((Set.ext_iff.mp hSection _).mp hy)).1
  · intro hx
    exact ⟨fun _ => scalarCodeExtension f x,(Set.ext_iff.mp hSection _).mpr
      ((scalarCodeExtension_graph f x _).mpr ⟨hx,rfl⟩)⟩

theorem zeroExtendedScalarGraph_at
    (R : Set (ι ⊕ ((Fin n ⊕ Fin r) ⊕ Fin 1) → M)) (a : ι → M)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
    (f : Map A B) (hSection : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawVFSpace 1) f.graph)
    (x : Fin n ⊕ Fin r → M) (y : M) :
    Sum.elim a (Sum.elim x (fun _ : Fin 1 => y)) ∈ zeroExtendedScalarGraph R ↔ scalarCodeExtension f x=y := by
  have hEntry : Sum.elim a (Sum.elim x (fun _ : Fin 1 => y)) ∈ R ↔
      x ∈ (rawMixedSpace n r).preimage A.carrier ∧ scalarCodeExtension f x=y :=
    (Set.ext_iff.mp hSection _).trans (scalarCodeExtension_graph f x y)
  change (Sum.elim a (Sum.elim x (fun _ : Fin 1 => y)) ∈ R ∨
    (Sum.elim a x ∉ scalarGraphDomain R ∧ y=iVFZero)) ↔ scalarCodeExtension f x=y
  rw [hEntry,scalarGraphDomain_at R a f hSection x]
  by_cases hx : x ∈ (rawMixedSpace n r).preimage A.carrier
  · simp only [hx,true_and,not_true_eq_false,false_and,or_false]
  · simp only [hx,false_and,not_false_eq_true,true_and,false_or]
    rw [scalarCodeExtension,dite_eq_right hx]
    exact eq_comm

end DiamondIntegral.Section6
