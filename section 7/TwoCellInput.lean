import «section 7».TwoCells
import «section 6».StandardContractionExistence

/-! Lemma 7.20 (`decom:into:2:units`) as an explicit, replaceable input.

**Temporary input.** By the author's decision of 2026-11-19 ("Input + parallel
build", the same arrangement as for Lemma 7.14), Lemma 7.20 is stated here
precisely and used as a hypothesis `Lemma720 M G` by the later results of
Section 7. A separate session proves it. Downstream theorems take
`(h720 : Lemma720 M G)` explicitly, so the input is visible in every type that
uses it, until it is discharged.

The paper's statement: let `A ⊆ VF²` be a proper invariant set. Then there is a
standard contraction `T̂_σ` of `A` such that `A_s` is a `2`-cell for every
`s ∈ T̂_σ(A)`. Lemma 7.22 applies it to a set with retained RV labels ("its
proof is uniform in such labels").

Formal reading:
* the base is a substructure `T` with support data `V ⊆ T ⊆ acl(V)` (`V` a set
  of VF names whose algebraic closure field has a nontrivial valuation), as for
  Lemma 7.14, so that it also covers the bases `S⟨a⟩` (GAP-REPAIRS 9);
* `A ⊆ VF² × RVʳ` is proper invariant, with `r` retained RV labels; `r = 0` is
  the printed statement;
* a standard contraction is Section 6's `StandardContraction A e` in some
  coordinate order `e` (the normalization, the ordered program and its lift),
  and `T̂_σ(A)` is its RV target, onto which `contraction` maps `A`;
* `A_s` is the fibre of the contraction over `s`, read in the order
  `(x_{e 0}, x_{e 1})` (`cellAt`). The first stage contracts `x_{e 1}`, so the
  second coordinate carries the RV-discs `t^♯ + ε(a)`, as in Definition 7.19.
  The retained labels of `A` are part of `s`, so `A_s` lies over one label value;
* "`2`-cell" is Definition 7.19 (`TwoCells.IsTwoCell`) with its data definable
  over `T ∪ s` (`DefinableTwoCell`). Definition 7.17 asks the set and the
  positioning bijection to be definable; under the paper's conventions the
  fibre `A_s` and its data are definable over the base with the parameter `s`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.TwoCellInput
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

section Cells
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Definition 7.19 with its data definable over `S`: the cell, the graph of
the positioning function on the first projection, the paradigm, and in the
balanced case the other paradigm. -/
def DefinableTwoCell (S : Set M) (C : Set (VF M × VF M)) : Prop :=
  (∃ t₁ t₂ : RVInfinity M, ∀ p ∈ C, rv M p.1 = t₁ ∧ rv M p.2 = t₂) ∧ IsOneCell (first C) ∧
    ∃ ε : VF M → VF M, ∃ t : RV M,
      (∀ a ∈ first C, fibre C a = (· + ε a) '' sharpSet t.val) ∧ PositioningCase C ε t ∧
      S.Definable LRV {z : Fin 2 → M | ∃ p ∈ C, z = ![p.1.val, p.2.val]} ∧
      S.Definable LRV {z : Fin 2 → M | ∃ a ∈ first C, z = ![a.val, (ε a).val]} ∧
      S.Definable₁ LRV {t.val.val} ∧
      ∀ t₁ : RVInfinity M, Balanced C ε t₁ t.val → S.Definable₁ LRV {t₁.val}

theorem DefinableTwoCell.isTwoCell {S : Set M} {C : Set (VF M × VF M)} (h : DefinableTwoCell S C) :
    IsTwoCell C := by
  obtain ⟨h1, h2, ε, t, h3, h4, -⟩ := h
  exact ⟨h1, h2, ε, t, h3, h4⟩

end Cells

variable (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The fibre `A_s` of a standard contraction over `s`, read in the order
`(x_{e 0}, x_{e 1})`. -/
def cellAt {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VF M) G] {S : Set M} {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 2 r) S} {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G) A e) (s : F.rvTarget) : Set (VF M × VF M) :=
  {q | ∃ p : A, F.contraction p = s ∧ q = (p.val.1 (e 0), p.val.1 (e 1))}

/-- **Lemma 7.20 (`decom:into:2:units`), explicit replaceable input.** A proper
invariant `A ⊆ VF² × RVʳ` has a standard contraction whose fibres over the
points `s` of its RV target are `2`-cells definable over `T ∪ s`. -/
def Lemma720 : Prop :=
  ∀ (_hc : CanonicalStructure.IsCanonical (M := M)) (_h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (_hκ : Cardinal.aleph0 < κ) (_hs : Saturated M κ)
    (_hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (V : Set M) (_hV : ∀ x ∈ V, iVF x) (_hVT : V ⊆ (T : Set M))
    (_hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (_hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (_hsmall : Cardinal.mk (T : Set M) < κ)
    (_hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 2 r) (T : Set M)) (_hA : ProperInvariant (T : Set M) A.carrier),
    ∃ (e : Equiv.Perm (Fin 2)) (F : StandardContraction (G := G) A e), ∀ s : F.rvTarget,
      DefinableTwoCell ((T : Set M) ∪ Set.range (rvValues s.val.2)) (cellAt F s)

end DiamondIntegral.Section7.TwoCellInput
