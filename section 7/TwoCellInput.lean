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
* `A_s` is the fibre of the contraction over `s`, in the normalized
  coordinates of the contraction (the preliminary adjustment by Remark
  `spec:addendum` that every standard contraction may make), read in the order
  `(x_{e 0}, x_{e 1})` (`cellAt`). In the original coordinates the statement
  fails as soon as `A` has a point with a zero coordinate: the normalization
  moves `0`, and the fibre through such a point meets several RV-discs. On a
  fibre the core bits of the normalization are constant (they are tags in `s`),
  so the normalized fibre is the original one translated by a constant vector
  definable over `T`; for doubly bounded `A` the two readings agree. The first stage contracts `x_{e 1}`, so the
  second coordinate carries the RV-discs `t^♯ + ε(a)`, as in Definition 7.19.
  The retained labels of `A` are part of `s`, so `A_s` lies over one label value;
* "`2`-cell" is Definition 7.19 (`TwoCells.IsTwoCell`). The cell data are given
  uniformly in `s` (`UniformTwoCells`): a positioning function `ε(s, ·)`, a
  paradigm `t(s)`, the second paradigm `t₁(s)` of a balanced cell and the kind
  `kind(s) ∈ {0, 1, 2}` (constant, narrow image, balanced), with graphs and kind
  pieces definable over `T`. Definition 7.17 asks the set and the positioning
  bijection to be definable, and Lemma 7.22 uses that the proof of 7.20 "is
  uniform in such labels": it applies Lemma 6.38 once to the family of
  positioning functions with `s` as a retained label. Since a positioning
  function is only determined up to a ball, this uniformity cannot be recovered
  afterwards and is part of the statement. -/

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

/-- The narrow-image case of Definition 7.19: `ε` is injective with the
disc-to-disc property and its image is an open disc of radius at least
`vrv(t)`. -/
def NarrowCase (C : Set (VF M × VF M)) (ε : VF M → VF M) (t : RV M) : Prop :=
  Set.InjOn ε (first C) ∧ DiscToDisc (first C) ε ∧
    ∃ x : VF M, ∃ γ : Gamma M, Subtype.val '' (ε '' first C) =
      BallImaginaries.underlying (openDiscCode x γ) ∧ Values.vrv t.val ≤ γ.val

/-- Definition 7.19 with given data: positioning function `ε`, paradigm `t`,
second paradigm `t₁` and kind `k` (`0` constant, `1` narrow image,
`2` balanced). -/
def CellWith (C : Set (VF M × VF M)) (ε : VF M → VF M) (t : RV M) (t₁ : RVInfinity M) (k : Fin 3) : Prop :=
  (∃ u₁ u₂ : RVInfinity M, ∀ p ∈ C, rv M p.1 = u₁ ∧ rv M p.2 = u₂) ∧ IsOneCell (first C) ∧
    (∀ a ∈ first C, fibre C a = (· + ε a) '' sharpSet t.val) ∧
    (k = 0 → ∀ a ∈ first C, ∀ a' ∈ first C, ε a = ε a') ∧
    (k = 1 → NarrowCase C ε t) ∧
    (k = 2 → Balanced C ε t₁ t.val)

theorem CellWith.isTwoCell {C : Set (VF M × VF M)} {ε : VF M → VF M} {t : RV M} {t₁ : RVInfinity M} {k : Fin 3}
    (h : CellWith C ε t t₁ k) : IsTwoCell C := by
  obtain ⟨h1, h2, h3, h0, hn, hb⟩ := h
  refine ⟨h1, h2, ε, t, h3, ?_⟩
  match k, h0, hn, hb with
  | 0, h0, _, _ => exact Or.inl (h0 rfl)
  | 1, _, hn, _ => exact Or.inr (Or.inl (hn rfl))
  | 2, _, _, hb => exact Or.inr (Or.inr ⟨t₁, hb rfl⟩)

end Cells

variable (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The fibre `A_s` of a standard contraction over `s`, in the normalized
coordinates of the contraction, read in the order `(x_{e 0}, x_{e 1})`. -/
def cellAt {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VF M) G] {S : Set M} {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 2 r) S} {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G) A e) (s : F.rvTarget) : Set (VF M × VF M) :=
  {q | ∃ p : A, F.contraction p = s ∧
    q = ((F.normalization.point p.val).1 (e 0), (F.normalization.point p.val).1 (e 1))}

/-- **Uniform cell data** for the fibres of a standard contraction: functions of
the RV point `s` of the target, with graphs and kind pieces definable over the
base, such that every fibre `cellAt F s` is a `2`-cell with the data at `s`. -/
def UniformTwoCells {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VF M) G] {S : Set M} {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 2 r) S} {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G) A e) : Prop :=
  ∃ (ε : (Fin F.arity → RVInfinity M) → VF M → VF M) (t : (Fin F.arity → RVInfinity M) → RV M)
    (t₁ : (Fin F.arity → RVInfinity M) → RVInfinity M) (kind : (Fin F.arity → RVInfinity M) → Fin 3),
    S.Definable LRV {z : Fin (2 + F.arity) → M | ∃ s : F.rvTarget, ∃ a ∈ first (cellAt F s),
      z = Fin.append ![a.val, (ε s.val.2 a).val] (rvValues s.val.2)} ∧
    S.Definable LRV {z : Fin (1 + F.arity) → M | ∃ s : F.rvTarget,
      z = Fin.append ![(t s.val.2).val.val] (rvValues s.val.2)} ∧
    S.Definable LRV {z : Fin (1 + F.arity) → M | ∃ s : F.rvTarget, kind s.val.2 = 2 ∧
      z = Fin.append ![(t₁ s.val.2).val] (rvValues s.val.2)} ∧
    (∀ i : Fin 3, S.Definable LRV {z : Fin F.arity → M | ∃ s : F.rvTarget, kind s.val.2 = i ∧
      z = rvValues s.val.2}) ∧
    ∀ s : F.rvTarget, CellWith (cellAt F s) (ε s.val.2) (t s.val.2) (t₁ s.val.2) (kind s.val.2)

/-- **Lemma 7.20 (`decom:into:2:units`), explicit replaceable input.** A proper
invariant `A ⊆ VF² × RVʳ` has a standard contraction whose fibres over the
points `s` of its RV target are `2`-cells, with cell data uniform in `s` and
definable over `T`. -/
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
    ∃ (e : Equiv.Perm (Fin 2)) (F : StandardContraction (G := G) A e), UniformTwoCells F

end DiamondIntegral.Section7.TwoCellInput
