import «section 6».StandardContractionStages
import «section 6».InverseFibres
import «section 6».CarriedExceptionalSets
import «section 7».FibreRestriction

/-! Pulling a unary contraction stage back to a fibre product (for Lemma 7.21).

Let `D ⊆ VFⁿ × RV^q` and `E ⊆ VF × RV^r` be definable sets and `π : r → q` a
map of labels. The fibre product `D ×_π E ⊆ VF^{n+1} × RV^q` consists of the
points `(x, t)` with `(x₁, …, xₙ, t) ∈ D` and `(x_{n+1}, t ∘ π) ∈ E`
(`pullbackProd`). It is definable, proper invariant when `D` and `E` are, VF-doubly
bounded when `D` and `E` are, and has finite RV fibres over VF points when `D`
has.

Let `H` be a unary standard contraction stage of `E`, with lift `E → T` and new
label set `a`. Its pullback (`pullbackStage`) is a standard contraction stage of
`D ×_π E` with `q + a` labels. Its lift sends `(x, t)` to
`((x₁, …, xₙ, y), (t, w))`, where `H(x_{n+1}, t ∘ π) = (y, w)`. Its target is the
set of `(x, t, w)` with `(x₁, …, xₙ, t) ∈ D`, `(x_{n+1}, w) ∈ T` and
`w ∘ o_H = t ∘ π`, where `o_H` is the embedding of the old labels of `H`
(`pullbackTarget`). The old labels are the first `q`, and the leading label is
the leading label of `H`.

* The graph fibre of the lift over the labels `(u, v)` is the product of the
  fibre `D_u` (when `v` extends `u`) with the graph fibre of `H` over
  `(u ∘ π, w)`, where `w` is the last `a` coordinates of `v`. The same holds for
  the inverse. So the radii of the lift combine the named radii of `D` with
  those of `H`, and the lift is a proper covariant homeomorphism
  (`IsGraphProduct`, `pullbackLift_home`).
* At a point `(x, t)` whose image `(x_{n+1}, t ∘ π)` avoids the exceptional set
  of `H`, a chart of the lift is `(x₁, …, xₙ, F₁(x_{n+1}))` for a chart `F₁` of
  `H`. Its derivative is block diagonal, the identity times the derivative of
  `H`, so its determinant is `1` (`pullbackLift_unitDerivative`). The fibre `D_t`
  is open, as a union of balls, so the chart is defined on a ball.
* The exceptional set is `D ×_π E_H`, where `E_H` is the exceptional set of `H`.
  A point of `D ×_π E_H` whose `n + 1` VF coordinates are algebraically
  independent has an independent last coordinate, which cannot lie in `E_H`
  since `E_H` has VF dimension `0`. Hence `D ×_π E_H` has VF dimension `< n + 1`
  (`pullbackProd_dim_lt`); this step uses canonicity, saturation and smallness.

The contracted set of the pulled-back stage consists of the `(x, t, w)` with
`(x, t) ∈ D`, `w` in the contracted set of `H` and `w ∘ o_H = t ∘ π`
(`mem_pullbackStage_contracted`). When `D` has no VF coordinates (`n = 0`), the
stage only needs bounded RV support of `D` (`pullbackStageZero`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.PullbackStages
open DiamondIntegral.Section6 DiamondIntegral.Section2
open SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

/-! ### Definability of conditions on reindexed coordinates -/

section Codes

variable {a b c d : ℕ}

/-- A map of mixed tuples that only reindexes the real codes has definable
preimages. -/
theorem definable_preimage_of_reindex (g : Mixed M a b → Mixed M c d)
    (ρ : Fin c ⊕ Fin d → Fin a ⊕ Fin b) (hρ : ∀ p, mixedValues p ∘ ρ = mixedValues (g p))
    {T : Set (Mixed M c d)} (hT : (rawMixedSpace (M := M) c d).Definable S T) :
    (rawMixedSpace (M := M) a b).Definable S {p | g p ∈ T} := by
  have hG : S.DefinableMap LRV (fun z : Fin a ⊕ Fin b → M => z ∘ ρ) :=
    fun _ => Set.DefinableFun.proj LRV
  have h := mixedValues_preimage_definable (S := S)
    ((fun z : Fin a ⊕ Fin b → M => z ∘ ρ) ⁻¹' (rawMixedSpace (M := M) c d).preimage T)
    (hT.preimage_map hG)
  convert h using 1
  ext p
  change g p ∈ T ↔ mixedValues p ∘ ρ ∈ (rawMixedSpace (M := M) c d).preimage T
  rw [hρ p]
  have h' := Space.preimage_decode (rawMixedSpace (M := M) c d) T
    ⟨mixedValues (g p), mixedValues_mem_domain _⟩
  rw [decode_mixedValues] at h'
  exact h'.symm

/-- The condition that two RV coordinates agree is definable. -/
theorem definable_label_eq (i j : Fin b) :
    (rawMixedSpace (M := M) a b).Definable S {p | p.2 i = p.2 j} := by
  have h := mixedValues_preimage_definable (M := M) (n := a) (r := b) (S := S)
    {z | z (.inr i) = z (.inr j)}
    ((Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV))
  convert h using 1
  ext p
  exact Subtype.ext_iff

theorem definable_labels_eq {m : ℕ} (e₁ e₂ : Fin m → Fin b) :
    (rawMixedSpace (M := M) a b).Definable S {p | ∀ i, p.2 (e₁ i) = p.2 (e₂ i)} := by
  have hR : S.Definable LRV (⋂ i, {z : Fin a ⊕ Fin b → M | z (.inr (e₁ i)) = z (.inr (e₂ i))}) :=
    Set.definable_iInter_of_finite fun i =>
      (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have h := mixedValues_preimage_definable (M := M) (n := a) (r := b) (S := S) _ hR
  convert h using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact forall_congr' fun i => Subtype.ext_iff

/-- The real codes of `(x, t) ↦ (x₁…xₙ, t ∘ ι)`. -/
def initIndex {n q k : ℕ} (ι : Fin q → Fin k) : Fin n ⊕ Fin q → Fin (n + 1) ⊕ Fin k :=
  Sum.elim (fun i => .inl i.castSucc) (fun i => .inr (ι i))

/-- The real codes of `(x, t) ↦ (x_{n+1}, t ∘ κ)`. -/
def lastIndex {n r k : ℕ} (κ : Fin r → Fin k) : Fin 1 ⊕ Fin r → Fin (n + 1) ⊕ Fin k :=
  Sum.elim (fun _ => .inl (Fin.last n)) (fun j => .inr (κ j))

omit [M ⊨ Axioms.ACVF] in
theorem initIndex_mixedValues {n q k : ℕ} (ι : Fin q → Fin k) (p : Mixed M (n + 1) k) :
    mixedValues p ∘ initIndex ι = mixedValues ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q) := by
  funext i
  rcases i with i | i <;> rfl

omit [M ⊨ Axioms.ACVF] in
theorem lastIndex_mixedValues {n r k : ℕ} (κ : Fin r → Fin k) (p : Mixed M (n + 1) k) :
    mixedValues p ∘ lastIndex κ =
      mixedValues (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r) := by
  funext i
  rcases i with i | i <;> rfl

end Codes

/-! ### Radii of tuples with a separate last coordinate -/

section Radii

variable {n : ℕ}

/-- The radius tuple `(α, β₀)` on `VF^{n+1}`. -/
def snocRadius (α : Fin n → Gamma M) (β : Fin 1 → Gamma M) : Fin (n + 1) → Gamma M :=
  Fin.snoc α (β 0)

@[simp] theorem snocRadius_castSucc (α : Fin n → Gamma M) (β : Fin 1 → Gamma M) (j : Fin n) :
    snocRadius α β j.castSucc = α j := Fin.snoc_castSucc (α := fun _ => Gamma M) _ _ _

@[simp] theorem snocRadius_last (α : Fin n → Gamma M) (β : Fin 1 → Gamma M) :
    snocRadius α β (Fin.last n) = β 0 := Fin.snoc_last (α := fun _ => Gamma M) _ _

theorem congruent_init_of_snocRadius {α : Fin n → Gamma M} {β : Fin 1 → Gamma M}
    {x y : Fin (n + 1) → VF M} (h : Congruent (snocRadius α β) x y) :
    Congruent α (Fin.init x) (Fin.init y) := by
  intro j
  have h' := h j.castSucc
  rw [snocRadius_castSucc] at h'
  exact h'

theorem congruent_last_of_snocRadius {α : Fin n → Gamma M} {β : Fin 1 → Gamma M}
    {x y : Fin (n + 1) → VF M} (h : Congruent (snocRadius α β) x y) :
    Congruent β (fun _ => x (Fin.last n)) (fun _ => y (Fin.last n)) := by
  intro i
  rw [Subsingleton.elim i 0]
  have h' := h (Fin.last n)
  rw [snocRadius_last] at h'
  exact h'

theorem congruent_snocRadius {α : Fin n → Gamma M} {β : Fin 1 → Gamma M}
    {x y : Fin (n + 1) → VF M} (h₁ : Congruent α (Fin.init x) (Fin.init y))
    (h₂ : Congruent β (fun _ => x (Fin.last n)) (fun _ => y (Fin.last n))) :
    Congruent (snocRadius α β) x y := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snocRadius_last]
    exact h₂ 0
  · rw [snocRadius_castSucc]
    exact h₁ j

theorem namedGammaTuple_snocRadius {T : Set M} {α : Fin n → Gamma M} {β : Fin 1 → Gamma M}
    (hα : NamedGammaTuple T α) (hβ : NamedGammaTuple T β) :
    NamedGammaTuple T (snocRadius α β) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snocRadius_last]
    exact hβ 0
  · rw [snocRadius_castSucc]
    exact hα j

omit [M ⊨ Axioms.ACVF] in
theorem range_rvValues_comp_subset {k l : ℕ} (t : Fin k → RVInfinity M) (ι : Fin l → Fin k) :
    Set.range (rvValues (fun i => t (ι i))) ⊆ Set.range (rvValues t) := by
  rintro _ ⟨i, rfl⟩
  exact ⟨ι i, rfl⟩

omit [M ⊨ Axioms.ACVF] in
theorem base_comp_subset {k l : ℕ} (t : Fin k → RVInfinity M) (ι : Fin l → Fin k) :
    S ∪ Set.range (rvValues (fun i => t (ι i))) ⊆ S ∪ Set.range (rvValues t) :=
  Set.union_subset_union_right _ (range_rvValues_comp_subset t ι)

omit [M ⊨ Axioms.ACVF] in
theorem graphFibreBase_comp_subset {a b c d : ℕ} (u : Fin a → RVInfinity M)
    (v : Fin b → RVInfinity M) (σ : Fin c → Fin a) (τ : Fin d → Fin b) :
    graphFibreBase S (fun i => u (σ i)) (fun j => v (τ j)) ⊆ graphFibreBase S u v :=
  Set.union_subset_union (base_comp_subset u σ) (range_rvValues_comp_subset v τ)

end Radii

/-! ### Pulled-back sets -/

section Sets

variable {n q r k : ℕ}

/-- The condition `(p₁, …, pₙ, p.2 ∘ ι) ∈ D` is definable. -/
theorem definable_init_mem (D : DefSet (rawMixedSpace (M := M) n q) S) (ι : Fin q → Fin k) :
    (rawMixedSpace (M := M) (n + 1) k).Definable S
      {p | ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q) ∈ D.carrier} :=
  definable_preimage_of_reindex
    (fun p : Mixed M (n + 1) k => ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q))
    (initIndex ι) (initIndex_mixedValues ι) D.definable

/-- The condition `(p_{n+1}, p.2 ∘ κ) ∈ E` is definable. -/
theorem definable_last_mem (E : DefSet (rawMixedSpace (M := M) 1 r) S) (κ : Fin r → Fin k) :
    (rawMixedSpace (M := M) (n + 1) k).Definable S
      {p | (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r) ∈ E.carrier} :=
  definable_preimage_of_reindex
    (fun p : Mixed M (n + 1) k =>
      (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r))
    (lastIndex κ) (lastIndex_mixedValues κ) E.definable

/-- The fibre product `D ×_π E ⊆ VF^{n+1} × RV^q` of `D ⊆ VFⁿ × RV^q` and
`E ⊆ VF × RV^r` along the label map `π : r → q`: a point `(x, t)` lies in it
when `(x₁, …, xₙ, t) ∈ D` and `(x_{n+1}, t ∘ π) ∈ E`. -/
def pullbackProd (D : DefSet (rawMixedSpace (M := M) n q) S)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (π : Fin r → Fin q) :
    DefSet (rawMixedSpace (M := M) (n + 1) q) S where
  carrier := {p | ((Fin.init p.1, p.2) : Mixed M n q) ∈ D.carrier ∧
    (((fun _ => p.1 (Fin.last n)), p.2 ∘ π) : Mixed M 1 r) ∈ E.carrier}
  definable := (definable_init_mem D id).inter _ (definable_last_mem E π)

theorem mem_pullbackProd {D : DefSet (rawMixedSpace (M := M) n q) S}
    {E : DefSet (rawMixedSpace (M := M) 1 r) S} {π : Fin r → Fin q} (p : Mixed M (n + 1) q) :
    p ∈ (pullbackProd D E π).carrier ↔ ((Fin.init p.1, p.2) : Mixed M n q) ∈ D.carrier ∧
      (((fun _ => p.1 (Fin.last n)), p.2 ∘ π) : Mixed M 1 r) ∈ E.carrier :=
  Iff.rfl

/-- The target of the pulled-back stage: points `(x, t, w)` with
`(x₁, …, xₙ, t) ∈ D`, `(x_{n+1}, w) ∈ T` and `w ∘ o = t ∘ π`. -/
def pullbackTarget (D : DefSet (rawMixedSpace (M := M) n q) S) {a : ℕ}
    (T : DefSet (rawMixedSpace (M := M) 1 a) S) (π : Fin r → Fin q) (o : Fin r → Fin a) :
    DefSet (rawMixedSpace (M := M) (n + 1) (q + a)) S where
  carrier := {p | ((Fin.init p.1, fun i => p.2 (Fin.castAdd a i)) : Mixed M n q) ∈ D.carrier ∧
    (((fun _ => p.1 (Fin.last n)), fun j => p.2 (Fin.natAdd q j)) : Mixed M 1 a) ∈ T.carrier ∧
    ∀ i, p.2 (Fin.natAdd q (o i)) = p.2 (Fin.castAdd a (π i))}
  definable := (definable_init_mem D _).inter _
    ((definable_last_mem T _).inter _ (definable_labels_eq _ _))

theorem mem_pullbackTarget {D : DefSet (rawMixedSpace (M := M) n q) S} {a : ℕ}
    {T : DefSet (rawMixedSpace (M := M) 1 a) S} {π : Fin r → Fin q} {o : Fin r → Fin a}
    (p : Mixed M (n + 1) (q + a)) :
    p ∈ (pullbackTarget D T π o).carrier ↔
      ((Fin.init p.1, fun i => p.2 (Fin.castAdd a i)) : Mixed M n q) ∈ D.carrier ∧
      (((fun _ => p.1 (Fin.last n)), fun j => p.2 (Fin.natAdd q j)) : Mixed M 1 a) ∈ T.carrier ∧
      ∀ i, p.2 (Fin.natAdd q (o i)) = p.2 (Fin.castAdd a (π i)) :=
  Iff.rfl

theorem vfBounded_of_pullback {Z : Set (Mixed M (n + 1) k)} {D : Set (Mixed M n q)}
    {E : Set (Mixed M 1 r)} (σ : (Fin k → RVInfinity M) → Fin q → RVInfinity M)
    (τ : (Fin k → RVInfinity M) → Fin r → RVInfinity M)
    (hZ : ∀ p ∈ Z, ((Fin.init p.1, σ p.2) : Mixed M n q) ∈ D ∧
      (((fun _ => p.1 (Fin.last n)), τ p.2) : Mixed M 1 r) ∈ E)
    (hD : VFBounded D) (hE : VFBounded E) : VFBounded Z := by
  obtain ⟨γ, hγ⟩ := hD
  obtain ⟨δ, hδ⟩ := hE
  refine ⟨min γ δ, fun p hp i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (show (min γ δ).val ≤ δ.val from min_le_right _ _).trans (hδ _ (hZ p hp).2 0)
  · exact (show (min γ δ).val ≤ γ.val from min_le_left _ _).trans (hγ _ (hZ p hp).1 j)

theorem vfDoublyBounded_of_pullback {Z : Set (Mixed M (n + 1) k)} {D : Set (Mixed M n q)}
    {E : Set (Mixed M 1 r)} (σ : (Fin k → RVInfinity M) → Fin q → RVInfinity M)
    (τ : (Fin k → RVInfinity M) → Fin r → RVInfinity M)
    (hZ : ∀ p ∈ Z, ((Fin.init p.1, σ p.2) : Mixed M n q) ∈ D ∧
      (((fun _ => p.1 (Fin.last n)), τ p.2) : Mixed M 1 r) ∈ E)
    (hD : VFDoublyBounded D) (hE : VFDoublyBounded E) : VFDoublyBounded Z := by
  obtain ⟨γ, hγ⟩ := hD
  obtain ⟨δ, hδ⟩ := hE
  have h1 : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := inv_le_inv' (le_max_left γ δ)
  have h2 : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := inv_le_inv' (le_max_right γ δ)
  have h3 : γ.val ≤ (max γ δ).val := le_max_left γ δ
  have h4 : δ.val ≤ (max γ δ).val := le_max_right γ δ
  refine ⟨max γ δ, fun p hp i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · obtain ⟨hl, hu⟩ := hδ _ (hZ p hp).2 0
    exact ⟨h2.trans hl, hu.trans h4⟩
  · obtain ⟨hl, hu⟩ := hγ _ (hZ p hp).1 j
    exact ⟨h1.trans hl, hu.trans h3⟩

theorem rvBounded_of_pullback {Z : Set (Mixed M (n + 1) k)} {D : Set (Mixed M n q)}
    {E : Set (Mixed M 1 r)} (ι : Fin q → Fin k) (κ : Fin r → Fin k)
    (hZ : ∀ p ∈ Z, ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q) ∈ D ∧
      (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r) ∈ E)
    (hcover : ∀ j, (∃ i, ι i = j) ∨ ∃ i, κ i = j)
    (hD : RVSupportDoublyBounded D) (hE : RVSupportDoublyBounded E) :
    RVSupportDoublyBounded Z := by
  obtain ⟨γ, hγ⟩ := hD
  obtain ⟨δ, hδ⟩ := hE
  have h1 : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := inv_le_inv' (le_max_left γ δ)
  have h2 : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := inv_le_inv' (le_max_right γ δ)
  have h3 : γ.val ≤ (max γ δ).val := le_max_left γ δ
  have h4 : δ.val ≤ (max γ δ).val := le_max_right γ δ
  refine ⟨max γ δ, fun p hp j => ?_⟩
  rcases hcover j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨hl, hu⟩ := hγ _ (hZ p hp).1 i
    exact ⟨h1.trans hl, hu.trans h3⟩
  · obtain ⟨hl, hu⟩ := hδ _ (hZ p hp).2 i
    exact ⟨h2.trans hl, hu.trans h4⟩

theorem radii_of_pullback {Z : Set (Mixed M (n + 1) k)} {D : Set (Mixed M n q)}
    {E : Set (Mixed M 1 r)} (ι : Fin q → Fin k) (κ : Fin r → Fin k)
    (R : (Fin k → RVInfinity M) → Prop)
    (hZ : ∀ p, p ∈ Z ↔ ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q) ∈ D ∧
      (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r) ∈ E ∧ R p.2)
    (hD : ProperInvariant S D) (hE : ProperInvariant S E) (t : Fin k → RVInfinity M) :
    ∃ α : Fin (n + 1) → Gamma M, NamedRadii S t α ∧ AlphaInvariant α (vfFibre Z t) := by
  obtain ⟨αD, hαD, hInvD⟩ := hD.radii (fun i => t (ι i))
  obtain ⟨αE, hαE, hInvE⟩ := hE.radii (fun j => t (κ j))
  refine ⟨snocRadius αD αE, fun i => ?_, fun x y hxy => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [snocRadius_last]
      exact (hαE 0).mono (base_comp_subset t κ)
    · rw [snocRadius_castSucc]
      exact (hαD j).mono (base_comp_subset t ι)
  · change (x, t) ∈ Z ↔ (y, t) ∈ Z
    rw [hZ, hZ]
    exact and_congr (hInvD _ _ (congruent_init_of_snocRadius hxy))
      (and_congr (hInvE _ _ (congruent_last_of_snocRadius hxy)) Iff.rfl)

theorem properInvariant_of_pullback {Z : Set (Mixed M (n + 1) k)}
    (hZdef : (rawMixedSpace (M := M) (n + 1) k).Definable S Z)
    {D : Set (Mixed M n q)} {E : Set (Mixed M 1 r)} (ι : Fin q → Fin k) (κ : Fin r → Fin k)
    (R : (Fin k → RVInfinity M) → Prop)
    (hZ : ∀ p, p ∈ Z ↔ ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q) ∈ D ∧
      (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r) ∈ E ∧ R p.2)
    (hcover : ∀ j, (∃ i, ι i = j) ∨ ∃ i, κ i = j)
    (hD : ProperInvariant S D) (hE : ProperInvariant S E) : ProperInvariant S Z := by
  have hZ' : ∀ p ∈ Z, ((Fin.init p.1, fun i => p.2 (ι i)) : Mixed M n q) ∈ D ∧
      (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r) ∈ E :=
    fun p hp => ⟨((hZ p).mp hp).1, ((hZ p).mp hp).2.1⟩
  exact ⟨hZdef, vfBounded_of_pullback (fun t i => t (ι i)) (fun t j => t (κ j)) hZ'
      hD.vfBounded hE.vfBounded,
    rvBounded_of_pullback ι κ hZ' hcover hD.rvBounded hE.rvBounded,
    radii_of_pullback ι κ R hZ hD hE⟩

variable {D : DefSet (rawMixedSpace (M := M) n q) S} {E : DefSet (rawMixedSpace (M := M) 1 r) S}
  {π : Fin r → Fin q}

theorem pullbackProd_vfBounded (hD : VFBounded D.carrier) (hE : VFBounded E.carrier) :
    VFBounded (pullbackProd D E π).carrier :=
  vfBounded_of_pullback (fun t => t) (fun t => t ∘ π) (fun _ hp => hp) hD hE

theorem pullbackProd_rvBounded (hD : RVSupportDoublyBounded D.carrier) :
    RVSupportDoublyBounded (pullbackProd D E π).carrier := by
  obtain ⟨γ, hγ⟩ := hD
  exact ⟨γ, fun p hp i => hγ _ hp.1 i⟩

/-- The fibre product of proper invariant sets is proper invariant. -/
theorem pullbackProd_properInvariant (hD : ProperInvariant S D.carrier)
    (hE : ProperInvariant S E.carrier) : ProperInvariant S (pullbackProd D E π).carrier :=
  properInvariant_of_pullback (pullbackProd D E π).definable id π (fun _ => True)
    (fun _ => ⟨fun h => ⟨h.1, h.2, trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩)
    (fun j => Or.inl ⟨j, rfl⟩) hD hE

/-- The fibre product of VF-doubly bounded sets is VF-doubly bounded. -/
theorem pullbackProd_vfDoublyBounded (hD : VFDoublyBounded D.carrier)
    (hE : VFDoublyBounded E.carrier) : VFDoublyBounded (pullbackProd D E π).carrier :=
  vfDoublyBounded_of_pullback (fun t => t) (fun t => t ∘ π) (fun _ hp => hp) hD hE

/-- Finite RV fibres over VF points pass from `D` to the fibre product. -/
theorem pullbackProd_finite_fibres (hfin : ∀ x : Fin n → VF M, {u | (x, u) ∈ D.carrier}.Finite)
    (x : Fin (n + 1) → VF M) : {u | (x, u) ∈ (pullbackProd D E π).carrier}.Finite :=
  (hfin (Fin.init x)).subset fun _ hu => hu.1

theorem pullbackProd_mono {E' : DefSet (rawMixedSpace (M := M) 1 r) S}
    (h : E'.carrier ⊆ E.carrier) :
    (pullbackProd D E' π).carrier ⊆ (pullbackProd D E π).carrier :=
  fun _ hp => ⟨hp.1, h hp.2⟩

theorem pullbackTarget_properInvariant {a : ℕ} {T : DefSet (rawMixedSpace (M := M) 1 a) S}
    {o : Fin r → Fin a} (hD : ProperInvariant S D.carrier) (hT : ProperInvariant S T.carrier) :
    ProperInvariant S (pullbackTarget D T π o).carrier :=
  properInvariant_of_pullback (pullbackTarget D T π o).definable (Fin.castAdd a) (Fin.natAdd q)
    (fun t => ∀ i, t (Fin.natAdd q (o i)) = t (Fin.castAdd a (π i))) (fun _ => Iff.rfl)
    (fun j => Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j) hD hT

theorem pullbackTarget_vfBounded {a : ℕ} {T : DefSet (rawMixedSpace (M := M) 1 a) S}
    {o : Fin r → Fin a} (hD : VFBounded D.carrier) (hT : VFBounded T.carrier) :
    VFBounded (pullbackTarget D T π o).carrier :=
  vfBounded_of_pullback (fun t i => t (Fin.castAdd a i)) (fun t j => t (Fin.natAdd q j))
    (fun _ hp => ⟨hp.1, hp.2.1⟩) hD hT

theorem pullbackTarget_rvBounded {a : ℕ} {T : DefSet (rawMixedSpace (M := M) 1 a) S}
    {o : Fin r → Fin a} (hD : RVSupportDoublyBounded D.carrier)
    (hT : RVSupportDoublyBounded T.carrier) :
    RVSupportDoublyBounded (pullbackTarget D T π o).carrier :=
  rvBounded_of_pullback (Fin.castAdd a) (Fin.natAdd q) (fun _ hp => ⟨hp.1, hp.2.1⟩)
    (fun j => Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j) hD hT

theorem pullbackTarget_vfDoublyBounded {a : ℕ} {T : DefSet (rawMixedSpace (M := M) 1 a) S}
    {o : Fin r → Fin a} (hD : VFDoublyBounded D.carrier) (hT : VFDoublyBounded T.carrier) :
    VFDoublyBounded (pullbackTarget D T π o).carrier :=
  vfDoublyBounded_of_pullback (fun t i => t (Fin.castAdd a i)) (fun t j => t (Fin.natAdd q j))
    (fun _ hp => ⟨hp.1, hp.2.1⟩) hD hT

end Sets

/-! ### Maps whose graph fibres are products -/

section GraphProduct

variable {n a b c d : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n + 1) a) S}
  {B : DefSet (rawMixedSpace (M := M) (n + 1) b) S}
  {E : DefSet (rawMixedSpace (M := M) 1 c) S} {F : DefSet (rawMixedSpace (M := M) 1 d) S}

/-- The graph fibres of `f` over the labels `(u, v)` are products: the
identity on `K u v ⊆ VFⁿ` in the first `n` coordinates, times the graph fibre of
the unary map `h` over the labels `(σ u, τ v)` in the last coordinate. -/
structure IsGraphProduct (f : Map A B) (h : Map E F)
    (σ : (Fin a → RVInfinity M) → Fin c → RVInfinity M)
    (τ : (Fin b → RVInfinity M) → Fin d → RVInfinity M)
    (K : (Fin a → RVInfinity M) → (Fin b → RVInfinity M) → Set (Fin n → VF M)) : Prop where
  graph : ∀ u v x y, graphFibre f u v x y ↔ Fin.init x ∈ K u v ∧ Fin.init y = Fin.init x ∧
    graphFibre h (σ u) (τ v) (fun _ => x (Fin.last n)) (fun _ => y (Fin.last n))

variable {f : Map A B} {h : Map E F} {σ : (Fin a → RVInfinity M) → Fin c → RVInfinity M}
  {τ : (Fin b → RVInfinity M) → Fin d → RVInfinity M}
  {K : (Fin a → RVInfinity M) → (Fin b → RVInfinity M) → Set (Fin n → VF M)}

omit [M ⊨ Axioms.ACVF] in
theorem snoc_init_last (x : Fin (n + 1) → VF M) (y : Fin 1 → VF M) :
    (fun _ : Fin 1 => (Fin.snoc (Fin.init x) (y 0) : Fin (n + 1) → VF M) (Fin.last n)) = y :=
  FibreRestriction.fin_one_ext (by simp)

omit [M ⊨ Axioms.ACVF] in
theorem IsGraphProduct.source (hf : IsGraphProduct f h σ τ K) (u : Fin a → RVInfinity M)
    (v : Fin b → RVInfinity M) :
    graphFibreSource f u v = {x : Fin (n + 1) → VF M | Fin.init x ∈ K u v ∧
      (fun _ => x (Fin.last n)) ∈ graphFibreSource h (σ u) (τ v)} := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨hK, -, hh⟩ := (hf.graph u v x y).mp hy
    exact ⟨hK, _, hh⟩
  · rintro ⟨hK, y₁, hy₁⟩
    refine ⟨Fin.snoc (Fin.init x) (y₁ 0), (hf.graph u v x _).mpr ⟨hK, Fin.init_snoc _ _, ?_⟩⟩
    rw [snoc_init_last]
    exact hy₁

omit [M ⊨ Axioms.ACVF] in
theorem IsGraphProduct.range (hf : IsGraphProduct f h σ τ K) (u : Fin a → RVInfinity M)
    (v : Fin b → RVInfinity M) :
    graphFibreRange f u v = {y : Fin (n + 1) → VF M | Fin.init y ∈ K u v ∧
      (fun _ => y (Fin.last n)) ∈ graphFibreRange h (σ u) (τ v)} := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hK, hxy, hh⟩ := (hf.graph u v x y).mp hx
    exact ⟨hxy ▸ hK, _, hh⟩
  · rintro ⟨hK, x₁, hx₁⟩
    refine ⟨Fin.snoc (Fin.init y) (x₁ 0), (hf.graph u v _ y).mpr ⟨?_, ?_, ?_⟩⟩
    · rw [Fin.init_snoc]
      exact hK
    · rw [Fin.init_snoc]
    · rw [snoc_init_last]
      exact hx₁

theorem IsGraphProduct.map (hf : IsGraphProduct f h σ τ K) (u : Fin a → RVInfinity M)
    (v : Fin b → RVInfinity M) {x : Fin (n + 1) → VF M} (hx : x ∈ graphFibreSource f u v) :
    graphFibreMap f u v x = Fin.snoc (Fin.init x)
      (graphFibreMap h (σ u) (τ v) (fun _ => x (Fin.last n)) 0) := by
  obtain ⟨-, hxy, hh⟩ := (hf.graph u v x _).mp (graphFibreMap_graph f u v hx)
  have hx₁ : (fun _ => x (Fin.last n)) ∈ graphFibreSource h (σ u) (τ v) := ⟨_, hh⟩
  have he := graphFibre_functional h (σ u) (τ v) hh (graphFibreMap_graph h (σ u) (τ v) hx₁)
  calc graphFibreMap f u v x = Fin.snoc (Fin.init (graphFibreMap f u v x))
        (graphFibreMap f u v x (Fin.last n)) := (Fin.snoc_init_self _).symm
    _ = _ := by
      rw [hxy]
      exact congrArg _ (congrFun he 0)

/-- A map whose graph fibres are products of an invariant set with the graph
fibres of a proper covariant unary map is proper covariant: the radii combine
those of the set with those of the unary map. -/
theorem IsGraphProduct.properCovariant (hf : IsGraphProduct f h σ τ K) (hh : ProperCovariant h)
    (hbase : ∀ u v, graphFibreBase S (σ u) (τ v) ⊆ graphFibreBase S u v)
    (hK : ∀ u v, ∃ α : Fin n → Gamma M,
      NamedGammaTuple (graphFibreBase S u v) α ∧ AlphaInvariant α (K u v))
    (h₁ : VFBounded A.carrier) (h₂ : VFBounded (mixedMapRange f))
    (h₃ : RVSupportDoublyBounded A.carrier) (h₄ : RVSupportDoublyBounded (mixedMapRange f)) :
    ProperCovariant f := by
  refine ⟨h₁, h₂, h₃, h₄, fun u v => ?_⟩
  obtain ⟨αK, hαK, hInvK⟩ := hK u v
  obtain ⟨α, β, hα, hβ, hInvα, hInvβ, hcov⟩ := hh.radii (σ u) (τ v)
  refine ⟨snocRadius αK α, snocRadius αK β,
    namedGammaTuple_snocRadius hαK (fun i => (hα i).mono (hbase u v)),
    namedGammaTuple_snocRadius hαK (fun i => (hβ i).mono (hbase u v)), ?_, ?_, ?_⟩
  · rw [hf.source u v]
    intro x y hxy
    exact and_congr (hInvK _ _ (congruent_init_of_snocRadius hxy))
      (hInvα _ _ (congruent_last_of_snocRadius hxy))
  · rw [hf.range u v]
    intro x y hxy
    exact and_congr (hInvK _ _ (congruent_init_of_snocRadius hxy))
      (hInvβ _ _ (congruent_last_of_snocRadius hxy))
  · intro x hx y hy hxy
    have hx' := hx
    rw [hf.source u v] at hx'
    have hy' := hy
    rw [hf.source u v] at hy'
    rw [hf.map u v hx, hf.map u v hy]
    apply congruent_snocRadius
    · rw [Fin.init_snoc, Fin.init_snoc]
      exact congruent_init_of_snocRadius hxy
    · have hc := hcov _ hx'.2 _ hy'.2 (congruent_last_of_snocRadius hxy)
      intro i
      rw [Subsingleton.elim i 0]
      simp only [Fin.snoc_last]
      exact hc 0

/-- A map whose graph fibres are products with the graph fibres of a unary map
continuous on its graph fibres is continuous on its graph fibres. -/
theorem IsGraphProduct.continuous {G : Type} [LinearOrderedCommGroupWithZero G]
    [Valued (VF M) G] (hf : IsGraphProduct f h σ τ K) (hh : ContinuousOnGraphFibres (G := G) h) :
    ContinuousOnGraphFibres (G := G) f := by
  intro u v
  have hlast : Continuous (fun x : Fin (n + 1) → VF M => (fun _ : Fin 1 => x (Fin.last n))) :=
    continuous_pi fun _ => continuous_apply _
  have hmaps : Set.MapsTo (fun x : Fin (n + 1) → VF M => (fun _ : Fin 1 => x (Fin.last n)))
      (graphFibreSource f u v) (graphFibreSource h (σ u) (τ v)) := by
    intro x hx
    rw [hf.source u v] at hx
    exact hx.2
  have hg : ContinuousOn (fun x : Fin (n + 1) → VF M =>
      graphFibreMap h (σ u) (τ v) (fun _ => x (Fin.last n)) 0) (graphFibreSource f u v) :=
    (continuous_apply 0).comp_continuousOn ((hh (σ u) (τ v)).comp hlast.continuousOn hmaps)
  have hsnoc : ContinuousOn (fun x : Fin (n + 1) → VF M => (Fin.snoc (Fin.init x)
      (graphFibreMap h (σ u) (τ v) (fun _ => x (Fin.last n)) 0) : Fin (n + 1) → VF M))
      (graphFibreSource f u v) := by
    refine continuousOn_pi.mpr fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      exact hg
    · simp only [Fin.snoc_castSucc, Fin.init]
      exact (continuous_apply _).continuousOn
  exact hsnoc.congr fun x hx => hf.map u v hx

/-- The inverse of a graph product is the graph product with the inverse. -/
theorem IsGraphProduct.inverse (hf : IsGraphProduct f h σ τ K) (hbij : Function.Bijective f)
    (hhbij : Function.Bijective h) :
    IsGraphProduct (f.inverse hbij) (h.inverse hhbij) τ σ (fun v u => K u v) := by
  refine ⟨fun v u y x => ?_⟩
  rw [inverse_graphFibre_iff f hbij u v x y, hf.graph u v x y,
    inverse_graphFibre_iff h hhbij (σ u) (τ v)]
  constructor
  · rintro ⟨hK, hxy, hh⟩
    exact ⟨hxy ▸ hK, hxy.symm, hh⟩
  · rintro ⟨hK, hxy, hh⟩
    exact ⟨hxy ▸ hK, hxy.symm, hh⟩

end GraphProduct

/-! ### Definable maps given by reindexing codes -/

section Maps

variable {n q a : ℕ}

/-- The definable map of a reindexing of the real codes. -/
def reindexMap {a' b' c' d' : ℕ} (A : DefSet (rawMixedSpace (M := M) a' b') S)
    (g : Mixed M a' b' → Mixed M c' d') (ρ : Fin c' ⊕ Fin d' → Fin a' ⊕ Fin b')
    (hρ : ∀ p, mixedValues p ∘ ρ = mixedValues (g p)) :
    Map A (DefSet.univ (rawMixedSpace (M := M) c' d') S) :=
  Map.ofCodes A g (fun z => z ∘ ρ) (fun _ => Set.DefinableFun.proj LRV)
    (fun z => by
      have h := hρ ((rawMixedSpace (M := M) a' b').decode z)
      rw [mixedValues_decode] at h
      show z.val ∘ ρ ∈ _
      rw [h]
      exact mixedValues_mem_domain _)
    (fun z => by
      apply mixedValues_injective
      have h := hρ ((rawMixedSpace (M := M) a' b').decode z)
      rw [mixedValues_decode] at h
      exact (mixedValues_decode _).trans h)

/-- The definable map `(x, t) ↦ (x_{n+1}, t ∘ κ)`. -/
def lastLabelMap {r k : ℕ} (A : DefSet (rawMixedSpace (M := M) (n + 1) k) S)
    (κ : Fin r → Fin k) : Map A (DefSet.univ (rawMixedSpace (M := M) 1 r) S) :=
  reindexMap A (fun p => (((fun _ => p.1 (Fin.last n)), fun j => p.2 (κ j)) : Mixed M 1 r))
    (lastIndex κ) (lastIndex_mixedValues κ)

/-- `((x, t), (y, w)) ↦ ((x₁, …, xₙ, y), (t, w))`. -/
def combine (x : Mixed M (n + 1) q) (y : Mixed M 1 a) : Mixed M (n + 1) (q + a) :=
  (Fin.snoc (Fin.init x.1) (y.1 0), Fin.append x.2 y.2)

/-- The real codes of `combine`. -/
def combineIndex : Fin (n + 1) ⊕ Fin (q + a) → (Fin (n + 1) ⊕ Fin q) ⊕ (Fin 1 ⊕ Fin a) :=
  Sum.elim (Fin.snoc (α := fun _ => (Fin (n + 1) ⊕ Fin q) ⊕ (Fin 1 ⊕ Fin a))
      (fun j => .inl (.inl j.castSucc)) (.inr (.inl 0)))
    (Fin.append (fun i => .inl (.inr i)) (fun j => .inr (.inr j)))

omit [M ⊨ Axioms.ACVF] in
theorem combineIndex_mixedValues (x : Mixed M (n + 1) q) (y : Mixed M 1 a) :
    Sum.elim (mixedValues x) (mixedValues y) ∘ combineIndex = mixedValues (combine x y) := by
  funext i
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [combineIndex, combine, mixedValues, vfValues]
    · simp [combineIndex, combine, mixedValues, vfValues, Fin.init]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [combineIndex, combine, mixedValues, rvValues]
    · simp [combineIndex, combine, mixedValues, rvValues]

omit [M ⊨ Axioms.ACVF] in
theorem combineIndex_decode
    (z : ((rawMixedSpace (M := M) (n + 1) q).prod (rawMixedSpace (M := M) 1 a)).domain) :
    z.val ∘ combineIndex = mixedValues
      (combine (((rawMixedSpace (M := M) (n + 1) q).prod (rawMixedSpace (M := M) 1 a)).decode z).1
        (((rawMixedSpace (M := M) (n + 1) q).prod (rawMixedSpace (M := M) 1 a)).decode z).2) := by
  have hz : z.val = Sum.elim
      (mixedValues ((rawMixedSpace (M := M) (n + 1) q).decode ⟨z.val ∘ Sum.inl, z.property.1⟩))
      (mixedValues ((rawMixedSpace (M := M) 1 a).decode ⟨z.val ∘ Sum.inr, z.property.2⟩)) := by
    rw [mixedValues_decode, mixedValues_decode]
    funext i
    cases i <;> rfl
  rw [hz]
  exact combineIndex_mixedValues _ _

/-- The definable map `combine` on a definable set of pairs. -/
def combineMap (A : DefSet ((rawMixedSpace (M := M) (n + 1) q).prod (rawMixedSpace (M := M) 1 a)) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) (n + 1) (q + a)) S) :=
  Map.ofCodes A (fun xy => combine xy.1 xy.2) (fun z => z ∘ combineIndex)
    (fun _ => Set.DefinableFun.proj LRV)
    (fun z => by
      show z.val ∘ combineIndex ∈ _
      rw [combineIndex_decode]
      exact mixedValues_mem_domain _)
    (fun z => mixedValues_injective ((mixedValues_decode _).trans (combineIndex_decode z)))

end Maps

/-! ### Block-diagonal derivatives -/

section Derivative

variable {n : ℕ}

/-- The block-diagonal linear map `w ↦ (w₁, …, wₙ, L₁(w_{n+1}))`. -/
def blockLinear (L₁ : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M)) :
    (Fin (n + 1) → VF M) →ₗ[VF M] (Fin (n + 1) → VF M) where
  toFun w := Fin.snoc (Fin.init w) (L₁ (fun _ => w (Fin.last n)) 0)
  map_add' w w' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h : (fun _ : Fin 1 => w (Fin.last n) + w' (Fin.last n)) =
          (fun _ => w (Fin.last n)) + (fun _ => w' (Fin.last n)) := rfl
      simp only [Pi.add_apply, Fin.snoc_last]
      rw [h, map_add]
      rfl
    · simp [Fin.init]
  map_smul' c w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h : (fun _ : Fin 1 => c • w (Fin.last n)) = c • (fun _ => w (Fin.last n)) := rfl
      simp only [Pi.smul_apply, Fin.snoc_last, RingHom.id_apply]
      rw [h, map_smul]
      rfl
    · simp [Fin.init]

theorem blockLinear_apply (L₁ : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M)) (w : Fin (n + 1) → VF M) :
    blockLinear L₁ w = Fin.snoc (Fin.init w) (L₁ (fun _ => w (Fin.last n)) 0) := rfl

theorem blockLinear_det (L₁ : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M)) :
    (LinearMap.toMatrix' (blockLinear (n := n) L₁)).det = (LinearMap.toMatrix' L₁).det := by
  have hlow : (LinearMap.toMatrix' (blockLinear (n := n) L₁)).IsLowerTriangular := by
    intro i k hik
    have hik' : i < k := OrderDual.toDual_lt_toDual.mp hik
    have hi : i ≠ Fin.last n := by
      rintro rfl
      exact (Fin.le_last k).not_gt hik'
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    rw [LinearMap.toMatrix'_apply, blockLinear_apply, Fin.snoc_castSucc]
    exact Pi.single_eq_of_ne (ne_of_lt hik') _
  have hdiag : ∀ j : Fin n, LinearMap.toMatrix' (blockLinear (n := n) L₁) j.castSucc j.castSucc = 1 := by
    intro j
    rw [LinearMap.toMatrix'_apply, blockLinear_apply, Fin.snoc_castSucc]
    exact Pi.single_eq_same _ _
  have hlast : LinearMap.toMatrix' (blockLinear (n := n) L₁) (Fin.last n) (Fin.last n) =
      LinearMap.toMatrix' L₁ 0 0 := by
    rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, blockLinear_apply, Fin.snoc_last]
    have hx : (fun _ : Fin 1 => (Pi.single (Fin.last n) (1 : VF M) : Fin (n + 1) → VF M) (Fin.last n)) =
        Pi.single 0 1 := by
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [hx]
  rw [Matrix.det_of_isLowerTriangular _ hlow, Fin.prod_univ_castSucc, Matrix.det_fin_one]
  simp only [hdiag, Finset.prod_const_one, one_mul, hlast]

/-- The derivative of `x ↦ (x₁, …, xₙ, F₁(x_{n+1}))` is block diagonal. -/
theorem hasVFDerivativeAt_block {F₁ : (Fin 1 → VF M) → Fin 1 → VF M}
    {L₁ : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M)} {a : Fin (n + 1) → VF M}
    (h : HasVFDerivativeAt F₁ (fun _ => a (Fin.last n)) L₁) :
    HasVFDerivativeAt (fun x : Fin (n + 1) → VF M =>
      (Fin.snoc (Fin.init x) (F₁ (fun _ => x (Fin.last n)) 0) : Fin (n + 1) → VF M)) a
      (blockLinear L₁) := by
  apply hasVFDerivativeAt_of_components
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro ε
    obtain ⟨δ, hδ⟩ := h.component 0 ε
    refine ⟨δ, fun b hb hbδ => ?_⟩
    have e1 : (fun _ : Fin 1 => (a + b) (Fin.last n)) =
        (fun _ => a (Fin.last n)) + (fun _ => b (Fin.last n)) := rfl
    simp only [blockLinear_apply, Fin.snoc_last]
    rw [e1]
    by_cases hb0 : b (Fin.last n) = 0
    · have hz : (fun _ : Fin 1 => b (Fin.last n)) = 0 := funext fun _ => hb0
      simp only [hz, add_zero, map_zero, Pi.zero_apply, sub_self]
      exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (vfTupleValue_ne_zero hb))
    · have hb1 : (fun _ : Fin 1 => b (Fin.last n)) ≠ 0 := fun h => hb0 (congrFun h 0)
      have hcomp : vfTupleValue b ≤ vfTupleValue (fun _ : Fin 1 => b (Fin.last n)) := by
        obtain ⟨k, hk⟩ := vfTupleValue_eq_component (fun _ : Fin 1 => b (Fin.last n)) Nat.zero_lt_one
        rw [hk]
        exact vfTupleValue_le_component b (Fin.last n)
      exact (mul_le_mul' le_rfl hcomp).trans_lt (hδ _ hb1 (hbδ.trans_le hcomp))
  · intro ε
    refine ⟨1, fun b hb _ => ?_⟩
    simp only [blockLinear_apply, Fin.snoc_castSucc, Fin.init, Pi.add_apply]
    rw [show a j.castSucc + b j.castSucc - a j.castSucc - b j.castSucc = 0 by abel, map_zero]
    exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (vfTupleValue_ne_zero hb))

end Derivative

/-! ### The pulled-back stage -/

section Stage

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {n q r : ℕ} {E : DefSet (rawMixedSpace (M := M) 1 r) S}

/-- The point `(x_{n+1}, t ∘ π)` of `E` under a point `(x, t)` of `D ×_π E`. -/
def toFactor {D : DefSet (rawMixedSpace (M := M) n q) S} {π : Fin r → Fin q}
    (p : pullbackProd D E π) : E :=
  ⟨((fun _ => p.val.1 (Fin.last n)), p.val.2 ∘ π), p.property.2⟩

/-- The definable map `D ×_π E → E`, `(x, t) ↦ (x_{n+1}, t ∘ π)`. -/
def factorMap (D : DefSet (rawMixedSpace (M := M) n q) S) (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (π : Fin r → Fin q) : Map (pullbackProd D E π) E :=
  (lastLabelMap (pullbackProd D E π) π).corestrict (fun p => p.property.2)

theorem factorMap_apply {D : DefSet (rawMixedSpace (M := M) n q) S} {π : Fin r → Fin q}
    (p : pullbackProd D E π) : factorMap D E π p = toFactor p := rfl

variable (D : DefSet (rawMixedSpace (M := M) n q) S) (π : Fin r → Fin q)
variable (H : StandardContractionStage (G := G) E)

/-- The value `((x₁, …, xₙ, y), (t, w))` of the pulled-back lift at `(x, t)`,
where `H(x_{n+1}, t ∘ π) = (y, w)`. -/
def pullbackValue (p : pullbackProd D E π) : Mixed M (n + 1) (q + H.arity) :=
  combine p.val (H.lift (toFactor p)).val

theorem pullbackValue_eq (p : pullbackProd D E π) :
    pullbackValue D π H p = (Fin.snoc (Fin.init p.val.1) ((H.lift (toFactor p)).val.1 0),
      Fin.append p.val.2 (H.lift (toFactor p)).val.2) := rfl

theorem pullbackValue_mem (p : pullbackProd D E π) :
    pullbackValue D π H p ∈ (pullbackTarget D H.target π H.oldLabels).carrier := by
  rw [pullbackValue_eq]
  refine ⟨?_, ?_, fun i => ?_⟩
  · simp only [Fin.init_snoc, Fin.append_left]
    exact p.property.1
  · simp only [Fin.append_right]
    rw [snoc_init_last]
    exact (H.lift (toFactor p)).property
  · simp only [Fin.append_left, Fin.append_right]
    exact H.retained (toFactor p) i

/-- The pulled-back lift `D ×_π E → pullbackTarget D H.target π H.oldLabels`. -/
def pullbackLift : Map (pullbackProd D E π) (pullbackTarget D H.target π H.oldLabels) :=
  ((combineMap _).comp ((Map.id _).pair (H.lift.comp (factorMap D E π)))).corestrict
    (fun p => pullbackValue_mem D π H p)

theorem pullbackLift_val (p : pullbackProd D E π) :
    (pullbackLift D π H p).val = pullbackValue D π H p := rfl

/-- The value of the pulled-back lift. -/
theorem pullbackLift_apply (p : pullbackProd D E π) :
    (pullbackLift D π H p).val = (Fin.snoc (Fin.init p.val.1)
      ((H.lift ⟨((fun _ => p.val.1 (Fin.last n)), p.val.2 ∘ π), p.property.2⟩).val.1 0),
      Fin.append p.val.2 (H.lift ⟨((fun _ => p.val.1 (Fin.last n)), p.val.2 ∘ π), p.property.2⟩).val.2) :=
  rfl

theorem pullbackLift_injective : Function.Injective (pullbackLift D π H) := by
  intro p p' hpp
  have hv : pullbackValue D π H p = pullbackValue D π H p' := congrArg Subtype.val hpp
  rw [pullbackValue_eq, pullbackValue_eq] at hv
  have h1 := congrArg (fun z : Mixed M (n + 1) (q + H.arity) => Fin.init z.1) hv
  have h2 := congrArg (fun z : Mixed M (n + 1) (q + H.arity) => z.1 (Fin.last n)) hv
  have h3 := congrArg (fun z : Mixed M (n + 1) (q + H.arity) =>
    fun i => z.2 (Fin.castAdd H.arity i)) hv
  have h4 := congrArg (fun z : Mixed M (n + 1) (q + H.arity) =>
    fun j => z.2 (Fin.natAdd q j)) hv
  simp only [Fin.init_snoc, Fin.snoc_last, Fin.append_left, Fin.append_right] at h1 h2 h3 h4
  have hH : H.lift (toFactor p) = H.lift (toFactor p') :=
    Subtype.ext (Prod.ext (FibreRestriction.fin_one_ext h2) h4)
  have hF := congrArg (fun e : E => e.val.1 0) (H.home.bijective.1 hH)
  apply Subtype.ext
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hF
    · exact congrFun h1 j
  · exact h3

theorem pullbackLift_surjective : Function.Surjective (pullbackLift D π H) := by
  intro p'
  obtain ⟨hD', hT', hlab⟩ := p'.property
  obtain ⟨e, he⟩ := H.home.bijective.2 ⟨_, hT'⟩
  have heval : (H.lift e).val = (((fun _ => p'.val.1 (Fin.last n)),
      fun j => p'.val.2 (Fin.natAdd q j)) : Mixed M 1 H.arity) := congrArg Subtype.val he
  have he2 : ∀ j, e.val.2 j = p'.val.2 (Fin.castAdd H.arity (π j)) := by
    intro j
    rw [← H.retained e j, heval]
    exact hlab j
  have hmemE : (((fun _ => (Fin.snoc (Fin.init p'.val.1) (e.val.1 0) : Fin (n + 1) → VF M)
      (Fin.last n)), fun j => p'.val.2 (Fin.castAdd H.arity (π j))) : Mixed M 1 r) = e.val := by
    rw [snoc_init_last]
    exact Prod.ext rfl (funext fun j => (he2 j).symm)
  have hp : ((Fin.snoc (Fin.init p'.val.1) (e.val.1 0), fun i => p'.val.2 (Fin.castAdd H.arity i)) :
      Mixed M (n + 1) q) ∈ (pullbackProd D E π).carrier := by
    refine ⟨?_, ?_⟩
    · show ((Fin.init (Fin.snoc (Fin.init p'.val.1) (e.val.1 0) : Fin (n + 1) → VF M),
        fun i => p'.val.2 (Fin.castAdd H.arity i)) : Mixed M n q) ∈ D.carrier
      rw [Fin.init_snoc]
      exact hD'
    · show (((fun _ => (Fin.snoc (Fin.init p'.val.1) (e.val.1 0) : Fin (n + 1) → VF M)
        (Fin.last n)), fun j => p'.val.2 (Fin.castAdd H.arity (π j))) : Mixed M 1 r) ∈ E.carrier
      rw [hmemE]
      exact e.property
  refine ⟨⟨_, hp⟩, Subtype.ext ?_⟩
  have hfac : toFactor (⟨_, hp⟩ : pullbackProd D E π) = e := Subtype.ext hmemE
  rw [pullbackLift_val, pullbackValue_eq, hfac, heval]
  apply Prod.ext
  · show (Fin.snoc (Fin.init (Fin.snoc (Fin.init p'.val.1) (e.val.1 0) : Fin (n + 1) → VF M))
      (p'.val.1 (Fin.last n)) : Fin (n + 1) → VF M) = p'.val.1
    rw [Fin.init_snoc]
    exact Fin.snoc_init_self _
  · exact Fin.append_castAdd_natAdd

theorem pullbackLift_bijective : Function.Bijective (pullbackLift D π H) :=
  ⟨pullbackLift_injective D π H, pullbackLift_surjective D π H⟩

/-- The graph fibres of the pulled-back lift: over the labels `(u, v)`, the
identity on `D_u` (when `v` extends `u`) times the graph fibre of `H` over
`(u ∘ π, (v_{q+j})_j)`. -/
theorem pullbackLift_graphProduct :
    IsGraphProduct (pullbackLift D π H) H.lift (fun u j => u (π j))
      (fun v j => v (Fin.natAdd q j))
      (fun u v => {z | ((z, u) : Mixed M n q) ∈ D.carrier ∧
        (fun i => v (Fin.castAdd H.arity i)) = u}) := by
  refine ⟨fun u v x y => ?_⟩
  constructor
  · rintro ⟨p, hpx, hfp⟩
    have hx : p.val.1 = x := congrArg Prod.fst hpx
    have hu : p.val.2 = u := congrArg Prod.snd hpx
    subst hx hu
    rw [pullbackLift_val, pullbackValue_eq] at hfp
    have hy : Fin.snoc (Fin.init p.val.1) ((H.lift (toFactor p)).val.1 0) = y :=
      congrArg Prod.fst hfp
    have hv : Fin.append p.val.2 (H.lift (toFactor p)).val.2 = v := congrArg Prod.snd hfp
    subst hy hv
    refine ⟨⟨p.property.1, ?_⟩, Fin.init_snoc _ _, toFactor p, rfl, ?_⟩
    · funext i
      exact Fin.append_left _ _ _
    · apply Prod.ext
      · exact (snoc_init_last p.val.1 _).symm
      · funext j
        exact (Fin.append_right _ _ _).symm
  · rintro ⟨⟨hDx, hvu⟩, hyx, e, he, hfe⟩
    have heE : (((fun _ => x (Fin.last n)), fun j => u (π j)) : Mixed M 1 r) ∈ E.carrier :=
      he ▸ e.property
    have hp : ((x, u) : Mixed M (n + 1) q) ∈ (pullbackProd D E π).carrier := ⟨hDx, heE⟩
    refine ⟨⟨(x, u), hp⟩, rfl, ?_⟩
    have hfac : toFactor (⟨(x, u), hp⟩ : pullbackProd D E π) = e := Subtype.ext he.symm
    rw [pullbackLift_val, pullbackValue_eq, hfac, hfe]
    apply Prod.ext
    · show (Fin.snoc (Fin.init x) (y (Fin.last n)) : Fin (n + 1) → VF M) = y
      rw [← hyx]
      exact Fin.snoc_init_self y
    · show Fin.append u (fun j => v (Fin.natAdd q j)) = v
      rw [← hvu]
      exact Fin.append_castAdd_natAdd

/-- The pulled-back lift is a proper covariant homeomorphism. Its graph fibres
are `D_u × (graph fibre of H)`, so its radii combine the named radii of `D`
with those of `H`, and similarly for the inverse. -/
theorem pullbackLift_home (hD : ProperInvariant S D.carrier) :
    ProperCovariantHomeomorphism (G := G) (pullbackLift D π H) := by
  have hbij := pullbackLift_bijective D π H
  have hgp := pullbackLift_graphProduct D π H
  have hgpi := hgp.inverse hbij H.home.bijective
  have hAvf : VFBounded (pullbackProd D E π).carrier :=
    pullbackProd_vfBounded hD.vfBounded H.home.covariant.sourceVFBounded
  have hArv : RVSupportDoublyBounded (pullbackProd D E π).carrier :=
    pullbackProd_rvBounded hD.rvBounded
  have hTvf : VFBounded (pullbackTarget D H.target π H.oldLabels).carrier :=
    pullbackTarget_vfBounded hD.vfBounded H.proper.vfBounded
  have hTrv : RVSupportDoublyBounded (pullbackTarget D H.target π H.oldLabels).carrier :=
    pullbackTarget_rvBounded hD.rvBounded H.proper.rvBounded
  have hrT : mixedMapRange (pullbackLift D π H) ⊆ (pullbackTarget D H.target π H.oldLabels).carrier := by
    rintro _ ⟨p, rfl⟩
    exact (pullbackLift D π H p).property
  have hrA : mixedMapRange ((pullbackLift D π H).inverse hbij) ⊆ (pullbackProd D E π).carrier := by
    rintro _ ⟨p, rfl⟩
    exact ((pullbackLift D π H).inverse hbij p).property
  refine ⟨hbij, ?_, hgp.continuous H.home.continuous, ?_,
    hgpi.continuous H.home.inverseContinuous⟩
  · refine hgp.properCovariant H.home.covariant
      (fun u v => graphFibreBase_comp_subset u v π (Fin.natAdd q)) (fun u v => ?_)
      hAvf (hTvf.mono hrT) hArv (hTrv.mono hrT)
    obtain ⟨α, hα, hInv⟩ := hD.radii u
    exact ⟨α, fun i => (hα i).mono Set.subset_union_left,
      fun a b hab => and_congr (hInv a b hab) Iff.rfl⟩
  · refine hgpi.properCovariant H.home.inverseCovariant
      (fun v u => graphFibreBase_comp_subset v u (Fin.natAdd q) π) (fun v u => ?_)
      hTvf (hAvf.mono hrA) hTrv (hArv.mono hrA)
    obtain ⟨α, hα, hInv⟩ := hD.radii u
    exact ⟨α, fun i => (hα i).mono (Set.union_subset_union_left _ Set.subset_union_left),
      fun a b hab => and_congr (hInv a b hab) Iff.rfl⟩

theorem pullbackLift_relative (p : pullbackProd D E π) (i : Fin n) :
    (pullbackLift D π H p).val.1 i.castSucc = p.val.1 i.castSucc := by
  rw [pullbackLift_val, pullbackValue_eq]
  exact Fin.snoc_castSucc (α := fun _ => VF M) _ _ _

theorem pullbackLift_retained (p : pullbackProd D E π) (i : Fin q) :
    (pullbackLift D π H p).val.2 (Fin.castAdd H.arity i) = p.val.2 i := by
  rw [pullbackLift_val, pullbackValue_eq]
  exact Fin.append_left _ _ _

theorem pullbackTarget_bundle :
    (pullbackTarget D H.target π H.oldLabels).carrier =
      (rvCoordinateBundle (vfDropLast (pullbackTarget D H.target π H.oldLabels)).image
        (Fin.natAdd q H.leading)).carrier := by
  ext p
  change p ∈ (pullbackTarget D H.target π H.oldLabels).carrier ↔
    ((Fin.init p.1, p.2) : Mixed M n (q + H.arity)) ∈
      (vfDropLast (pullbackTarget D H.target π H.oldLabels)).image.carrier ∧
      rv M (p.1 (Fin.last n)) = p.2 (Fin.natAdd q H.leading)
  constructor
  · intro hp
    exact ⟨⟨⟨p, hp⟩, rfl⟩, ((H.recover_target _).mp hp.2.1).2⟩
  · rintro ⟨⟨a, ha⟩, hrv⟩
    have h1 : Fin.init a.val.1 = Fin.init p.1 := by
      have h := congrArg Prod.fst ha
      exact h
    have h2 : a.val.2 = p.2 := by
      have h := congrArg Prod.snd ha
      exact h
    obtain ⟨haD, haT, hal⟩ := a.property
    refine ⟨?_, (H.recover_target _).mpr ⟨?_, hrv⟩, fun i => ?_⟩
    · rw [← h1, ← h2]
      exact haD
    · have hc := ((H.recover_target _).mp haT).1
      rw [h2] at hc
      have hz : (Fin.init (fun _ : Fin 1 => p.1 (Fin.last n)) : Fin 0 → VF M) =
          Fin.init (fun _ : Fin 1 => a.val.1 (Fin.last n)) := Subsingleton.elim _ _
      rw [hz]
      exact hc
    · rw [← h2]
      exact hal i

theorem pullbackProd_dim_lt (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) {X : DefSet (rawMixedSpace (M := M) 1 r) S}
    (hX : vfDim (rawRVSpace (M := M) 1) X < 1) :
    vfDim (rawRVSpace (M := M) 1) (pullbackProd D X π) < n + 1 := by
  apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) (Nat.zero_lt_succ n)
  intro p hInd
  have hLast : AlgebraicIndependent (vfParameterField S) (fun _ : Fin 1 => p.val.1 (Fin.last n)) :=
    hInd.comp (fun _ => Fin.last n) (fun a b _ => Subsingleton.elim a b)
  exact not_mem_small_set_of_independent hc X hX ((fun _ => p.val.1 (Fin.last n)), p.val.2 ∘ π)
    hLast p.property.2

theorem pullbackLift_unitDerivative (hD : ProperInvariant S D.carrier) (p : pullbackProd D E π)
    (hp : p.val ∉ (pullbackProd D H.exceptional π).carrier) :
    HasMixedUnitDerivativeAt (pullbackLift D π H) p := by
  have hp1 : (toFactor p).val ∉ H.exceptional.carrier := fun h => hp ⟨p.property.1, h⟩
  obtain ⟨L₁, ⟨F₁, ⟨ρ₁, hρ₁⟩, hF₁⟩, hdet⟩ := H.unitDerivative (toFactor p) hp1
  obtain ⟨αD, -, hInvD⟩ := hD.radii p.val.2
  obtain ⟨γ, hγ⟩ := Finite.exists_le αD
  refine ⟨blockLinear L₁, ⟨fun x => Fin.snoc (Fin.init x) (F₁ (fun _ => x (Fin.last n)) 0),
    ⟨max ρ₁ γ, fun x hx => ?_⟩, hasVFDerivativeAt_block hF₁⟩, by rw [blockLinear_det, hdet]⟩
  have hx₁ : (fun _ : Fin 1 => x (Fin.last n)) ∈ vfBall (toFactor p).val.1 ρ₁ := by
    intro i
    exact (show ρ₁.val ≤ (max ρ₁ γ).val from le_max_left _ _).trans_lt (hx (Fin.last n))
  obtain ⟨hxE, hval⟩ := hρ₁ _ hx₁
  have hxD : ((Fin.init x, p.val.2) : Mixed M n q) ∈ D.carrier := by
    have hc : Congruent αD (Fin.init x) (Fin.init p.val.1) := fun j =>
      (show (αD j).val ≤ (max ρ₁ γ).val from (hγ j).trans (le_max_right _ _)).trans_lt
        (hx j.castSucc)
    exact (hInvD _ _ hc).mpr p.property.1
  refine ⟨⟨hxD, hxE⟩, ?_⟩
  have hfac : toFactor (⟨(x, p.val.2), ⟨hxD, hxE⟩⟩ : pullbackProd D E π) =
      ⟨((fun _ => x (Fin.last n)), (toFactor p).val.2), hxE⟩ := rfl
  rw [pullbackLift_val, pullbackValue_eq, hfac, hval]
  rfl

/-- The pullback of a unary standard contraction stage `H` of `E` to the fibre
product `D ×_π E`. It contracts the last VF coordinate by `H`, keeps the first
`n` VF coordinates and all old labels, and appends the labels of `H`. -/
def pullbackStage (hD : ProperInvariant S D.carrier) (hDb : VFDoublyBounded D.carrier)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : StandardContractionStage (G := G) (pullbackProd D E π) where
  arity := q + H.arity
  target := pullbackTarget D H.target π H.oldLabels
  lift := pullbackLift D π H
  home := pullbackLift_home D π H hD
  proper := pullbackTarget_properInvariant hD H.proper
  doublyBounded := pullbackTarget_vfDoublyBounded hDb H.doublyBounded
  relative := pullbackLift_relative D π H
  oldLabels := Fin.castAdd H.arity
  oldLabels_injective := Fin.castAdd_injective q H.arity
  retained := pullbackLift_retained D π H
  leading := Fin.natAdd q H.leading
  bundle := pullbackTarget_bundle D π H
  exceptional := pullbackProd D H.exceptional π
  exceptional_subset := pullbackProd_mono H.exceptional_subset
  exceptional_dim := pullbackProd_dim_lt D π hc hs hsmall H.exceptional_dim
  unitDerivative := pullbackLift_unitDerivative D π H hD

variable (hD : ProperInvariant S D.carrier) (hDb : VFDoublyBounded D.carrier)
  (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
  (hsmall : Cardinal.mk S < κ)

theorem pullbackStage_arity : (pullbackStage D π H hD hDb hc hs hsmall).arity = q + H.arity := rfl

theorem pullbackStage_target :
    (pullbackStage D π H hD hDb hc hs hsmall).target = pullbackTarget D H.target π H.oldLabels := rfl

theorem pullbackStage_oldLabels :
    (pullbackStage D π H hD hDb hc hs hsmall).oldLabels = Fin.castAdd H.arity := rfl

theorem pullbackStage_leading :
    (pullbackStage D π H hD hDb hc hs hsmall).leading = Fin.natAdd q H.leading := rfl

theorem pullbackStage_exceptional :
    (pullbackStage D π H hD hDb hc hs hsmall).exceptional = pullbackProd D H.exceptional π := rfl

/-- The value of the lift of the pulled-back stage at `(x, t)`: the first `n`
coordinates and the labels `t` are kept, and `H(x_{n+1}, t ∘ π) = (y, w)`
supplies the last coordinate `y` and the new labels `w`. -/
theorem pullbackStage_lift_apply (p : pullbackProd D E π) :
    ((pullbackStage D π H hD hDb hc hs hsmall).lift p).val = (Fin.snoc (Fin.init p.val.1)
      ((H.lift ⟨((fun _ => p.val.1 (Fin.last n)), p.val.2 ∘ π), p.property.2⟩).val.1 0),
      Fin.append p.val.2 (H.lift ⟨((fun _ => p.val.1 (Fin.last n)), p.val.2 ∘ π), p.property.2⟩).val.2) :=
  rfl

/-- The contracted set of the pulled-back target. -/
theorem mem_pullbackTarget_contracted (x : Fin n → VF M) (w' : Fin (q + H.arity) → RVInfinity M) :
    ((x, w') : Mixed M n (q + H.arity)) ∈
        (vfDropLast (pullbackTarget D H.target π H.oldLabels)).image.carrier ↔
      ((x, fun i => w' (Fin.castAdd H.arity i)) : Mixed M n q) ∈ D.carrier ∧
      ((Fin.elim0, fun j => w' (Fin.natAdd q j)) : Mixed M 0 H.arity) ∈ H.contracted.carrier ∧
      ∀ i, w' (Fin.natAdd q (H.oldLabels i)) = w' (Fin.castAdd H.arity (π i)) := by
  constructor
  · rintro ⟨a, ha⟩
    have h1 : Fin.init a.val.1 = x := by
      have h := congrArg Prod.fst ha
      exact h
    have h2 : a.val.2 = w' := by
      have h := congrArg Prod.snd ha
      exact h
    obtain ⟨haD, haT, hal⟩ := a.property
    refine ⟨?_, ⟨⟨_, haT⟩, ?_⟩, fun i => ?_⟩
    · rw [← h1, ← h2]
      exact haD
    · show ((Fin.init (fun _ : Fin 1 => a.val.1 (Fin.last n)), fun j => a.val.2 (Fin.natAdd q j)) :
        Mixed M 0 H.arity) = (Fin.elim0, fun j => w' (Fin.natAdd q j))
      rw [h2]
      exact Prod.ext (Subsingleton.elim _ _) rfl
    · rw [← h2]
      exact hal i
  · rintro ⟨hD', ⟨b, hb⟩, hlab⟩
    have hb2 : b.val.2 = fun j => w' (Fin.natAdd q j) := by
      have h := congrArg Prod.snd hb
      exact h
    have hT : (((fun _ => (Fin.snoc x (b.val.1 0) : Fin (n + 1) → VF M) (Fin.last n)),
        fun j => w' (Fin.natAdd q j)) : Mixed M 1 H.arity) ∈ H.target.carrier := by
      have he : (((fun _ => (Fin.snoc x (b.val.1 0) : Fin (n + 1) → VF M) (Fin.last n)),
          fun j => w' (Fin.natAdd q j)) : Mixed M 1 H.arity) = b.val :=
        Prod.ext (FibreRestriction.fin_one_ext (by simp)) hb2.symm
      rw [he]
      exact b.property
    refine ⟨⟨(Fin.snoc x (b.val.1 0), w'), ?_, hT, hlab⟩, ?_⟩
    · show ((Fin.init (Fin.snoc x (b.val.1 0) : Fin (n + 1) → VF M),
        fun i => w' (Fin.castAdd H.arity i)) : Mixed M n q) ∈ D.carrier
      rw [Fin.init_snoc]
      exact hD'
    · show ((Fin.init (Fin.snoc x (b.val.1 0) : Fin (n + 1) → VF M), w') :
        Mixed M n (q + H.arity)) = (x, w')
      rw [Fin.init_snoc]

/-- The contracted set of the pulled-back stage: `(x, t, w)` lies in it exactly
when `(x, t) ∈ D`, `w` lies in the contracted set of `H`, and `w ∘ o_H = t ∘ π`. -/
theorem mem_pullbackStage_contracted (x : Fin n → VF M) (w' : Fin (q + H.arity) → RVInfinity M) :
    ((x, w') : Mixed M n (q + H.arity)) ∈
        (pullbackStage D π H hD hDb hc hs hsmall).contracted.carrier ↔
      ((x, fun i => w' (Fin.castAdd H.arity i)) : Mixed M n q) ∈ D.carrier ∧
      ((Fin.elim0, fun j => w' (Fin.natAdd q j)) : Mixed M 0 H.arity) ∈ H.contracted.carrier ∧
      ∀ i, w' (Fin.natAdd q (H.oldLabels i)) = w' (Fin.castAdd H.arity (π i)) :=
  mem_pullbackTarget_contracted D π H x w'

end Stage

/-! ### No VF coordinates in the first factor -/

section Zero

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {q r : ℕ} {E : DefSet (rawMixedSpace (M := M) 1 r) S}

/-- A set without VF coordinates is VF-doubly bounded. -/
theorem vfDoublyBounded_zero (D : Set (Mixed M 0 q)) : VFDoublyBounded D :=
  ⟨1, fun _ _ i => i.elim0⟩

/-- A definable set without VF coordinates with bounded RV support is proper
invariant (with the empty radius tuple). -/
theorem properInvariant_zero {D : DefSet (rawMixedSpace (M := M) 0 q) S}
    (hrv : RVSupportDoublyBounded D.carrier) : ProperInvariant S D.carrier :=
  ⟨D.definable, ⟨1, fun _ _ i => i.elim0⟩, hrv, fun _ => ⟨Fin.elim0, fun i => i.elim0,
    fun a b _ => by rw [Subsingleton.elim a b]⟩⟩

theorem mem_pullbackProd_zero {D : DefSet (rawMixedSpace (M := M) 0 q) S} {π : Fin r → Fin q}
    (p : Mixed M 1 q) :
    p ∈ (pullbackProd D E π).carrier ↔
      ((Fin.elim0, p.2) : Mixed M 0 q) ∈ D.carrier ∧ ((p.1, p.2 ∘ π) : Mixed M 1 r) ∈ E.carrier := by
  have h1 : (Fin.init p.1 : Fin 0 → VF M) = Fin.elim0 := Subsingleton.elim _ _
  have h2 : (fun _ : Fin 1 => p.1 (Fin.last 0)) = p.1 := FibreRestriction.fin_one_ext rfl
  rw [mem_pullbackProd, h1, h2]

/-- The pulled-back stage when the first factor `D ⊆ RV^q` has no VF
coordinates. It only needs bounded RV support of `D`. -/
def pullbackStageZero (D : DefSet (rawMixedSpace (M := M) 0 q) S) (π : Fin r → Fin q)
    (H : StandardContractionStage (G := G) E) (hD : RVSupportDoublyBounded D.carrier)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : StandardContractionStage (G := G) (pullbackProd D E π) :=
  pullbackStage D π H (properInvariant_zero hD) (vfDoublyBounded_zero D.carrier) hc hs hsmall

/-- The value of the lift of the pulled-back stage without VF coordinates in the
first factor: `(x, t) ↦ (y, (t, w))` where `H(x, t ∘ π) = (y, w)`. -/
theorem pullbackStageZero_lift_apply (D : DefSet (rawMixedSpace (M := M) 0 q) S)
    (π : Fin r → Fin q) (H : StandardContractionStage (G := G) E)
    (hD : RVSupportDoublyBounded D.carrier) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (p : pullbackProd D E π) :
    ((pullbackStageZero D π H hD hc hs hsmall).lift p).val =
      ((H.lift ⟨(p.val.1, p.val.2 ∘ π), ((mem_pullbackProd_zero p.val).mp p.property).2⟩).val.1,
        Fin.append p.val.2
          (H.lift ⟨(p.val.1, p.val.2 ∘ π), ((mem_pullbackProd_zero p.val).mp p.property).2⟩).val.2) := by
  have h2 : (fun _ : Fin 1 => p.val.1 (Fin.last 0)) = p.val.1 := FibreRestriction.fin_one_ext rfl
  have hf : (⟨((fun _ => p.val.1 (Fin.last 0)), p.val.2 ∘ π), p.property.2⟩ : E) =
      ⟨(p.val.1, p.val.2 ∘ π), ((mem_pullbackProd_zero p.val).mp p.property).2⟩ :=
    Subtype.ext (Prod.ext h2 rfl)
  change (Fin.snoc (Fin.init p.val.1)
      ((H.lift ⟨((fun _ => p.val.1 (Fin.last 0)), p.val.2 ∘ π), p.property.2⟩).val.1 0),
      Fin.append p.val.2 (H.lift ⟨((fun _ => p.val.1 (Fin.last 0)), p.val.2 ∘ π),
        p.property.2⟩).val.2) = _
  rw [hf]
  refine Prod.ext (FibreRestriction.fin_one_ext ?_) rfl
  show (Fin.snoc (Fin.init p.val.1) ((H.lift ⟨(p.val.1, p.val.2 ∘ π),
    ((mem_pullbackProd_zero p.val).mp p.property).2⟩).val.1 0) : Fin (0 + 1) → VF M) (Fin.last 0) = _
  exact Fin.snoc_last (α := fun _ => VF M) _ _

end Zero

end DiamondIntegral.Section7.PullbackStages
