import «section 7».ProductKinds
import «section 7».Corollary715Fibres

/-! Lemmas 7.22 and 7.23 for `n = 2`.

**Lemma 7.22** (`lemma_7_22`). For the object `A*` of Lemma 7.22 (the
normalized image of the prepared object, with the RV point of the Lemma 7.20
contraction grafted), any two standard contractions in the orders `21` and `12`
have `μIsp^db`-related classes. The product piece is `ProductKinds.prodPiece_orders`;
the balanced piece is the hypothesis `hBal` until the balanced case of
Lemma 7.21 is assembled; the pieces combine by
`PieceCombination.ispRel_orders_of_pieces`.

**Lemma 7.23, `n = 2`** (`lemma_7_23_two`). For an object `A` of `μVF^◇[2]`,
standard contractions in the two orders have `μIsp^db`-related classes. The
chain is
* `A → A'`, the graft of the prepared labels: a morphism fixing every VF
  coordinate, so Corollary 7.15 applies in both orders;
* `A'` and its normalized image `Y = D(A')`, `D` the normalization of the
  Lemma 7.20 contraction: contractions of `Y` pull back to contractions of `A'`
  with normalization `D` and the same class (`NormalizationComparison`);
* `Y → A*`, the graft of the RV point: Corollary 7.15 in both orders;
* Lemma 7.22 on `A*`.

This replaces the single morphism `A → A*` of the printed proof: the cells of
Lemma 7.20 live in the normalized coordinates of its standard contraction
(GAP-REPAIRS 13), so `A*` is built on the normalized image, and the
normalization is handled by the normalization comparison. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma723Two
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.GraftObjects DiamondIntegral.Section7.LabelPieces
open DiamondIntegral.Section7.Lemma722Objects DiamondIntegral.Section7.Lemma722Cells
open DiamondIntegral.Section7.ProductKinds DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.Corollary715Fibres
open DiamondIntegral.Section7.NormalizationComparison DiamondIntegral.Section7.TwoCellInput
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.ContractionChoice

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-- The balanced piece of `A*`. -/
abbrev balPiece (A' : VFObject (M := M) (T : Set M) 2)
    (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z) {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F) : VFObject (M := M) (T : Set M) 2 :=
  pieceObject (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) (complLabels (prodLabels Dt (2 + A'.labels)))

/-- The balanced case of Lemma 7.21 on `A*`, as a statement. -/
def BalancedOrders : Prop :=
  ∀ (A' : VFObject (M := M) (T : Set M) 2) (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z)
    {e : Equiv.Perm (Fin 2)} (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F),
    OrdersRelated (G := G) h00 hc hκ hs hv hsmall hΓ (balPiece h00 hc hκ hs hv hsmall hΓ A' hω F Dt)

include V hV hVT hTV hnt in
/-- **Lemma 7.22 (`subset:partitioned:2:unit:contracted`), on `A*`.** -/
theorem lemma_7_22 (h714 : Lemma714 M G) (A' : VFObject (M := M) (T : Set M) 2)
    (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z) {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F)
    (hBal : OrdersRelated (G := G) h00 hc hκ hs hv hsmall hΓ (balPiece h00 hc hκ hs hv hsmall hΓ A' hω F Dt))
    (K₁ : NormalizedMeasuredContraction (G := G) (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).carrier
      (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).form 1)
    (K₂ : NormalizedMeasuredContraction (G := G) (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).carrier
      (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).form (Equiv.swap 0 1)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) K₁)
      (clsOf h00 hc hκ hs hv hsmall hΓ (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) K₂) :=
  ispRel_orders_of_pieces (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714
    (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) (prodLabels Dt (2 + A'.labels))
    (prodPiece_orders h00 hc lin hκ hs hv hsmall hΓ A' hω F Dt V hV hVT hTV hnt) hBal K₁ K₂

include h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ in
/-- Every object has standard contractions in every order. -/
theorem exists_contraction {n : ℕ} (X : VFObject (M := M) (T : Set M) (n + 1)) (e : Equiv.Perm (Fin (n + 1))) :
    Nonempty (NormalizedMeasuredContraction (G := G) X.carrier X.form e) := by
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    X.carrier X.proper
  obtain ⟨F, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    X.carrier X.form (object_levels hv X) e D
  exact ⟨F⟩

include V hV hVT hTV hnt in
/-- **One order of the chain.** A contraction of `A` in the order `σ` is
related to every contraction of `A*` in the order `σ`. -/
theorem chain_order (h714 : Lemma714 M G) (A : VFObject (M := M) (T : Set M) 2) {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G)
      (prepObject (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A).carrier e)
    (σ : Equiv.Perm (Fin 2)) (F₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (L : NormalizedMeasuredContraction (G := G)
      (cellObject h00 hc lin hκ hs hv hsmall hΓ (prepObject (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A)
        (prepObject_form_labels h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A) F).carrier
      (cellObject h00 hc lin hκ hs hv hsmall hΓ (prepObject (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A)
        (prepObject_form_labels h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A) F).form σ) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₀)
      (clsOf h00 hc hκ hs hv hsmall hΓ (cellObject h00 hc lin hκ hs hv hsmall hΓ
        (prepObject (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A)
        (prepObject_form_labels h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A) F) L) := by
  let A' := prepObject (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A
  let hω := prepObject_form_labels h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A
  let D := F.normalization
  let Y := normObject h00 hc hκ hs hv A' hω D
  obtain ⟨KA, hKA⟩ := prepMorphism (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A
  obtain ⟨KY, hKY⟩ := cellMorphism (G := G) h00 hc lin hκ hs hv hsmall hΓ A' hω F
  obtain ⟨H⟩ := exists_contraction (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ Y σ
  have hrel1 : VFRelativelyUnary KA.map (σ (Fin.last 1)) (σ (Fin.last 1)) := by
    rw [hKA]; exact graft_relativelyUnary hc A _ _
  have hrel2 : VFRelativelyUnary KY.map (σ (Fin.last 1)) (σ (Fin.last 1)) := by
    rw [hKY]; exact graft_relativelyUnary hc Y _ _
  have r1 := corollary_7_15 (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (hsmall := hsmall)
    (hΓ := hΓ) (V := V) (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) h714 KA hrel1 F₀
    (normalizedPullback h00 hc lin hκ hs hv hsmall hΓ D H)
  have r2 := cls_normalizedPullback_of_finite (G := G) h00 hc lin hκ hs hv hsmall hΓ D H (object_hFin A' Fin.elim0)
  have r3 := corollary_7_15 (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (hsmall := hsmall)
    (hΓ := hΓ) (V := V) (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) h714 KY hrel2 H L
  exact ispRel_trans r1 (ispRel_trans (ispRel_of_eq r2) r3)

include V hV hVT hTV hnt in
/-- **Lemma 7.23 (`contraction:perm:pair:isp`) for `n = 2`**, with the balanced
case of Lemma 7.21 as a hypothesis. -/
theorem lemma_7_23_two (h714 : Lemma714 M G) (h720 : Lemma720 M G)
    (hBal : BalancedOrders (G := G) h00 hc hκ hs hv hsmall hΓ)
    (A : VFObject (M := M) (T : Set M) 2)
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form 1)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (Equiv.swap 0 1)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
  let A' := prepObject (G := G) h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A
  let hω := prepObject_form_labels h00 hc lin hκ hs hv V hV hVT hTV hnt hsmall hΓ A
  obtain ⟨e, F, hU⟩ := h720 hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ A'.carrier A'.proper
  obtain ⟨Dt⟩ := nonempty_cellData hU
  obtain ⟨L₁⟩ := exists_contraction (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ
    (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) 1
  obtain ⟨L₂⟩ := exists_contraction (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ
    (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) (Equiv.swap 0 1)
  have c1 := chain_order h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A F 1 F₁ L₁
  have c2 := chain_order h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A F (Equiv.swap 0 1) F₂ L₂
  have h22 := lemma_7_22 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A' hω F Dt
    (hBal A' hω F Dt) L₁ L₂
  exact ispRel_trans c1 (ispRel_trans h22 (ispRel_symm c2))

end DiamondIntegral.Section7.Lemma723Two
