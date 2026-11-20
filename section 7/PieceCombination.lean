import «section 7».LabelPieces
import «section 7».Corollary715

/-! Combining the two orders over label pieces (for Lemma 7.22).

Let `A` be an object of `μVF^◇[2]` and `L` a definable set of labels. Suppose
the piece of `A` over `L` and the piece over its complement each have standard
contractions in the orders `21` (`e = 1`) and `12` (`e = swap`) with
`μIsp^db`-related head-start-`0` classes. Then any two standard contractions of
`A` in these orders have `μIsp^db`-related classes (`ispRel_orders_of_pieces`).

Proof: a contraction of `A` restricts to both pieces, and its class is the sum
of the classes of the restrictions (`RestrictContractions.cls_headStart_zero_split`).
On each piece, the restriction is related to the given contraction of the same
order by the independence of the centre (`Corollary715.ispRel_same_set`, from
the Lemma 7.14 input). Finally `μIsp^db` is a congruence (`ispRel_add`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.RestrictContractions DiamondIntegral.Section7.LabelPieces
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- `μIsp^db` in positive degree is a congruence. -/
theorem ispRel_add {B : GammaParameters.Base (M := M)} {k : ℕ} {x y x' y' : Cls B (k + 1)}
    (h : IspRel x y) (h' : IspRel x' y') : IspRel (x + x') (y + y') := by
  rw [ispRel_iff (show k + 1 = 1 + k by omega)] at h h' ⊢
  have hc : ∀ {a b : ℕ} (e : a = b) (z w : Cls B a), castCls e (z + w) = castCls e z + castCls e w := by
    intro a b e z w
    subst e
    rfl
  rw [hc, hc]
  exact BlowupCongruence.muIsp_add h h'

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-- The class of a contraction of an object, with head start `0`. -/
abbrev clsOf {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1)) {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :=
  cls (objOf hc T (F.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0 (object_hFin A Fin.elim0))
    (F.headStartObject_doublyBounded 0 Fin.elim0))

/-- Two orders on an object have related classes. -/
def OrdersRelated (A : VFObject (M := M) (T : Set M) 2) : Prop :=
  ∃ (G₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form 1)
    (G₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (Equiv.swap 0 1)),
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A G₁) (clsOf h00 hc hκ hs hv hsmall hΓ A G₂)

include V hV hVT hTV hnt in
/-- **Combining the pieces.** -/
theorem ispRel_orders_of_pieces (h714 : Lemma714 M G) (A : VFObject (M := M) (T : Set M) 2)
    (L : DefSet (rawRVSpace (M := M) A.labels) (T : Set M))
    (hP : OrdersRelated (G := G) h00 hc hκ hs hv hsmall hΓ (pieceObject A L))
    (hB : OrdersRelated (G := G) h00 hc hκ hs hv hsmall hΓ (pieceObject A (complLabels L)))
    (K₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form 1)
    (K₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (Equiv.swap 0 1)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A K₁) (clsOf h00 hc hκ hs hv hsmall hΓ A K₂) := by
  obtain ⟨P₁, P₂, hPP⟩ := hP
  obtain ⟨B₁, B₂, hBB⟩ := hB
  have hC := pieceObject_saturated A L
  have hC' := pieceObject_saturated A (complLabels L)
  have hCp := (pieceObject A L).proper
  have hC'p := (pieceObject A (complLabels L)).proper
  have hdisj := pieces_disjoint A L
  have hcover := pieces_cover A L
  have split₁ := cls_headStart_zero_split h00 hc lin hκ hs hv hsmall hΓ K₁ _ _ hC hC' hCp hC'p hdisj hcover
    (object_hFin A Fin.elim0)
  have split₂ := cls_headStart_zero_split h00 hc lin hκ hs hv hsmall hΓ K₂ _ _ hC hC' hCp hC'p hdisj hcover
    (object_hFin A Fin.elim0)
  have r₁ := ispRel_same_set (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (V := V)
    (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) (hsmall := hsmall) (hΓ := hΓ) h714 (pieceObject A L)
    (restrictContraction h00 hc lin hκ hs hv hsmall hΓ K₁ _ hC hCp) P₁
  have r₂ := ispRel_same_set (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (V := V)
    (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) (hsmall := hsmall) (hΓ := hΓ) h714
    (pieceObject A (complLabels L)) (restrictContraction h00 hc lin hκ hs hv hsmall hΓ K₁ _ hC' hC'p) B₁
  have r₃ := ispRel_same_set (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (V := V)
    (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) (hsmall := hsmall) (hΓ := hΓ) h714 (pieceObject A L)
    P₂ (restrictContraction h00 hc lin hκ hs hv hsmall hΓ K₂ _ hC hCp)
  have r₄ := ispRel_same_set (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (V := V)
    (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) (hsmall := hsmall) (hΓ := hΓ) h714
    (pieceObject A (complLabels L)) B₂ (restrictContraction h00 hc lin hκ hs hv hsmall hΓ K₂ _ hC' hC'p)
  unfold clsOf
  rw [split₁, split₂]
  exact ispRel_trans (ispRel_add r₁ r₂) (ispRel_trans (ispRel_add hPP hBB) (ispRel_add r₃ r₄))

end DiamondIntegral.Section7.PieceCombination
