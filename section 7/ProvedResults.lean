import «section 7».Lemma723TwoFinal
import «section 7».Lemma714Final
import «section 7».Lemma720Main

/-! Section 7 results with the Lemma 7.14 and Lemma 7.20 inputs discharged.

Lemma 7.14 (`Lemma714Reduce.lemma714 : FiberwiseInput.Lemma714 M G`) and
Lemma 7.20 (`Lemma720.lemma720 M G : TwoCellInput.Lemma720 M G`) are proved. The
results below are the downstream results without the hypotheses `h714`, `h720`.
The forms taking the hypotheses are kept, since later Section 7 work uses them. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ProvedResults
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.PieceCombination DiamondIntegral.Section7.Lemma722Cells
open DiamondIntegral.Section7.ProductKinds DiamondIntegral.Section7.TwoCellInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include V hV hVT hTV hnt in
/-- **Independence of the centre** (Lemma 7.14 with equal sets): any two standard
contractions of one object in the same order are `μIsp^db`-related. -/
theorem ispRel_same_set {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1)) {e : Equiv.Perm (Fin (n + 1))}
    (F₁ F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) :=
  Corollary715.ispRel_same_set (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv) (V := V)
    (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt) (hsmall := hsmall) (hΓ := hΓ) Lemma714Reduce.lemma714 A F₁ F₂

include V hV hVT hTV hnt in
/-- **Corollary 7.15 (`contraction:same:perm:isp`).** -/
theorem corollary_7_15 {n : ℕ} {e : Equiv.Perm (Fin (n + 1 + 1))}
    {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)} (F : Morphism G A' A'')
    (hF : VFRelativelyUnary F.map (e (Fin.last (n + 1))) (e (Fin.last (n + 1))))
    (F' : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
    (F'' : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A' F') (clsOf h00 hc hκ hs hv hsmall hΓ A'' F'') :=
  Corollary715Fibres.corollary_7_15 (G := G) (hc := hc) (h00 := h00) (hκ := hκ) (hs := hs) (hv := hv)
    (hsmall := hsmall) (hΓ := hΓ) (V := V) (hV := hV) (hVT := hVT) (hTV := hTV) (hnt := hnt)
    Lemma714Reduce.lemma714 F hF F' F''

include V hV hVT hTV hnt in
/-- **Lemma 7.22 (`subset:partitioned:2:unit:contracted`), on the object `A*`.** -/
theorem lemma_7_22 (A' : VFObject (M := M) (T : Set M) 2)
    (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z) {e : Equiv.Perm (Fin 2)}
    (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F)
    (K₁ : NormalizedMeasuredContraction (G := G) (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).carrier
      (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).form 1)
    (K₂ : NormalizedMeasuredContraction (G := G) (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).carrier
      (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F).form (Equiv.swap 0 1)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) K₁)
      (clsOf h00 hc hκ hs hv hsmall hΓ (cellObject h00 hc lin hκ hs hv hsmall hΓ A' hω F) K₂) :=
  Lemma723Two.lemma_7_22 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ Lemma714Reduce.lemma714 A' hω F Dt
    (Lemma723TwoFinal.balancedOrders h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A' hω F Dt) K₁ K₂

include V hV hVT hTV hnt in
/-- **Lemma 7.23 (`contraction:perm:pair:isp`) for `n = 2`.** -/
theorem lemma_7_23_n2 (A : VFObject (M := M) (T : Set M) 2)
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form 1)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (Equiv.swap 0 1)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) :=
  Lemma723TwoFinal.lemma_7_23_n2 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ Lemma714Reduce.lemma714
    (Lemma720.lemma720 M G) A F₁ F₂

end DiamondIntegral.Section7.ProvedResults
