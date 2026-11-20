import «section 7».BalancedOrders
import «section 7».BalancedMatching
import «section 7».MapClasses

/-! Lemma 7.21 for balanced cells, on the balanced piece of `A*`.

Let `Y` be the prepared balanced piece in the order `e` of the Lemma 7.20
contraction (`BalancedKinds.prepared`), with its balanced translation input
(`BalancedKinds.preparedInput`). Lemma 6.38 for the positioning map gives unary
stages `S₁` of the first family and `S₂` of the second family, and an RV map
`ψ` between their contracted sets with
`vrv(lead ψ z) + vrv(t₁) = vrv(lead z) + vrv(t)` (`BalancedMatching.exists_balanced_matching`).

* Order `e`: the translation `y ↦ y − ε(u, x)`, then `S₁` pulled back.
* The other order `e'`: the translation `x ↦ x − ε⁻¹(u, y)` of the transposed
  cells (`BalancedMatching.swapInput`), then `S₂` pulled back.

The final targets project bijectively onto the contracted sets of `S₁` and `S₂`
(`BalancedOrders.finalProj`). So `Φ = proj⁻¹ ∘ ψ ∘ proj` is a definable
bijection between them. It sends the volume `vrv(t) + vrv(lead z)` to
`vrv(t₁) + vrv(lead ψ z)`, which is equal, and keeps the form, which is read on
the old labels. Hence the two head-start-`0` classes are equal
(`cls_balanced_orders`, via `MapClasses.cls_labelObject_map`). This is the
second case of the paper's proof, with the completion of the referee's report
R132. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BalancedPiece
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.TwoCells DiamondIntegral.Section7.TwoCellInput
open DiamondIntegral.Section7.LabelPieces DiamondIntegral.Section7.Lemma722Cells
open DiamondIntegral.Section7.ProductKinds DiamondIntegral.Section7.BalancedShearStages
open DiamondIntegral.Section7.BalancedKinds DiamondIntegral.Section7.BalancedOrders
open DiamondIntegral.Section7.BalancedMatching DiamondIntegral.Section7.MapClasses
open DiamondIntegral.Section7.TwoStageContractions DiamondIntegral.Section7.ProductCells
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.FiberwiseInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The product of the volume over `Fin (2 + 0)`, reindexed by a permutation. -/
theorem prod_two_append_perm {q : ℕ} (f : Fin q → Gamma M) (σ : Equiv.Perm (Fin 2)) (ν : Fin 2 → Fin q)
    (l : Fin 0 → Fin q) : ∏ i, f (Fin.append (fun i => ν (σ.symm i)) l i) = f (ν 0) * f (ν 1) := by
  rw [Fin.prod_univ_add (a := 2) (b := 0)]
  simp only [Fin.append_left, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [Equiv.prod_comp σ.symm (fun i => f (ν i)), Fin.prod_univ_two]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable (A' : VFObject (M := M) (T : Set M) 2) (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z)
variable {e : Equiv.Perm (Fin 2)} (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F)

theorem balObj_form_labels :
    ∀ p z : (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier, p.val.2 = z.val.2 →
      (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).form p =
        (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).form z :=
  fun p z he => cellObject_form_labels h00 hc linear hκ hs hv hsmall hΓ A' hω F ⟨p.val, p.property.1⟩
    ⟨z.val, z.property.1⟩ he

include V hV hVT hTV hnt in
/-- **The balanced case of Lemma 7.21.** For a normalization `D` of the balanced
piece and an order `e'` whose prepared set is the transpose of the prepared set
in the order `e`, there are standard contractions in the orders `e` and `e'`
with equal head-start-`0` classes. -/
theorem cls_balanced_orders (D : ZeroCenteredData (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier)
    (e' : Equiv.Perm (Fin 2))
    (hcar : (reindexedVFSet D.map.image e').carrier =
      (reindexedVFSet (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D) (Equiv.swap 0 1)).carrier) :
    ∃ (G₁ : NormalizedMeasuredContraction (G := G) (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier
        (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).form e)
      (G₂ : NormalizedMeasuredContraction (G := G) (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier
        (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).form e'),
      ∀ hFin₁ hFin₂,
        cls (objOf hc T (G₁.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin₁)
          (G₁.headStartObject_doublyBounded 0 Fin.elim0)) =
        cls (objOf hc T (G₂.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin₂)
          (G₂.headStartObject_doublyBounded 0 Fin.elim0)) := by
  let Y := prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  have H := preparedInput h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  have ht₁ := secondGraph_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  obtain ⟨S₁, S₂, ψ, hψb, hψold, hψgam⟩ := exists_balanced_matching (G := G) h00 hc linear hκ hs hv V hV hVT hTV hnt
    hsmall hΓ H ht₁
  have H' := swapInput H ht₁
  let R := chosenRadii (G := G) h00 hc linear hκ hs hv hsmall hΓ V hV hVT hTV hnt H
  let R' := chosenRadii (G := G) h00 hc linear hκ hs hv hsmall hΓ V hV hVT hTV hnt H'
  have hω_b := balObj_form_labels h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt
  let A1 := transStage h00 hc linear hκ hs hv hsmall hΓ H R
  let A2 := secondStageB h00 hc linear hκ hs hv hsmall hΓ H R S₁
  let B1 := ProductCells.stageOn (transStage h00 hc linear hκ hs hv hsmall hΓ H' R') hcar
  let B2 := secondStageB h00 hc linear hκ hs hv hsmall hΓ H' R' S₂
  let G₁ := twoStage h00 hc linear hκ hs hv hsmall hΓ D A1 A2
    (descForm h00 hω_b D e (twoStageProgram A1 A2))
    (fun p => descForm_factor h00 hω_b D e (twoStageProgram A1 A2) p)
  let G₂ := twoStage h00 hc linear hκ hs hv hsmall hΓ D B1 B2
    (descForm h00 hω_b D e' (twoStageProgram B1 B2))
    (fun p => descForm_factor h00 hω_b D e' (twoStageProgram B1 B2) p)
  refine ⟨G₁, G₂, fun hFin₁ hFin₂ => ?_⟩
  let P₁ := finalProj h00 hc linear hκ hs hv hsmall hΓ H R S₁
  let P₂ := finalProj h00 hc linear hκ hs hv hsmall hΓ H' R' S₂
  have hP₂ := finalProj_bijective h00 hc linear hκ hs hv hsmall hΓ H' R' S₂
  let Φ : Map A2.contracted B2.contracted := (P₂.inverse hP₂).comp (ψ.comp P₁)
  have hinv : Function.Bijective (P₂.inverse hP₂) :=
    ⟨fun a b h => by
      have h' := congrArg P₂ h
      rwa [Map.apply_inverse, Map.apply_inverse] at h',
     fun b => ⟨P₂ b, Map.inverse_apply P₂ hP₂ b⟩⟩
  have hΦ : Function.Bijective Φ :=
    hinv.comp (hψb.comp (finalProj_bijective h00 hc linear hκ hs hv hsmall hΓ H R S₁))
  have hPΦ : ∀ z, P₂ (Φ z) = ψ (P₁ z) := fun z => Map.apply_inverse P₂ hP₂ _
  -- the old labels of `z` and of `Φ z`
  have hold₁ : ∀ (z : A2.contracted) (i : Fin _), z.val.2 (Fin.castAdd S₁.arity (oldPos _ i)) =
      (P₁ z).val.2 (S₁.oldLabels i) := fun z i => finalB_old h00 hc linear hκ hs hv hsmall hΓ H R S₁ z i
  have hold₂ : ∀ (z : A2.contracted) (i : Fin _), (Φ z).val.2 (Fin.castAdd S₂.arity (oldPos _ i)) =
      z.val.2 (Fin.castAdd S₁.arity (oldPos _ i)) := by
    intro z i
    rw [finalB_old h00 hc linear hκ hs hv hsmall hΓ H' R' S₂ (Φ z) i, hold₁ z i]
    change (P₂ (Φ z)).val.2 (S₂.oldLabels i) = _
    rw [hPΦ]
    exact hψold (P₁ z) i
  have hprod : ∀ z : A2.contracted,
      ∏ i, gam (z.val.2 (Fin.append (fun i => G₁.preparedContraction.data.program.volumeIndex (e.symm i))
        (G₁.oldIndex ∘ (Fin.elim0 : Fin 0 → Fin _)) i)) =
      ∏ i, gam ((Φ z).val.2 (Fin.append (fun i => G₂.preparedContraction.data.program.volumeIndex (e'.symm i))
        (G₂.oldIndex ∘ (Fin.elim0 : Fin 0 → Fin _)) i)) := by
    intro z
    rw [prod_two_append_perm (fun j => gam (z.val.2 j)), prod_two_append_perm (fun j => gam ((Φ z).val.2 j))]
    have v₁₀ : G₁.preparedContraction.data.program.volumeIndex 0 = Fin.natAdd _ S₁.leading :=
      (twoStage_volumeIndex h00 hc linear hκ hs hv hsmall hΓ A1 A2 _ _ 0).trans rfl
    have v₁₁ : G₁.preparedContraction.data.program.volumeIndex 1 = Fin.castAdd S₁.arity (Fin.castAdd _ 1) :=
      (twoStage_volumeIndex h00 hc linear hκ hs hv hsmall hΓ A1 A2 _ _ 1).trans rfl
    have v₂₀ : G₂.preparedContraction.data.program.volumeIndex 0 = Fin.natAdd _ S₂.leading :=
      (twoStage_volumeIndex h00 hc linear hκ hs hv hsmall hΓ B1 B2 _ _ 0).trans rfl
    have v₂₁ : G₂.preparedContraction.data.program.volumeIndex 1 = Fin.castAdd S₂.arity (Fin.castAdd _ 1) :=
      (twoStage_volumeIndex h00 hc linear hκ hs hv hsmall hΓ B1 B2 _ _ 1).trans rfl
    simp only [v₁₀, v₁₁, v₂₀, v₂₁]
    have t₁ := finalB_t h00 hc linear hκ hs hv hsmall hΓ H R S₁ z
    have t₂ := finalB_t h00 hc linear hκ hs hv hsmall hΓ H' R' S₂ (Φ z)
    rw [t₁, t₂]
    have hu : (fun i => (Φ z).val.2 (Fin.castAdd S₂.arity (oldPos _ i))) =
        fun i => (P₁ z).val.2 (S₁.oldLabels i) := funext fun i => (hold₂ z i).trans (hold₁ z i)
    have hu' : (fun i => z.val.2 (Fin.castAdd S₁.arity (oldPos _ i))) =
        fun i => (P₁ z).val.2 (S₁.oldLabels i) := funext fun i => hold₁ z i
    rw [hu, hu']
    have hne := nonempty_cell_of_final h00 hc linear hκ hs hv hsmall hΓ H R S₁ z
    rw [hu'] at hne
    rw [secondParadigm_val H hne]
    have hlead₁ : z.val.2 (Fin.natAdd _ S₁.leading) = (P₁ z).val.2 S₁.leading := rfl
    have hlead₂ : (Φ z).val.2 (Fin.natAdd _ S₂.leading) = (ψ (P₁ z)).val.2 S₂.leading := by
      change (P₂ (Φ z)).val.2 S₂.leading = _
      rw [hPΦ]
    rw [hlead₁, hlead₂]
    exact (hψgam (P₁ z)).symm
  have hρ : ∀ z : A2.contracted, ((descForm h00 hω_b D e (twoStageProgram A1 A2)) z).val =
      ((descForm h00 hω_b D e' (twoStageProgram B1 B2)) (Φ z)).val := by
    intro z
    obtain ⟨y, rfl⟩ := (twoStageProgram A1 A2).surjective z
    obtain ⟨p, rfl⟩ := (prepOf_bijective h00 D e).surjective y
    rw [descForm_factor]
    symm
    apply descForm_labels
    intro i
    change (Φ ((twoStageProgram A1 A2).toMap (prepOf D e p))).val.2
      (Fin.castAdd S₂.arity (oldPos _ (Fin.natAdd 2 i))) = p.val.2 i
    rw [hold₂]
    exact ((twoStageProgram A1 A2).retained (prepOf D e p) (Fin.natAdd 2 i)).trans (prepOf_labels D e p i)
  exact cls_labelObject_map hc rfl G₁.preparedContraction.lift.originalTarget_recover
    G₂.preparedContraction.lift.originalTarget_recover _ _ Φ hΦ hprod _ _ hρ _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end DiamondIntegral.Section7.BalancedPiece
