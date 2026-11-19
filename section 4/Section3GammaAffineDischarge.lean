import «section 4».Section3GammaAffineInput
import «section 4».GammaQEFlatNormalFormArity
import «section 4».GammaQECoefficientNames
import FubiniTheorems.Prerequisites.Euler.Section3GammaCodeBridge
import FubiniTheorems.Prerequisites.Grothendieck.FullGammaTupleAbstraction
import FubiniTheorems.Prerequisites.Grothendieck.FullGammaPresentations

/-! The multivariate rational-affine normal form for original-base
definable Gamma maps, `Section3GammaAffineInput.Input`, as a theorem.

The finitely many Gamma names of the base used by the graph are first
abstracted to free Gamma variables over the real base. The resulting
Gamma predicate has a flat RV literal normal form with coefficients in the
real base. At every point of the graph, uniqueness of the output gives an
equal-value pair of flat monomials with different output slopes. Solving
that equality for the output gives one of finitely many rational-affine
branches. Its constant is a product of Gamma values of named flat
coefficients and integral powers of the abstracted Gamma names, hence it is
named over the original base. Only ACVF is used: no characteristic,
saturation, nontriviality or HK hypothesis enters.

Literature: definable maps in an ordered vector space over ℚ are piecewise
affine (van den Dries, *Tame Topology and O-minimal Structures*, Ch. 1 §7);
in ACVF, Γ is stably embedded and a pure divisible ordered abelian group
(Haskell–Hrushovski–Macpherson), which gives the statement on paper. Neither
pinned Lean dependency (Mathlib 56a0058, hilbert-mathlib 88bb338) contains
DOAG quantifier elimination or piecewise-linearity of definable maps, so the
proof here goes directly through the pinned RV quantifier elimination
instead of DOAG QE plus stable embeddedness. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section4.Section3GammaAffineDischarge
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3ACVF
open CanonicalRV GuardedRVNormalForm
open GammaDefinableMaps GammaRationalAffineContinuity GammaQEOutputSlopes GammaQECoefficientNames
open DiamondIntegral.Section5.GammaQE (rvGamma rvGamma_eq_iff rvGamma_surjective)
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Solving an equal-value relation of two flat monomials for the output. -/
theorem solve_output {G : Type*} [CommGroup G] (cP cQ gP gQ XP XQ y : G) (a b : ℤ)
    (hab : b < a) (h : cP * (gP * (y ^ a * XP)) = cQ * (gQ * (y ^ b * XQ))) :
    y ^ (a - b).toNat = cQ * gQ * (cP * gP)⁻¹ * (XQ / XP) := by
  have hz : ((a - b).toNat : ℤ) = a - b := Int.toNat_of_nonneg (by omega)
  rw [← zpow_natCast, hz, zpow_sub, ← div_eq_mul_inv, ← div_eq_mul_inv (cQ * gQ),
    div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  calc y ^ a * (cP * gP * XP) = cP * (gP * (y ^ a * XP)) := by ac_rfl
    _ = cQ * (gQ * (y ^ b * XQ)) := h
    _ = cQ * gQ * XQ * y ^ b := by ac_rfl

theorem prod_div_zpow {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι] (x : ι → G)
    (p q : ι → ℤ) : (∏ i, x i ^ q i) / (∏ i, x i ^ p i) = ∏ i, x i ^ (q i - p i) := by
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun i _ => by rw [zpow_sub, div_eq_mul_inv])

/-- Decomposition of a monomial in the abstracted coordinates
`Fin k ⊕ Fin (n + 1)`, with output coordinate `inr 0`. -/
theorem prod_decompose {G : Type*} [CommGroup G] {k n : ℕ}
    (γ : Fin k → G) (x : Fin n → G) (y : G) (p : Fin (k + (n + 1)) → ℤ) :
    ∏ i, (Sum.elim γ (Fin.cons y x : Fin (n + 1) → G) ∘ finSumFinEquiv.symm) i ^ p i =
      (∏ l, γ l ^ p (finSumFinEquiv (Sum.inl l))) *
        (y ^ p (finSumFinEquiv (Sum.inr 0)) *
          ∏ j, x j ^ p (finSumFinEquiv (Sum.inr j.succ))) := by
  rw [← (finSumFinEquiv : Fin k ⊕ Fin (n + 1) ≃ Fin (k + (n + 1))).prod_comp,
    Fintype.prod_sum_type, Fin.prod_univ_succ]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
    Fin.cons_zero, Fin.cons_succ]

/-- The multivariate Section 3 Gamma normal form over any base. -/
theorem input (B : Base (M := M)) : Section3GammaAffineInput.Input B := by
  intro n T hT
  obtain ⟨k, γ, hγ, hW⟩ := hT
  let B0 : Base (M := M) := ⟨B.real, ∅⟩
  let graph : Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | z 0 = T (fun i => z i.succ)}
  have hB' : GammaOrderLogic.GammaDefinable (DiamondIntegral.Section3.adjoinGammaTuple B0 γ) graph :=
    ⟨k, γ, fun i => Or.inr ⟨i, rfl⟩, hW⟩
  have hF := (Section3GammaCodeBridge.full_iff graph).mpr hB'
  obtain ⟨Q, hQ, hQγ⟩ := DiamondIntegral.Section3.fullGamma_tuple_abstraction B0 γ _ hF
  let e : Fin k ⊕ Fin (n + 1) ≃ Fin (k + (n + 1)) := finSumFinEquiv
  let G : (Fin (k + (n + 1)) → Values.Gamma (M := M)) → Prop := fun w => Q (w ∘ e)
  have hG : GammaSyntax.Definable B.real G :=
    DiamondIntegral.Section3.fullGamma_realBase (FullGammaSyntax.Definable.reindex hQ e)
  obtain ⟨I, R, a, r, D, ha, hr, hD⟩ :=
    GammaQEFlatNormalFormArity.gamma_flat_normal_form_arity B.real (k + (n + 1)) G hG
  have haN : ∀ i, a i ∈ vfDefinableClosureFieldBase B := fun i => vf_named_of_mem B (a i) (ha i)
  have hrN : ∀ j, r j ∈ rvNamed B := fun j => rv_named_of_mem B (r j) (hr j)
  let o : Fin (k + (n + 1)) := e (Sum.inr 0)
  let s := dnfMonomialsAt D
  let Tm : Fin s.length → Monomial I R (Fin (k + (n + 1))) := s.get
  let J := {j : Fin s.length × Fin s.length //
    coefficientAt (Tm j.1) a r ≠ 0 ∧ coefficientAt (Tm j.2) a r ≠ 0 ∧
      (Tm j.2).powers o < (Tm j.1).powers o}
  let gam : Monomial I R (Fin (k + (n + 1))) → Values.Gamma (M := M) :=
    fun P => ∏ l, γ l ^ P.powers (e (Sum.inl l))
  let xe : Monomial I R (Fin (k + (n + 1))) → Fin n → ℤ :=
    fun P j => P.powers (e (Sum.inr j.succ))
  let mk : J → Branch B n := fun j =>
    { exponent := fun i => xe (Tm j.val.2) i - xe (Tm j.val.1) i
      denominator := ((Tm j.val.1).powers o - (Tm j.val.2).powers o).toNat
      denominator_ne_zero := by have := j.property.2.2; omega
      constant := rvGamma (coefficientAt (Tm j.val.2) a r) j.property.2.1 * gam (Tm j.val.2) *
        (rvGamma (coefficientAt (Tm j.val.1) a r) j.property.1 * gam (Tm j.val.1))⁻¹
      constant_definable := by
        apply gamma_mul_named
        · exact gamma_mul_named B _ _
            (gamma_named_of_rvNamed B _ _ (coefficientAt_named _ a r haN hrN))
            (gamma_character_named B _ γ hγ)
        · apply gamma_inv_named
          exact gamma_mul_named B _ _
            (gamma_named_of_rvNamed B _ _ (coefficientAt_named _ a r haN hrN))
            (gamma_character_named B _ γ hγ) }
  let eJ := Fintype.equivFin J
  refine ⟨Fintype.card J, fun i => mk (eJ.symm i), ?_⟩
  intro x
  -- The point of the graph over `x`, in the abstracted coordinates.
  let z : Fin (n + 1) → Values.Gamma (M := M) := Fin.cons (T x) x
  let w : Fin (k + (n + 1)) → Values.Gamma (M := M) := Sum.elim γ z ∘ e.symm
  have hrep : ∀ i, ∃ X : RVSort M, ∃ hX : X ≠ 0, rvGamma X hX = w i := fun i => rvGamma_surjective (w i)
  choose X hX hXw using hrep
  have hW' : (fun i => rvGamma (X i) (hX i)) = w := funext hXw
  have hGw : ∀ y, G (Function.update w o y) ↔ y = T x := by
    intro y
    have he : Function.update w o y ∘ e = Sum.elim γ (Fin.cons y x : Fin (n + 1) → _) := by
      have h1 : Function.update w o y = Function.update (Sum.elim γ z) (Sum.inr 0) y ∘ e.symm := by
        rw [Function.update_comp_equiv]
        rfl
      rw [h1, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Sum.update_elim_inr,
        Fin.update_cons_zero]
    change Q (Function.update w o y ∘ e) ↔ _
    rw [he, hQγ]
    change y = T (fun i => (Fin.cons y x : Fin (n + 1) → _) i.succ) ↔ _
    simp only [Fin.cons_succ]
  have hwo : w o = T x := by
    change Sum.elim γ z (e.symm (e (Sum.inr 0))) = T x
    rw [Equiv.symm_apply_apply]
    rfl
  have hGpt : G (fun i => rvGamma (X i) (hX i)) := by
    rw [hW', ← Function.update_eq_self o w, hGw, hwo]
  have hunique : ∀ y, G (Function.update (fun i => rvGamma (X i) (hX i)) o y) →
      y = rvGamma (X o) (hX o) := by
    intro y hy
    rw [hW'] at hy
    rw [hXw, hwo]
    exact (hGw y).mp hy
  obtain ⟨P, hP, P', hP', hP0, hP'0, hval, hslope⟩ :=
    graph_has_critical_pair o a r D G hD X hX hGpt hunique
  obtain ⟨i0, hi0⟩ := List.mem_iff_get.mp hP
  obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp hP'
  have hPi : Tm i0 = P := hi0
  have hP'j : Tm j0 = P' := hj0
  have hPc : coefficientAt (Tm i0) a r ≠ 0 :=
    (rawEval_ne_zero_iff _ a r X hX).mp (by rw [hPi]; exact hP0)
  have hP'c : coefficientAt (Tm j0) a r ≠ 0 :=
    (rawEval_ne_zero_iff _ a r X hX).mp (by rw [hP'j]; exact hP'0)
  have hdec : ∀ p : Fin (k + (n + 1)) → ℤ, ∏ i, w i ^ p i =
      (∏ l, γ l ^ p (e (Sum.inl l))) * (T x ^ p o * ∏ j, x j ^ p (e (Sum.inr j.succ))) :=
    fun p => prod_decompose γ x (T x) p
  -- The equal-value relation in Gamma.
  have heq : rvGamma (coefficientAt (Tm i0) a r) hPc *
      (gam (Tm i0) * (T x ^ (Tm i0).powers o * ∏ j, x j ^ xe (Tm i0) j)) =
      rvGamma (coefficientAt (Tm j0) a r) hP'c *
      (gam (Tm j0) * (T x ^ (Tm j0).powers o * ∏ j, x j ^ xe (Tm j0) j)) := by
    have hv : Values.vrv ((Tm i0).rawEval a r X) = Values.vrv ((Tm j0).rawEval a r X) := by
      rw [hPi, hP'j]
      exact hval
    have hγ' := (rvGamma_eq_iff ((Tm i0).rawEval a r X) ((Tm j0).rawEval a r X)
      ((rawEval_ne_zero_iff _ a r X hX).mpr hPc)
      ((rawEval_ne_zero_iff _ a r X hX).mpr hP'c)).mpr hv
    rw [rvGamma_rawEval _ a r hPc X hX, rvGamma_rawEval _ a r hP'c X hX] at hγ'
    rw [hW'] at hγ'
    unfold valueAt at hγ'
    rw [hdec, hdec] at hγ'
    exact hγ'
  have hslope' : (Tm i0).powers o ≠ (Tm j0).powers o := by
    rw [hPi, hP'j]
    exact hslope
  have finish (jj : J) (hjj : T x ^ (mk jj).denominator =
      (mk jj).constant * ∏ i, x i ^ (mk jj).exponent i) :
      ∃ i, T x = (mk (eJ.symm i)).eval x := by
    refine ⟨eJ jj, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact (rationalAffine_unique _ _ _ _ x (T x) hjj).symm
  rcases lt_or_gt_of_ne hslope' with hlt | hgt
  · let jj : J := ⟨(j0, i0), hP'c, hPc, hlt⟩
    apply finish jj
    change T x ^ ((Tm j0).powers o - (Tm i0).powers o).toNat =
      rvGamma (coefficientAt (Tm i0) a r) hPc * gam (Tm i0) *
        (rvGamma (coefficientAt (Tm j0) a r) hP'c * gam (Tm j0))⁻¹ *
        ∏ i, x i ^ (xe (Tm i0) i - xe (Tm j0) i)
    rw [← prod_div_zpow]
    exact solve_output _ _ _ _ _ _ _ _ _ hlt heq.symm
  · let jj : J := ⟨(i0, j0), hPc, hP'c, hgt⟩
    apply finish jj
    change T x ^ ((Tm i0).powers o - (Tm j0).powers o).toNat =
      rvGamma (coefficientAt (Tm j0) a r) hP'c * gam (Tm j0) *
        (rvGamma (coefficientAt (Tm i0) a r) hPc * gam (Tm i0))⁻¹ *
        ∏ i, x i ^ (xe (Tm j0) i - xe (Tm i0) i)
    rw [← prod_div_zpow]
    exact solve_output _ _ _ _ _ _ _ _ _ hgt heq

end DiamondIntegral.Section4.Section3GammaAffineDischarge
