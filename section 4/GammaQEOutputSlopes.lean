import Section3.GammaQEFlatPerturbation

/-! Flat RV literals in an arbitrary finite set of RV variables, with one
distinguished output variable. Multiplying the output by a nonzero RV
element scales every flat monomial by its output slope. If a point of a
Gamma graph met no equal-value pair of distinct output slopes, a small
output perturbation would keep every literal of a true clause, against
uniqueness of the output. This is the arity-generic form of the binary
argument in `DiamondIntegral.Section5.GammaQE.graph_has_critical_pair`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
noncomputable section
namespace DiamondIntegral.Section4.GammaQEOutputSlopes
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV GuardedRVNormalForm
open DiamondIntegral.Section5.GammaQE (rvGamma rvGamma_val rv_inK_iff gamma_val_zpow rv_value_zpow
  rvGamma_mul rvGamma_eq_iff raw_residue_sum_inK scaled_residue_equality scaled_value_order_zero)
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {I R V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Multiply only the output variable `o` by `t`. -/
def perturbAt (o : V) (x : V → RVSort M) (t : RVSort M) : V → RVSort M :=
  Function.update x o (x o * t)

/-- The variable-free factor of a flat monomial. -/
def coefficientAt (P : Monomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M) : RVSort M :=
  RVOperations.rvHom (P.numerator.realize a) / RVOperations.rvHom (P.denominator.realize a) *
    P.coefficient.prod (fun i n => r i ^ n)

theorem rawEval_eq_prod (P : Monomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M)
    (x : V → RVSort M) : P.rawEval a r x = coefficientAt P a r * ∏ i, x i ^ P.powers i := by
  rw [Monomial.rawEval, P.powers.prod_fintype (fun i n => x i ^ n) (fun i => zpow_zero (x i))]
  rfl

theorem prod_perturbAt (o : V) (x : V → RVSort M) (t : RVSort M) (p : V → ℤ) :
    ∏ i, perturbAt o x t i ^ p i = (∏ i, x i ^ p i) * t ^ p o := by
  have h (i : V) : perturbAt o x t i ^ p i = x i ^ p i * (Pi.mulSingle o (t ^ p o) : V → RVSort M) i := by
    by_cases hi : i = o
    · subst hi
      simp only [perturbAt, Function.update_self, mul_zpow, Pi.mulSingle_eq_same]
    · simp only [perturbAt, Function.update_of_ne hi, Pi.mulSingle_eq_of_ne hi, mul_one]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, Finset.prod_pi_mulSingle']
  simp only [Finset.mem_univ, ite_true]

theorem rawEval_perturbAt (o : V) (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : V → RVSort M) (t : RVSort M) :
    P.rawEval a r (perturbAt o x t) = P.rawEval a r x * t ^ P.powers o := by
  rw [rawEval_eq_prod, rawEval_eq_prod, prod_perturbAt, mul_assoc]

theorem rawEval_ne_zero_iff (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : V → RVSort M) (hx : ∀ i, x i ≠ 0) :
    P.rawEval a r x ≠ 0 ↔ coefficientAt P a r ≠ 0 := by
  rw [rawEval_eq_prod]
  have hp : ∏ i, x i ^ P.powers i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hx i))
  constructor
  · intro h hc
    apply h
    rw [hc, zero_mul]
  · intro hc
    exact mul_ne_zero hc hp

/-- The Gamma value of a flat monomial with nonzero coefficient. -/
def valueAt (P : Monomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M)
    (hc : coefficientAt P a r ≠ 0) (u : V → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  rvGamma (coefficientAt P a r) hc * ∏ i, u i ^ P.powers i

theorem gamma_val_prod (u : V → Values.Gamma (M := M)) (p : V → ℤ) :
    (∏ i, u i ^ p i).val = ∏ i, (u i).val ^ p i := by
  have h := map_prod (Values.gammaValHom (M := M)) (fun i => u i ^ p i) Finset.univ
  refine h.trans ?_
  exact Finset.prod_congr rfl (fun i _ => gamma_val_zpow (u i) (p i))

theorem vrv_prod (x : V → RVSort M) (p : V → ℤ) :
    Values.vrv (∏ i, x i ^ p i) = ∏ i, Values.vrv (x i) ^ p i := by
  have h := map_prod (RVOperations.vrvHom (M := M)) (fun i => x i ^ p i) Finset.univ
  refine h.trans ?_
  exact Finset.prod_congr rfl (fun i _ => rv_value_zpow (x i) (p i))

theorem rvGamma_congr {s t : RVSort M} (hs : s ≠ 0) (ht : t ≠ 0) (h : s = t) :
    rvGamma s hs = rvGamma t ht := by
  subst h
  rfl

theorem rvGamma_rawEval (P : Monomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M)
    (hc : coefficientAt P a r ≠ 0) (x : V → RVSort M) (hx : ∀ i, x i ≠ 0) :
    rvGamma (P.rawEval a r x) ((rawEval_ne_zero_iff P a r x hx).mpr hc) =
      valueAt P a r hc (fun i => rvGamma (x i) (hx i)) := by
  apply Subtype.ext
  rw [rvGamma_val, rawEval_eq_prod, valueAt, Values.gamma_val_mul, rvGamma_val,
    RVOperations.vrv_mul, gamma_val_prod, vrv_prod]
  rfl

def SlopesSeparatedAt (o : V) (s : List (Monomial I R V)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : V → RVSort M) : Prop :=
  ∀ P ∈ s, ∀ Q ∈ s, P.rawEval a r x ≠ 0 → Q.rawEval a r x ≠ 0 →
    Values.vrv (P.rawEval a r x) = Values.vrv (Q.rawEval a r x) → P.powers o = Q.powers o

theorem residue_term_fixed (o : V) (s : List (Monomial I R V)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : V → RVSort M) (h1 : Monomial.one ∈ s)
    (hs : SlopesSeparatedAt o s a r x) (P : Monomial I R V) (hP : P ∈ s)
    (hK : ValuedModelMap.inK (P.rawEval a r x)) (t : RVSort M) :
    P.rawEval a r (perturbAt o x t) = P.rawEval a r x := by
  rw [rawEval_perturbAt]
  by_cases hz : P.rawEval a r x = 0
  · rw [hz, zero_mul]
  · have hv : Values.vrv (P.rawEval a r x) = 1 := (rv_inK_iff _).mp hK |>.resolve_left hz
    have hq := hs P hP Monomial.one h1 hz
      (by rw [Monomial.rawEval_one]; exact one_ne_zero)
      (by rw [Monomial.rawEval_one, RVOperations.vrv_one]; exact hv)
    have hq0 : P.powers o = 0 := by simpa only [Monomial.one, Finsupp.zero_apply] using hq
    rw [hq0, zpow_zero, mul_one]

theorem residue_polynomial_fixed (o : V) (s : List (Monomial I R V)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : V → RVSort M) (h1 : Monomial.one ∈ s)
    (hs : SlopesSeparatedAt o s a r x) (P : KPolynomial I R V)
    (hP : ∀ i, P.terms i ∈ s) (hD : P.Domain a r x) (t : RVSort M) :
    P.Domain a r (perturbAt o x t) ∧ P.rawEval a r (perturbAt o x t) = P.rawEval a r x := by
  have he (i : Fin P.size) :
      (P.terms i).rawEval a r (perturbAt o x t) = (P.terms i).rawEval a r x :=
    residue_term_fixed o s a r x h1 hs (P.terms i) (hP i) (hD i).2 t
  constructor
  · intro i
    exact ⟨(hD i).1, (he i).symm ▸ (hD i).2⟩
  · unfold KPolynomial.rawEval
    rw [funext he]

theorem polynomial_inK (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : V → RVSort M) : ValuedModelMap.inK (P.rawEval a r x) :=
  raw_residue_sum_inK _

def literalMonomialsAt : RVLiteral I R V → List (Monomial I R V)
  | .equality E _ => [E.left, E.right] ++ List.ofFn E.leftK.terms ++ List.ofFn E.rightK.terms
  | .order E _ => [E.left, E.right]

def ValueComparisonsPreservedAt (o : V) (s : List (Monomial I R V))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : V → RVSort M) (t : RVSort M) : Prop :=
  ∀ P ∈ s, ∀ Q ∈ s,
    (Values.vrv (P.rawEval a r (perturbAt o x t)) ≤ Values.vrv (Q.rawEval a r (perturbAt o x t)) ↔
      Values.vrv (P.rawEval a r x) ≤ Values.vrv (Q.rawEval a r x))

theorem value_equality_preserved (o : V) (s : List (Monomial I R V))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : V → RVSort M) (t : RVSort M)
    (hv : ValueComparisonsPreservedAt o s a r x t) (P Q : Monomial I R V)
    (hP : P ∈ s) (hQ : Q ∈ s) :
    Values.vrv (P.rawEval a r x * t ^ P.powers o) = Values.vrv (Q.rawEval a r x * t ^ Q.powers o) →
      Values.vrv (P.rawEval a r x) = Values.vrv (Q.rawEval a r x) := by
  intro he
  rw [← rawEval_perturbAt, ← rawEval_perturbAt] at he
  exact le_antisymm ((hv P hP Q hQ).mp he.le) ((hv Q hQ P hP).mp he.ge)

theorem literal_preserved (o : V) (s : List (Monomial I R V))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : V → RVSort M)
    (h1 : Monomial.one ∈ s) (hs : SlopesSeparatedAt o s a r x) (t : RVSort M) (ht : t ≠ 0)
    (hv : ValueComparisonsPreservedAt o s a r x t) (L : RVLiteral I R V)
    (hL : ∀ P ∈ literalMonomialsAt L, P ∈ s) (h : L.holds a r x) :
    L.holds a r (perturbAt o x t) := by
  cases L with
  | equality E pos =>
    have hEL : E.left ∈ s := hL _ (by simp [literalMonomialsAt])
    have hER : E.right ∈ s := hL _ (by simp [literalMonomialsAt])
    have hKL := residue_polynomial_fixed o s a r x h1 hs E.leftK
      (fun i => hL _ (by simp [literalMonomialsAt, List.mem_ofFn])) h.1.2.1 t
    have hKR := residue_polynomial_fixed o s a r x h1 hs E.rightK
      (fun i => hL _ (by simp [literalMonomialsAt, List.mem_ofFn])) h.1.2.2.2 t
    refine ⟨⟨h.1.1, hKL.1, h.1.2.2.1, hKR.1⟩, ?_⟩
    have he := scaled_residue_equality (E.left.rawEval a r x) (E.right.rawEval a r x)
      (E.leftK.rawEval a r x) (E.rightK.rawEval a r x) t ht
      (polynomial_inK _ a r x) (polynomial_inK _ a r x) _ _
      (hs _ hEL _ hER) (value_equality_preserved o s a r x t hv _ _ hEL hER)
    change NFTest.signed pos _
    rw [rawEval_perturbAt, rawEval_perturbAt, hKL.2, hKR.2]
    cases pos <;> simp only [NFTest.signed, Bool.false_eq_true, ite_false, ite_true] at *
    · exact not_congr he |>.mpr h.2
    · exact he.mpr h.2
  | order E pos =>
    refine ⟨h.1, ?_⟩
    have hc := hv E.left (hL _ (by simp [literalMonomialsAt]))
      E.right (hL _ (by simp [literalMonomialsAt]))
    have he : iLe (E.left.rawEval a r (perturbAt o x t)).val
        (E.right.rawEval a r (perturbAt o x t)).val ↔
        iLe (E.left.rawEval a r x).val (E.right.rawEval a r x).val := by
      simpa only [Values.vrv_le_iff] using hc
    cases pos <;>
      simp only [RVLiteral.comparison, NFTest.signed, Bool.false_eq_true, ite_false, ite_true] at *
    · exact not_congr he |>.mpr h.2
    · exact he.mpr h.2

section Perturbation
local instance gammaTopology : TopologicalSpace (Values.Gamma (M := M)) := Preorder.topology _
local instance gammaOrderTopology : OrderTopology (Values.Gamma (M := M)) := ⟨rfl⟩

theorem finite_perturbation (o : V) (s : List (Monomial I R V))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : V → RVSort M)
    (hs : SlopesSeparatedAt o s a r x) :
    ∃ t : RVSort M, ∃ ht : t ≠ 0, 1 < rvGamma t ht ∧ ValueComparisonsPreservedAt o s a r x t := by
  let J := s.toFinset.filter (fun P => P.rawEval a r x ≠ 0)
  let av : Monomial I R V → Values.Gamma (M := M) := fun P =>
    if h : P.rawEval a r x ≠ 0 then rvGamma (P.rawEval a r x) h else 1
  have hsep : ∀ P ∈ J, ∀ Q ∈ J, av P = av Q → P.powers o = Q.powers o := by
    intro P hP Q hQ he
    obtain ⟨hPs, hP0⟩ := Finset.mem_filter.mp hP
    obtain ⟨hQs, hQ0⟩ := Finset.mem_filter.mp hQ
    apply hs P (List.mem_toFinset.mp hPs) Q (List.mem_toFinset.mp hQs) hP0 hQ0
    simpa only [av, dif_pos hP0, dif_pos hQ0, rvGamma_val] using congrArg Subtype.val he
  obtain ⟨e, he, hcomp⟩ :=
    DiamondIntegral.Section5.GammaFinitePerturbation.finite_comparisons J av (fun P => P.powers o) hsep
  obtain ⟨t, ht, hte⟩ := DiamondIntegral.Section5.GammaQE.rvGamma_surjective e
  refine ⟨t, ht, hte.symm ▸ he, ?_⟩
  intro P hP Q hQ
  by_cases hP0 : P.rawEval a r x = 0
  · rw [rawEval_perturbAt, rawEval_perturbAt]
    exact scaled_value_order_zero _ _ t ht _ _ (Or.inl hP0)
  · by_cases hQ0 : Q.rawEval a r x = 0
    · rw [rawEval_perturbAt, rawEval_perturbAt]
      exact scaled_value_order_zero _ _ t ht _ _ (Or.inr hQ0)
    · have hPj : P ∈ J := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hP, hP0⟩
      have hQj : Q ∈ J := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hQ, hQ0⟩
      have hc := hcomp P hPj Q hQj
      change ((av P * e ^ P.powers o).val ≤ (av Q * e ^ Q.powers o).val ↔
        (av P).val ≤ (av Q).val) at hc
      simp only [av, dif_pos hP0, dif_pos hQ0, Values.gamma_val_mul, gamma_val_zpow,
        rvGamma_val] at hc
      rw [← hte, rvGamma_val] at hc
      simpa only [rawEval_perturbAt, RVOperations.vrv_mul, rv_value_zpow] using hc

end Perturbation

/-- All monomials of a literal DNF, together with the constant monomial one. -/
def dnfMonomialsAt (D : LiteralDNF I R V) : List (Monomial I R V) :=
  Monomial.one :: D.flatten.flatMap literalMonomialsAt

theorem rvGamma_perturbAt (o : V) (x : V → RVSort M) (hx : ∀ i, x i ≠ 0) (t : RVSort M)
    (ht : t ≠ 0) (hxt : ∀ i, perturbAt o x t i ≠ 0) :
    (fun i => rvGamma (perturbAt o x t i) (hxt i)) =
      Function.update (fun i => rvGamma (x i) (hx i)) o (rvGamma (x o) (hx o) * rvGamma t ht) := by
  funext i
  by_cases hi : i = o
  · subst hi
    rw [Function.update_self, ← rvGamma_mul (x i) t (hx i) ht]
    exact rvGamma_congr _ _ (by simp only [perturbAt, Function.update_self])
  · rw [Function.update_of_ne hi]
    exact rvGamma_congr _ _ (by simp only [perturbAt, Function.update_of_ne hi])

/-- A Gamma predicate presented by a flat literal DNF on all nonzero RV
representatives, at a point where it determines coordinate `o` uniquely,
meets an equal-value pair of active monomials with distinct output slopes. -/
theorem graph_has_critical_pair (o : V) (a : I → VFType (M := M)) (r : R → RVSort M)
    (D : LiteralDNF I R V) (G : (V → Values.Gamma (M := M)) → Prop)
    (hgraph : ∀ (x : V → RVSort M) (hx : ∀ i, x i ≠ 0),
      G (fun i => rvGamma (x i) (hx i)) ↔ PolarityDNF.holds (RVLiteral.holds a r x) D)
    (x : V → RVSort M) (hx : ∀ i, x i ≠ 0) (h : G (fun i => rvGamma (x i) (hx i)))
    (hunique : ∀ y, G (Function.update (fun i => rvGamma (x i) (hx i)) o y) →
      y = rvGamma (x o) (hx o)) :
    ∃ P ∈ dnfMonomialsAt D, ∃ Q ∈ dnfMonomialsAt D,
      P.rawEval a r x ≠ 0 ∧ Q.rawEval a r x ≠ 0 ∧
      Values.vrv (P.rawEval a r x) = Values.vrv (Q.rawEval a r x) ∧ P.powers o ≠ Q.powers o := by
  by_contra hn
  have hs : SlopesSeparatedAt o (dnfMonomialsAt D) a r x := by
    intro P hP Q hQ hP0 hQ0 he
    by_contra hne
    exact hn ⟨P, hP, Q, hQ, hP0, hQ0, he, hne⟩
  obtain ⟨t, ht, he, hv⟩ := finite_perturbation o (dnfMonomialsAt D) a r x hs
  have hxt : ∀ i, perturbAt o x t i ≠ 0 := by
    intro i
    by_cases hi : i = o
    · subst hi
      simp only [perturbAt, Function.update_self]
      exact mul_ne_zero (hx i) ht
    · simp only [perturbAt, Function.update_of_ne hi]
      exact hx i
  obtain ⟨C, hC, htrue⟩ := (hgraph x hx).mp h
  have hnew : PolarityDNF.holds (RVLiteral.holds a r (perturbAt o x t)) D := by
    refine ⟨C, hC, ?_⟩
    intro L hL
    apply literal_preserved o (dnfMonomialsAt D) a r x (by simp [dnfMonomialsAt]) hs t ht hv L ?_
      (htrue L hL)
    intro P hP
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨L, List.mem_flatten.mpr ⟨C, hC, hL⟩, hP⟩
  have hG := (hgraph (perturbAt o x t) hxt).mpr hnew
  rw [rvGamma_perturbAt o x hx t ht hxt] at hG
  have hout := hunique _ hG
  have hone : rvGamma t ht = 1 := mul_left_cancel (hout.trans (mul_one _).symm)
  exact (ne_of_gt he) hone

end DiamondIntegral.Section4.GammaQEOutputSlopes
