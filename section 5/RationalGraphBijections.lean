import «section 5».CommonRationalDenominators

/-! Both directions of an actual definable bijection have finite
original-coefficient rational descriptions. The rational matching loci
are themselves definable, including zero-dimensional output tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
attribute [local instance] compatibleRingOfRing

theorem complex_named_formula_definable {α : Type} (φ : (Language.ring[[ℂ]]).Formula α) :
    (Set.univ : Set ℂ).Definable Language.ring {v | φ.Realize v} := by
  let f : ℂ → ↥(Set.univ : Set ℂ) := fun c => ⟨c, Set.mem_univ _⟩
  letI : (LHom.constantsOnMap f).IsExpansionOn ℂ := constantsOnMap_isExpansionOn rfl
  letI : (Language.ring.lhomWithConstantsMap f).IsExpansionOn ℂ :=
    LHom.sumMap_isExpansionOn _ _ _
  refine ⟨(Language.ring.lhomWithConstantsMap f).onFormula φ, ?_⟩
  ext v
  exact (LHom.realize_onFormula _ _).symm

theorem complex_polynomial_zeroSet_definable {α : Type} (p : MvPolynomial α ℂ) :
    (Set.univ : Set ℂ).Definable Language.ring {v | p.eval₂ (RingHom.id ℂ) v = 0} := by
  have h := complex_named_formula_definable ((namedPolynomialTerm p).equal (namedPolynomialTerm 0))
  convert h using 1
  ext v
  simp only [Set.mem_setOf_eq, Formula.realize_equal,
    namedPolynomialTerm_realize p ℂ (RingHom.id ℂ) (fun _ => rfl),
    namedPolynomialTerm_realize (0 : MvPolynomial α ℂ) ℂ (RingHom.id ℂ) (fun _ => rfl),
    MvPolynomial.eval₂_zero]

def rationalTupleEquationSet {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) : Set (Fin n ⊕ Fin m → ℂ) :=
  {v | q.eval₂ (RingHom.id ℂ) (fun i => v (.inl i)) ≠ 0 ∧
    ∀ j, v (.inr j) * q.eval₂ (RingHom.id ℂ) (fun i => v (.inl i)) =
      (p j).eval₂ (RingHom.id ℂ) (fun i => v (.inl i))}

theorem rationalTupleEquationSet_definable {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    (Set.univ : Set ℂ).Definable Language.ring (rationalTupleEquationSet p q) := by
  have hq := (complex_polynomial_zeroSet_definable
    (MvPolynomial.rename (Sum.inl : Fin n → Fin n ⊕ Fin m) q)).compl
  have hp (j : Fin m) := complex_polynomial_zeroSet_definable
    (MvPolynomial.X (Sum.inr j) * MvPolynomial.rename Sum.inl q - MvPolynomial.rename Sum.inl (p j))
  have h := hq.inter (Set.definable_iInter_of_finite hp)
  convert h using 1
  ext v
  simp only [rationalTupleEquationSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_iInter, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, sub_eq_zero]
  rfl

theorem complex_definable_bijection_finite_rational_cover {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (hv : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
      Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z) :
    ∃ (s : Finset ((Fin m → MvPolynomial (Fin n) ℂ) × MvPolynomial (Fin n) ℂ))
      (t : Finset ((Fin n → MvPolynomial (Fin m) ℂ) × MvPolynomial (Fin m) ℂ)),
      ∀ (x : Fin n → ℂ) (y : Fin m → ℂ), Sum.elim x y ∈ G →
        ∃ r ∈ s, ∃ u ∈ t,
          Sum.elim x y ∈ rationalTupleEquationSet r.1 r.2 ∧
          Sum.elim y x ∈ rationalTupleEquationSet u.1 u.2 := by
  obtain ⟨s, hs⟩ := complex_definable_graph_finite_common_denominator_cover G hG hu
  let H : Set (Fin m ⊕ Fin n → ℂ) := {v | v ∘ Sum.swap ∈ G}
  have hH : (Set.univ : Set ℂ).Definable Language.ring H := hG.preimage_comp Sum.swap
  have he (x : Fin n → ℂ) (y : Fin m → ℂ) :
      Sum.elim y x ∈ H ↔ Sum.elim x y ∈ G := by
    have he : Sum.elim y x ∘ Sum.swap = Sum.elim x y := by
      funext i
      cases i <;> rfl
    change (Sum.elim y x ∘ Sum.swap) ∈ G ↔ _
    rw [he]
  obtain ⟨t, ht⟩ := complex_definable_graph_finite_common_denominator_cover H hH
    (fun y x z hx hz => hv y x z ((he x y).mp hx) ((he z y).mp hz))
  refine ⟨s, t, ?_⟩
  intro x y hxy
  obtain ⟨r, hr, hrf⟩ := hs x y hxy
  obtain ⟨u, hu, huf⟩ := ht y x ((he x y).mpr hxy)
  exact ⟨r, hr, u, hu, hrf, huf⟩

end DiamondIntegral.Section5
