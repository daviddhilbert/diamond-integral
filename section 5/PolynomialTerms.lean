import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial evaluations are represented by one actual ring-language
term uniformly in every compatible target ring and coefficient map.
This keeps the forthcoming rational graph cover valid in elementary
extensions, with every coefficient and input coordinate retained. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring

theorem polynomial_term_exists {R : Type} [CommRing R] {ι : Type} (p : MvPolynomial ι R) :
    ∃ t : Language.ring.Term (R ⊕ ι), ∀ (K : Type) [CommRing K] [CompatibleRing K]
      (c : R →+* K) (x : ι → K), t.realize (Sum.elim c x) = p.eval₂ c x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨.var (.inl a), ?_⟩
    intro K _ _ c x
    simp
  | add p q hp hq =>
    obtain ⟨t, ht⟩ := hp
    obtain ⟨u, hu⟩ := hq
    refine ⟨t + u, ?_⟩
    intro K _ _ c x
    simp only [realize_add, ht K c x, hu K c x, MvPolynomial.eval₂_add]
  | mul_X p i hp =>
    obtain ⟨t, ht⟩ := hp
    refine ⟨t * .var (.inr i), ?_⟩
    intro K _ _ c x
    simp only [realize_mul, ht K c x, Term.realize_var, Sum.elim_inr,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]

def polynomialTerm {R : Type} [CommRing R] {ι : Type} (p : MvPolynomial ι R) :
    Language.ring.Term (R ⊕ ι) := Classical.choose (polynomial_term_exists p)

theorem polynomialTerm_realize {R : Type} [CommRing R] {ι : Type} (p : MvPolynomial ι R)
    (K : Type) [CommRing K] [CompatibleRing K] (c : R →+* K) (x : ι → K) :
    (polynomialTerm p).realize (Sum.elim c x) = p.eval₂ c x :=
  Classical.choose_spec (polynomial_term_exists p) K c x

end DiamondIntegral.Section5
