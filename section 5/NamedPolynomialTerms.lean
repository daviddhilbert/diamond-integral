import «section 5».PolynomialTerms

/-! Polynomial syntax with named coefficients, uniformly realized by the
actual coefficient homomorphism in every language expansion. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language FirstOrder.Ring

def namedPolynomialTerm {R : Type} [CommRing R] {ι : Type} (p : MvPolynomial ι R) :
    (Language.ring[[R]]).Term ι := (polynomialTerm p).varsToConstants

theorem namedPolynomialTerm_realize {R : Type} [CommRing R] {ι : Type} (p : MvPolynomial ι R)
    (K : Type) [CommRing K] [CompatibleRing K] [(Language.ring[[R]]).Structure K]
    [(Language.ring.lhomWithConstants R).IsExpansionOn K] (c : R →+* K)
    (hc : ∀ a, c a = ((Language.ring.con a : (Language.ring[[R]]).Constants) : K)) (x : ι → K) :
    (namedPolynomialTerm p).realize x = p.eval₂ c x := by
  rw [namedPolynomialTerm, Term.realize_varsToConstants]
  have he : (fun a => ((Language.ring.con a : (Language.ring[[R]]).Constants) : K)) = c :=
    funext (fun a => (hc a).symm)
  rw [he, polynomialTerm_realize]

end DiamondIntegral.Section5
