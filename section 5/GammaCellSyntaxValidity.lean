import «section 5».FirstOrderEulerCertificates

/-! Actual Gamma preimage presentations satisfy the finite quotient and
cylindrical validity formulas. This is the encoding direction of the Euler
certificate construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaFormulaRepresents {P : Type*} {n : ℕ} (D : LRV.Formula (P ⊕ Fin n))
    (v : P → M) (X : Set (Fin n → Values.Gamma (M := M))) : Prop :=
  ∀ x : Fin n → M, D.Realize (Sum.elim v x) ↔ (∀ i, NonzeroRV (x i)) ∧ codeValue ∘ x ∈ X

theorem quotientDomainValidity_of_gamma_presentation {P : Type*} {n : ℕ}
    (U : LRV.Formula (Fin 1)) (E : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (D : LRV.Formula (P ⊕ Fin n)) (v : P → M)
    (X : Set (Fin n → Values.Gamma (M := M))) (hD : gammaFormulaRepresents D v X) :
    (quotientDomainValidityFormula U E D).Realize v := by
  apply (quotientDomainValidityFormula_realize U E D v).mpr
  constructor
  · intro x hx i
    exact (hU _).mpr ((hD x).mp hx |>.1 i)
  · intro x y hx hy he
    have hpx : ∀ i, NonzeroRV (x i) := fun i => (hU _).mp (hx i)
    have hpy : ∀ i, NonzeroRV (y i) := fun i => (hU _).mp (hy i)
    have hq : codeValue ∘ x = codeValue ∘ y :=
      funext (fun i => (hE (x i) (y i) (hpx i) (hpy i)).mp (he i))
    exact (hD x).trans (((and_iff_right hpx).trans
      ((Iff.of_eq (congrArg (fun q => q ∈ X) hq)).trans (and_iff_right hpy).symm)).trans (hD y).symm)

theorem quotientFormulaDomain_eq_of_gamma_presentation {P : Type*} {n : ℕ}
    (D : LRV.Formula (P ⊕ Fin n)) (v : P → M)
    (X : Set (Fin n → Values.Gamma (M := M))) (hD : gammaFormulaRepresents D v X) :
    quotientFormulaDomain D v codeValue = X := by
  ext γ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hD x).mp hx |>.2
  · intro hγ
    obtain ⟨x, hx, hq⟩ := gamma_tuple_code_surjective γ
    exact ⟨x, (hD x).mpr ⟨hx, hq.symm ▸ hγ⟩, hq⟩

theorem cylindricalStepValidity_of_gamma_presentations {P : Type*} {n : ℕ}
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x, y] ↔ codeValue x < codeValue y))
    (k : CylinderFibreKind) (C : LRV.Formula (P ⊕ Fin n))
    (D : LRV.Formula (P ⊕ Fin (n + 1))) (v : P → M)
    (S : Set (Fin n → Values.Gamma (M := M))) (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hC : gammaFormulaRepresents C v S) (hD : gammaFormulaRepresents D v R)
    (hprojection : ∀ z ∈ R, Fin.tail z ∈ S)
    (hshape : ∀ y ∈ S, k.Describes (fun t => Fin.cons t y ∈ R)) :
    (cylindricalStepValidityFormula k U E T C D).Realize v := by
  apply (cylindricalStepValidityFormula_realize k U E T C D v).mpr
  intro y
  constructor
  · intro hy
    obtain ⟨hpy, hqy⟩ := (hC y).mp hy
    apply (cylindricalFibreValidityFormula_quotient k U E T (curryFirstCoordinateFormula D)
      (Sum.elim v y) NonzeroRV codeValue (fun t => Fin.cons t (codeValue ∘ y) ∈ R)
      hU hE hT EndpointLogic.codeValue_surjective ?_).mpr (hshape _ hqy)
    intro t ht
    rw [curryFirstCoordinateFormula_realize, hD]
    have hp : ∀ i : Fin (n + 1), NonzeroRV ((Fin.cons (t 0) y : Fin (n + 1) → M) i) := by
      intro i
      exact Fin.cases ht hpy i
    have he : codeValue ∘ Fin.cons (t 0) y = Fin.cons (codeValue (t 0)) (codeValue ∘ y) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    exact (and_iff_right hp).trans (Iff.of_eq (congrArg (fun q => q ∈ R) he))
  · intro hy t ht hd
    obtain ⟨hp, hm⟩ := (hD (Fin.cons (t 0) y)).mp hd
    have hs := hprojection _ hm
    apply hy
    apply (hC y).mpr
    exact ⟨fun i => hp i.succ, hs⟩

end DiamondIntegral.Section5
