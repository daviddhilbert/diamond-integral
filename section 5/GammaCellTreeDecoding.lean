import «section 5».CylindricalFormulaTrees

/-! Decoding a valid finite formula tree gives an actual cylindrical cell
in the native Gamma sort, so the certificate computes the actual Euler value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def CylindricalFormulaTree.gammaDomain {P : Type*} {n : ℕ}
    (C : CylindricalFormulaTree LRV P n) (v : P → M) : Set (Fin n → Values.Gamma (M := M)) :=
  quotientFormulaDomain C.domain v (codeValue (M := M))

def CylindricalFormulaTree.gammaDefinable {P : Type*} (B : Base (M := M)) (v : P → M) :
    {n : ℕ} → CylindricalFormulaTree LRV P n → Prop
  | _, .base _ => True
  | _, .step C k D => C.gammaDefinable B v ∧ GammaDefinable B ((CylindricalFormulaTree.step C k D).gammaDomain v)

theorem CylindricalFormulaTree.gamma_shaped_of_validity {P : Type*}
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x, y] ↔ codeValue x < codeValue y))
    (B : Base (M := M)) (v : P → M) {n : ℕ} (C : CylindricalFormulaTree LRV P n)
    (hdef : C.gammaDefinable B v) (hvalid : (C.validity U E T).Realize v) :
    ShapedGammaCell B n (C.gammaDomain v) C.shape := by
  induction C with
  | base D =>
    have he : quotientFormulaDomain D v (codeValue (M := M)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro γ
      have hd := (setEqualityValidityFormula_realize D ⊤ v).mp hvalid
      have hpt : D.Realize (Sum.elim v (Fin.elim0 : Fin 0 → M)) := by
        have hmem : (Fin.elim0 : Fin 0 → M) ∈ {x | (⊤ : LRV.Formula (P ⊕ Fin 0)).Realize (Sum.elim v x)} := by simp
        exact (Set.ext_iff.mp hd _).mpr hmem
      exact ⟨Fin.elim0, hpt, Subsingleton.elim _ _⟩
    change ShapedGammaCell B 0 (quotientFormulaDomain D v codeValue) .base
    rw [he]
    exact .base
  | @step n C k D ih =>
    simp only [CylindricalFormulaTree.validity, Formula.realize_inf] at hvalid
    have hCvalid : (C.validity U E T).Realize v := hvalid.1.1
    have hDvalid : (quotientDomainValidityFormula U E D).Realize v := hvalid.1.2
    have hstep := (cylindricalStepValidityFormula_realize k U E T C.domain D v).mp hvalid.2
    have hCmem (x : Fin n → M) : C.domain.Realize (Sum.elim v x) ↔
        (∀ i, NonzeroRV (x i)) ∧ (codeValue ∘ x) ∈ C.gammaDomain v :=
      quotientFormulaDomain_full_preimage U E C.domain v NonzeroRV codeValue hU hE
        (C.domainValidity U E T v hCvalid) x
    have hDmem (x : Fin (n + 1) → M) : D.Realize (Sum.elim v x) ↔
        (∀ i, NonzeroRV (x i)) ∧ (codeValue ∘ x) ∈ (CylindricalFormulaTree.step C k D).gammaDomain v :=
      quotientFormulaDomain_full_preimage U E D v NonzeroRV codeValue hU hE hDvalid x
    apply shaped_cell_of_fibre_certificate B (C.gammaDomain v) C.shape (ih hdef.1 hCvalid)
      k ((CylindricalFormulaTree.step C k D).gammaDomain v) hdef.2
    · rintro γ ⟨x, hx, rfl⟩
      change D.Realize (Sum.elim v x) at hx
      have hpx := (hDmem x).mp hx |>.1
      have hc : C.domain.Realize (Sum.elim v (Fin.tail x)) := by
        by_contra hn
        have hh := (hstep (Fin.tail x)).2 hn (fun _ => x 0) ((hU _).mpr (hpx 0))
        apply hh
        simpa only [Fin.cons_self_tail] using hx
      exact ⟨Fin.tail x, hc, rfl⟩
    · rintro γ ⟨y, hy, rfl⟩
      change C.domain.Realize (Sum.elim v y) at hy
      have hpy := (hCmem y).mp hy |>.1
      apply (cylindricalFibreValidityFormula_quotient k U E T (curryFirstCoordinateFormula D)
        (Sum.elim v y) NonzeroRV codeValue
        (fun (t : Values.Gamma (M := M)) => Fin.cons t ((codeValue (M := M)) ∘ y) ∈ (CylindricalFormulaTree.step C k D).gammaDomain v)
        hU hE hT EndpointLogic.codeValue_surjective ?_).mp ((hstep y).1 hy)
      intro t ht
      rw [curryFirstCoordinateFormula_realize, hDmem]
      have hp : ∀ i : Fin (n + 1), NonzeroRV ((Fin.cons (t 0) y : Fin (n + 1) → M) i) := by
        intro i
        exact Fin.cases ht hpy i
      have he : codeValue ∘ Fin.cons (t 0) y = Fin.cons (codeValue (t 0)) (codeValue ∘ y) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simp only [hp, forall_const, true_and, he]

def CylindricalFormulaTree.rawDefinable {P : Type*} (B : Base (M := M)) (v : P → M) :
    {n : ℕ} → CylindricalFormulaTree LRV P n → Prop
  | _, .base _ => True
  | _, .step C _ D => C.rawDefinable B v ∧
      DefinableOverBase B (fun _ => .rv) {x | D.Realize (Sum.elim v x)}

theorem CylindricalFormulaTree.gamma_domain_definable_of_raw {P : Type*}
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (B : Base (M := M)) (v : P → M) {n : ℕ} (C : CylindricalFormulaTree LRV P n)
    (hvalid : (C.validity U E T).Realize v)
    (hraw : DefinableOverBase B (fun _ => .rv) {x | C.domain.Realize (Sum.elim v x)}) :
    GammaDefinable B (C.gammaDomain v) := by
  change DefinableOverBase B (fun _ : Fin n => .rv)
    {z | Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ C.gammaDomain v}
  have he : {z | Proper z ∧ (fun i => codeValue (M := M) (z i)) ∈ C.gammaDomain v} =
      {x | C.domain.Realize (Sum.elim v x)} := by
    ext z
    exact (quotientFormulaDomain_full_preimage U E C.domain v NonzeroRV codeValue hU hE
      (C.domainValidity U E T v hvalid) z).symm
  rw [he]
  exact hraw

theorem CylindricalFormulaTree.gamma_definable_of_raw {P : Type*}
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (B : Base (M := M)) (v : P → M) {n : ℕ} (C : CylindricalFormulaTree LRV P n)
    (hvalid : (C.validity U E T).Realize v) (hraw : C.rawDefinable B v) : C.gammaDefinable B v := by
  induction C with
  | base D => trivial
  | step C k D ih =>
    have hh := hvalid
    simp only [CylindricalFormulaTree.validity, Formula.realize_inf] at hh
    exact ⟨ih hh.1.1 hraw.1,
      (CylindricalFormulaTree.step C k D).gamma_domain_definable_of_raw U E T hU hE B v hvalid hraw.2⟩

theorem CylindricalFormulaTree.gamma_euler_value {P : Type*}
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x, y] ↔ codeValue x < codeValue y))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (v : P → M) {n : ℕ} (C : CylindricalFormulaTree LRV P n)
    (hvalid : (C.validity U E T).Realize v) (hraw : C.rawDefinable B v) (k : EulerKind) :
    GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
      (GammaIndicators.indicatorFamily B (C.gammaDomain v)
        (C.gamma_shaped_of_validity U E T hU hE hT B v
          (C.gamma_definable_of_raw U E T hU hE B v hvalid hraw) hvalid).definable) =
      C.shape.eulerValue k :=
  shaped_cell_euler_value h00 hκ hs B hr hγ k
    (C.gamma_shaped_of_validity U E T hU hE hT B v
      (C.gamma_definable_of_raw U E T hU hE B v hvalid hraw) hvalid)

end DiamondIntegral.Section5
