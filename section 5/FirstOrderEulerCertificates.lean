import «section 5».GammaCellTreeDecoding
import «section 5».FinitePartitionSyntax

/-! An Euler certificate is one finite syntax object. Its fixed validity
formula certifies a complete disjoint cylindrical decomposition, and its
syntactically computed integer equals the actual native Gamma integral. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic

structure EulerFormulaCertificate (L : Language) (P : Type*) (n : ℕ) where
  size : ℕ
  cells : Fin size → CylindricalFormulaTree L P n

def EulerFormulaCertificate.eulerValue {L : Language} {P : Type*} {n : ℕ}
    (C : EulerFormulaCertificate L P n) (k : EulerKind) : ℤ :=
  ∑ i, (C.cells i).shape.eulerValue k

def EulerFormulaCertificate.validity {L : Language} {P : Type*} {n : ℕ}
    (C : EulerFormulaCertificate L P n) (U : L.Formula (Fin 1)) (E T : L.Formula (Fin 2))
    (D : L.Formula (P ⊕ Fin n)) : L.Formula P :=
  finiteWitnessValidityFormula (fun i => (C.cells i).validity U E T) ⊓
    finitePartitionValidityFormula D (fun i => (C.cells i).domain)

theorem gamma_tuple_code_surjective {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
    {n : ℕ} (γ : Fin n → Values.Gamma (M := M)) :
    ∃ x : Fin n → M, (∀ i, NonzeroRV (x i)) ∧ codeValue ∘ x = γ := by
  choose x hx he using (fun i => EndpointLogic.codeValue_surjective (γ i))
  exact ⟨x, hx, funext he⟩

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem EulerFormulaCertificate.integral_eq {P : Type*} {n : ℕ}
    (C : EulerFormulaCertificate LRV P n)
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x, y] ↔ codeValue x < codeValue y))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (v : P → M) (D : LRV.Formula (P ⊕ Fin n))
    (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X)
    (hDX : ∀ x : Fin n → M, (∀ i, NonzeroRV (x i)) →
      (D.Realize (Sum.elim v x) ↔ codeValue ∘ x ∈ X))
    (hvalid : (C.validity U E T D).Realize v)
    (hraw : ∀ i, (C.cells i).rawDefinable B v) (k : EulerKind) :
    GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
      (GammaIndicators.indicatorFamily B X hX) = C.eulerValue k := by
  have hval := hvalid
  simp only [validity, Formula.realize_inf, finiteWitnessValidityFormula_realize] at hval
  have hcells := hval.1
  obtain ⟨hcover, hdisj⟩ := (finitePartitionValidityFormula_realize D (fun i => (C.cells i).domain) v).mp hval.2
  have hmem (i : Fin C.size) (x : Fin n → M) (hx : ∀ j, NonzeroRV (x j)) :
      (C.cells i).domain.Realize (Sum.elim v x) ↔ codeValue ∘ x ∈ (C.cells i).gammaDomain v := by
    have hh := quotientFormulaDomain_full_preimage U E (C.cells i).domain v NonzeroRV codeValue hU hE
      ((C.cells i).domainValidity U E T v (hcells i)) x
    exact hh.trans (and_iff_right hx)
  have hshape (i : Fin C.size) : ShapedGammaCell B n ((C.cells i).gammaDomain v) (C.cells i).shape :=
    (C.cells i).gamma_shaped_of_validity U E T hU hE hT B v
      ((C.cells i).gamma_definable_of_raw U E T hU hE B v (hcells i) (hraw i)) (hcells i)
  have hpartition : X = ⋃ i, (C.cells i).gammaDomain v := by
    ext γ
    obtain ⟨x, hx, hq⟩ := gamma_tuple_code_surjective γ
    have hh := hcover x
    rw [hDX x hx] at hh
    simp_rw [hmem _ x hx] at hh
    simpa only [hq, Set.mem_iUnion] using hh
  have hd : Pairwise (fun i j => Disjoint ((C.cells i).gammaDomain v) ((C.cells j).gammaDomain v)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro γ hi hj
    obtain ⟨x, hx, hq⟩ := gamma_tuple_code_surjective γ
    apply hdisj i j hij x
    exact ⟨(hmem i x hx).mpr (hq.symm ▸ hi), (hmem j x hx).mpr (hq.symm ▸ hj)⟩
  rw [GammaFinitePartitions.integral_partition h00 hκ hs B hr hγ k n X hX
    (fun i => (C.cells i).gammaDomain v) (fun i => (hshape i).definable) hd hpartition]
  exact Finset.sum_congr rfl (fun i _ => shaped_cell_euler_value h00 hκ hs B hr hγ k (hshape i))

end DiamondIntegral.Section5
