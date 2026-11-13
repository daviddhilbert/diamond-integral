import «section 4».GammaIntegerFamilies

/-! Actual unary-coordinate integration of finite-range definable integer
families. The output remains definable over the original base. Its value
is the Euler integral of the actual weighted fibre, not a formal symbol.
Coordinate-order independence is a later Fubini obligation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaWeightedFamilies
open GammaOrderLogic GammaDefinableEuler GammaEulerSets GammaFamilyEuler
open GammaFamilyIntegration GammaIntegerFamilies EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_fibreFunction (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) :
    ∃ F : EulerFunction k (PaperGamma (M := M)), ∀ x : Values.Gamma (M := M),
      F (toPaperGamma x) = f (Fin.cons x y) := by
  let B' := GammaBaseExtension.withGamma B (Set.range y)
  let g : PaperGamma (M := M) → ℤ := fun x => f (Fin.cons (toPaperGamma.symm x) y)
  have hgr : (Set.range g).Finite := hf.1.subset
    (by rintro _ ⟨x, rfl⟩; exact ⟨Fin.cons (toPaperGamma.symm x) y, rfl⟩)
  have hgd (m : ℤ) : GammaDefinableOverBase B' {x | g (toPaperGamma x) = m} :=
    GammaFamilySlices.slice_definable_base B {z | f z = m} (hf.2 m) y
  obtain ⟨F, hF⟩ := exists_eulerFunction_of_definable h00 B' k g hgr hgd
  exact ⟨F, fun x => hF (toPaperGamma x)⟩

def fibreFunction (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) : EulerFunction k (PaperGamma (M := M)) :=
  Classical.choose (exists_fibreFunction h00 B k f hf y)

theorem fibreFunction_eval (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) (x : Values.Gamma (M := M)) :
    fibreFunction h00 B k f hf y (toPaperGamma x) = f (Fin.cons x y) :=
  Classical.choose_spec (exists_fibreFunction h00 B k f hf y) x

def integralFirst (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) : ℤ := totalEuler k (fibreFunction h00 B k f hf y)

theorem integralFirst_levelSum (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) :
    integralFirst h00 B k f hf y =
      ∑ m ∈ hf.1.toFinset, m * fibreEuler h00 B k {z | f z = m} (hf.2 m) y := by
  let B' := GammaBaseExtension.withGamma B (Set.range y)
  let D (m : ℤ) : Set (Values.Gamma (M := M)) := {x | f (Fin.cons x y) = m}
  have hD (m : ℤ) : GammaDefinableOverBase B' (D m) :=
    GammaFamilySlices.slice_definable_base B {z | f z = m} (hf.2 m) y
  let I (m : ℤ) := indicator h00 B' k (D m) (hD m)
  have he : (∑ m ∈ hf.1.toFinset, m • I m) = fibreFunction h00 B k f hf y := by
    apply eval_injective k
    funext x
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    change (∑ m ∈ hf.1.toFinset, m • I m) (toPaperGamma γ) =
      fibreFunction h00 B k f hf y (toPaperGamma γ)
    simp only [eval_finsetSum, eval_zsmul, I, indicator_eval, fibreFunction_eval]
    simp only [D, Set.mem_ofPred_eq, zsmul_eq_mul, Int.cast_id, mul_ite, mul_one, mul_zero]
    simp_rw [eq_comm (a := f (Fin.cons γ y))]
    rw [Finset.sum_ite_eq']
    exact ite_eq_left (hf.1.mem_toFinset.mpr ⟨Fin.cons γ y, rfl⟩)
  change totalEuler k (fibreFunction h00 B k f hf y) = _
  rw [← he, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_zsmul]
  change m • fibreEuler h00 B k {z | f z = m} (hf.2 m) y = _
  simp only [zsmul_eq_mul, Int.cast_id]

theorem integralFirst_definable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    IntegerFamilyDefinable B (integralFirst h00 B k f hf) := by
  have h := finsetSum_definable B hf.1.toFinset
    (fun m y => m * fibreEuler h00 B k {z | f z = m} (hf.2 m) y)
    (fun m _ => map_definable B _ (fibreEuler_integerFamilyDefinable h00 hκ hs B hr hγ k
      {z | f z = m} (hf.2 m)) (fun v => m * v))
  convert h using 1
  funext y
  exact integralFirst_levelSum h00 B k f hf y

theorem integralFirst_zero (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) (n : ℕ)
    (y : Fin n → Values.Gamma (M := M)) :
    integralFirst h00 B k (fun _ : Fin (n + 1) → Values.Gamma (M := M) => 0)
      (const_definable B (n + 1) 0) y = 0 := by
  have he : fibreFunction h00 B k (fun _ : Fin (n + 1) → Values.Gamma (M := M) => 0)
      (const_definable B (n + 1) 0) y = 0 := by
    apply eval_injective k
    funext x
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    change fibreFunction h00 B k _ _ y (toPaperGamma γ) = (0 : EulerFunction k (PaperGamma (M := M))) (toPaperGamma γ)
    rw [fibreFunction_eval, eval_zero]
  rw [integralFirst, he, map_zero]

theorem integralFirst_add (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f g : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (hf : IntegerFamilyDefinable B f) (hg : IntegerFamilyDefinable B g)
    (y : Fin n → Values.Gamma (M := M)) :
    integralFirst h00 B k (fun z => f z + g z) (add_definable B f g hf hg) y =
      integralFirst h00 B k f hf y + integralFirst h00 B k g hg y := by
  have he : fibreFunction h00 B k (fun z => f z + g z) (add_definable B f g hf hg) y =
      fibreFunction h00 B k f hf y + fibreFunction h00 B k g hg y := by
    apply eval_injective k
    funext x
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    change fibreFunction h00 B k _ _ y (toPaperGamma γ) =
      (fibreFunction h00 B k f hf y + fibreFunction h00 B k g hg y) (toPaperGamma γ)
    simp only [fibreFunction_eval, eval_add]
  rw [integralFirst, he, map_add]
  rfl

def integrateFirst (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) : familySubgroup B (n + 1) →+ familySubgroup B n where
  toFun f := ⟨integralFirst h00 B k f.val f.property,
    integralFirst_definable h00 hκ hs B hr hγ k f.val f.property⟩
  map_zero' := by
    apply Subtype.ext
    funext y
    exact integralFirst_zero h00 B k n y
  map_add' f g := by
    apply Subtype.ext
    funext y
    exact integralFirst_add h00 B k f.val g.val f.property g.property y

end DiamondIntegral.Section4.GammaWeightedFamilies
