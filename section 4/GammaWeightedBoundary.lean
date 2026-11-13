import «section 4».GammaGermFamilies
import «section 4».GammaUniformFiniteFibres
import «section 4».GammaFiniteGraphPartition

/-! The intrinsic boundary of an integer-valued Gamma family, over the
original base. A finite level-set union defines local constancy; actual
finite-jump fibres and genuine saturation supply the uniform bound. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaWeightedBoundary
open GammaOrderLogic GammaDefinableEuler GammaFamilyIntegration GammaWeightedFamilies EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ConstantRegion {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) :=
  {z | z ∈ GammaFamilyBoundary.Interior {w | f w = f z}}

def Boundary {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) := (ConstantRegion f)ᶜ

theorem constantRegion_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    GammaDefinable B (ConstantRegion f) := by
  have h := GammaQuantifierLogic.finite_iUnion_definable_base B
    (fun m : hf.1.toFinset => {z | f z = m.val} ∩ GammaFamilyBoundary.Interior {w | f w = m.val})
    (fun m => GammaRelationLogic.inter_definable_base B _ _ (hf.2 m.val)
      (GammaFamilyBoundary.interior_definable_base B _ (hf.2 m.val)))
  convert h using 1
  ext z
  simp only [ConstantRegion, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hz
    exact ⟨⟨f z, hf.1.mem_toFinset.mpr ⟨z, rfl⟩⟩, rfl, hz⟩
  · rintro ⟨m, hm, hz⟩
    simpa only [hm] using hz

theorem boundary_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    GammaDefinable B (Boundary f) :=
  GammaRelationLogic.complement_definable_base B _ (constantRegion_definable B f hf)

theorem constantRegion_iff (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) :
    z ∈ ConstantRegion f ↔ ConstantNear
      (fibreFunction h00 B k f hf (fun j => z j.succ)) (toPaperGamma (z 0)) := by
  have hez : Fin.cons (z 0) (fun j => z j.succ) = z := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  change (∃ l u : Values.Gamma (M := M), l < z 0 ∧ z 0 < u ∧
      ∀ x, l < x → x < u → f (Fin.cons x (fun j => z j.succ)) = f z) ↔
    (∃ l u : Values.Gamma (M := M), l < z 0 ∧ z 0 < u ∧
      ∀ x, l < x → x < u →
        fibreFunction h00 B k f hf (fun j => z j.succ) (toPaperGamma x) =
          fibreFunction h00 B k f hf (fun j => z j.succ) (toPaperGamma (z 0)))
  simp only [fibreFunction_eval, hez]

theorem boundary_iff (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (z : Fin (n + 1) → Values.Gamma (M := M)) :
    z ∈ Boundary f ↔ ¬ ConstantNear
      (fibreFunction h00 B k f hf (fun j => z j.succ)) (toPaperGamma (z 0)) :=
  not_congr (constantRegion_iff h00 B k f hf z)

theorem finite_boundary_fibres (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) : {x | Fin.cons x y ∈ Boundary f}.Finite := by
  have h := (finite_breakpoints k (fibreFunction h00 B k f hf y)).preimage toPaperGamma.injective.injOn
  convert h using 1
  ext x
  exact boundary_iff h00 B k f hf (Fin.cons x y)

theorem exists_boundaryPartition (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    Nonempty (GammaFiniteGraphPartition.FiniteGraphPartition B (Boundary f)) := by
  have hR := boundary_definable B f hf
  have hfin := finite_boundary_fibres h00 B k f hf
  obtain ⟨N, hb⟩ := GammaUniformFiniteFibres.uniform_finite_bound hκ hs B hr hγ (Boundary f) hR hfin
  exact ⟨GammaFiniteGraphPartition.canonicalPartition B (Boundary f) hR hfin N hb⟩

end DiamondIntegral.Section4.GammaWeightedBoundary
