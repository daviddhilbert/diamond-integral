import «section 4».GammaRelationLogic
import «section 4».GammaGroupNames

/-! Actual Gamma-valued map graphs over the original base. Algebraic
operations are implemented through full proper RV-code relations and
Gamma quantifiers, without a fictitious LRV structure on Gamma itself. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaDefinableMaps
open GammaOrderLogic GammaGroupNames

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def MapDefinable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : Prop :=
  GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = f (fun i => z i.succ)}

theorem eq_definable_base (B : Base (M := M)) {n : ℕ} (i j : Fin n) :
    GammaDefinable B {z : Fin n → Values.Gamma (M := M) | z i = z j} := by
  have h := formula_definable_base B (fun a : Empty => nomatch a) (fun a => nomatch a)
    (.and (.not (.lt i j)) (.not (.lt j i)))
  have he : {z : Fin n → Values.Gamma (M := M) | z i = z j} =
      {z | Formula.Realize (fun a : Empty => nomatch a)
        (.and (.not (.lt i j)) (.not (.lt j i))) z} := by
    ext z
    change z i = z j ↔ ¬ z i < z j ∧ ¬ z j < z i
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      exact le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1)
  rwa [he]

theorem projection_definable (B : Base (M := M)) {n : ℕ} (i : Fin n) :
    MapDefinable B (fun z : Fin n → Values.Gamma (M := M) => z i) :=
  eq_definable_base B 0 i.succ

theorem constant_definable (B : Base (M := M)) {n : ℕ} (c : Values.Gamma (M := M))
    (hc : GammaDefinableClosureAtBase B c) :
    MapDefinable B (fun _ : Fin n → Values.Gamma (M := M) => c) :=
  GammaRelationLogic.preimage_definable_base B _ ((unary_definable_iff B {c}).mpr hc)
    (fun _ : Fin 1 => (0 : Fin (n + 1)))

theorem reindex_definable (B : Base (M := M)) {n m : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (π : Fin n → Fin m) : MapDefinable B (fun z => f (z ∘ π)) := by
  let σ : Fin (n + 1) → Fin (m + 1) := Fin.cases 0 (fun i => (π i).succ)
  have h := GammaRelationLogic.preimage_definable_base B _ hf σ
  unfold MapDefinable
  convert h using 1
  ext z
  rfl

theorem mul_definable (B : Base (M := M)) {n : ℕ}
    (f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : MapDefinable B f) (hg : MapDefinable B g) :
    MapDefinable B (fun x => f x * g x) := by
  let πf : Fin (n + 1) → Fin (n + 3) := Fin.cases 0 (fun i => i.succ.succ.succ)
  let πg : Fin (n + 1) → Fin (n + 3) := Fin.cases 1 (fun i => i.succ.succ.succ)
  have hF := GammaRelationLogic.preimage_definable_base B _ hf πf
  have hG := GammaRelationLogic.preimage_definable_base B _ hg πg
  have hM := GammaRelationLogic.preimage_definable_base B _ (mul_graph_definable_base B)
    (![0, 1, 2] : Fin 3 → Fin (n + 3))
  have hP : GammaDefinable B {z : Fin (n + 3) → Values.Gamma (M := M) |
      (z 0 = f (fun i => z i.succ.succ.succ) ∧ z 1 = g (fun i => z i.succ.succ.succ)) ∧
        z 0 * z 1 = z 2} :=
    GammaRelationLogic.inter_definable_base B _ _
      (GammaRelationLogic.inter_definable_base B _ _ hF hG) hM
  have hQ := GammaRelationLogic.exists_definable_base B _
    (GammaRelationLogic.exists_definable_base B _ hP)
  change GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
    ∃ b a, (a = f (fun i => z i.succ) ∧ b = g (fun i => z i.succ)) ∧ a * b = z 0} at hQ
  have he : {z : Fin (n + 1) → Values.Gamma (M := M) |
      ∃ b a, (a = f (fun i => z i.succ) ∧ b = g (fun i => z i.succ)) ∧ a * b = z 0} =
      {z | z 0 = f (fun i => z i.succ) * g (fun i => z i.succ)} := by
    ext z
    constructor
    · rintro ⟨b, a, ⟨ha, hb⟩, hm⟩
      rw [ha, hb] at hm
      exact hm.symm
    · intro h
      exact ⟨g (fun i => z i.succ), f (fun i => z i.succ), ⟨rfl, rfl⟩, h.symm⟩
  unfold MapDefinable
  rwa [he] at hQ

theorem nat_power_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (m : ℕ) : MapDefinable B (fun x => f x ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using constant_definable (n := n) B 1 (one_definable_base B)
  | succ m ih => simpa only [pow_succ] using mul_definable B _ _ ih hf

theorem inverse_graph_definable (B : Base (M := M)) :
    GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 * z 1 = 1} := by
  have hM := GammaRelationLogic.preimage_definable_base B _ (mul_graph_definable_base B)
    (![1, 2, 0] : Fin 3 → Fin 3)
  have hO := GammaRelationLogic.preimage_definable_base B _
    ((unary_definable_iff B {1}).mpr (one_definable_base B)) (fun _ : Fin 1 => (0 : Fin 3))
  have hQ := GammaRelationLogic.exists_definable_base B _
    (GammaRelationLogic.inter_definable_base B _ _ hM hO)
  change GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) |
    ∃ u, z 0 * z 1 = u ∧ u = 1} at hQ
  have he : {z : Fin 2 → Values.Gamma (M := M) | ∃ u, z 0 * z 1 = u ∧ u = 1} =
      {z | z 0 * z 1 = 1} := by
    ext z
    simp
  rwa [he] at hQ

theorem inverse_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f) :
    MapDefinable B (fun x => (f x)⁻¹) := by
  let πf : Fin (n + 1) → Fin (n + 2) := Fin.cases 0 (fun i => i.succ.succ)
  have hF := GammaRelationLogic.preimage_definable_base B _ hf πf
  have hI := GammaRelationLogic.preimage_definable_base B _ (inverse_graph_definable B)
    (![0, 1] : Fin 2 → Fin (n + 2))
  have hQ := GammaRelationLogic.exists_definable_base B _
    (GammaRelationLogic.inter_definable_base B _ _ hF hI)
  change GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
    ∃ a, a = f (fun i => z i.succ) ∧ a * z 0 = 1} at hQ
  have he : {z : Fin (n + 1) → Values.Gamma (M := M) |
      ∃ a, a = f (fun i => z i.succ) ∧ a * z 0 = 1} =
      {z | z 0 = (f (fun i => z i.succ))⁻¹} := by
    ext z
    constructor
    · rintro ⟨a, ha, hm⟩
      rw [ha] at hm
      apply mul_left_cancel (a := f (fun i => z i.succ))
      rw [hm, mul_inv_cancel]
    · intro h
      exact ⟨f (fun i => z i.succ), rfl, by rw [h, mul_inv_cancel]⟩
  unfold MapDefinable
  rwa [he] at hQ

theorem int_power_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (m : ℤ) : MapDefinable B (fun x => f x ^ m) := by
  cases m with
  | ofNat m =>
    change MapDefinable B (fun x => f x ^ (m : ℤ))
    simpa only [zpow_natCast] using nat_power_definable B f hf m
  | negSucc m =>
    simpa only [zpow_negSucc] using inverse_definable B _ (nat_power_definable B f hf (m + 1))

theorem equal_maps_definable (B : Base (M := M)) {n : ℕ}
    (f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : MapDefinable B f) (hg : MapDefinable B g) : GammaDefinable B {x | f x = g x} := by
  have hQ := GammaRelationLogic.exists_definable_base B _
    (GammaRelationLogic.inter_definable_base B _ _ hf hg)
  change GammaDefinable B {z : Fin n → Values.Gamma (M := M) | ∃ a, a = f z ∧ a = g z} at hQ
  have he : {z : Fin n → Values.Gamma (M := M) | ∃ a, a = f z ∧ a = g z} = {z | f z = g z} := by
    ext z
    constructor
    · rintro ⟨a, hf, hg⟩
      exact hf.symm.trans hg
    · intro h
      exact ⟨f z, rfl, h⟩
  rwa [he] at hQ

theorem root_definable (B : Base (M := M)) {n : ℕ}
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : MapDefinable B f)
    (q : ℕ) (hq : q ≠ 0) : MapDefinable B (fun x => RootableBy.root (f x) q) := by
  have hL := nat_power_definable B _ (projection_definable B (0 : Fin (n + 1))) q
  have hR := reindex_definable B f hf (fun i : Fin n => i.succ)
  have hE := equal_maps_definable B _ _ hL hR
  change GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
    z 0 ^ q = f (fun i => z i.succ)} at hE
  have he : {z : Fin (n + 1) → Values.Gamma (M := M) |
      z 0 ^ q = f (fun i => z i.succ)} =
      {z | z 0 = RootableBy.root (f (fun i => z i.succ)) q} := by
    ext z
    change (z 0 ^ q = f (fun i => z i.succ)) ↔
      z 0 = RootableBy.root (f (fun i => z i.succ)) q
    constructor
    · intro h
      apply HasUniqueRoots.pow_left_injective hq
      change z 0 ^ q = RootableBy.root (f (fun i => z i.succ)) q ^ q
      rw [RootableBy.root_cancel _ hq]
      exact h
    · intro h
      rw [h, RootableBy.root_cancel _ hq]
  unfold MapDefinable
  rwa [he] at hE

end DiamondIntegral.Section4.GammaDefinableMaps
