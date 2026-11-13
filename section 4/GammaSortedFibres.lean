import «section 4».GammaTupleCounting
import «section 4».FiniteOrderRanks

/-! Canonical ordered points of finite Gamma fibres. The kth graph is
defined by membership and counting exactly k smaller points, over the
original base. No RV representatives or new parameters are chosen. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaSortedFibres
open GammaOrderLogic GammaRelationLogic GammaTupleCounting FiniteOrderRanks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def lowerRelation {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) :
    Set (Fin (n + 2) → Values.Gamma (M := M)) :=
  {z | Fin.cons (z 0) (fun j => z j.succ.succ) ∈ R ∧ z 0 < z (0 : Fin (n + 1)).succ}

theorem lowerRelation_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R) :
    GammaDefinable B (lowerRelation R) := by
  let π : Fin (n + 1) → Fin (n + 2) := Fin.cases 0 (fun j => j.succ.succ)
  have h := preimage_definable_base B R hR π
  have hR' : GammaDefinable B {z : Fin (n + 2) → Values.Gamma (M := M) |
      Fin.cons (z 0) (fun j => z j.succ.succ) ∈ R} := by
    convert h using 1
    ext z
    have he : z ∘ π = (Fin.cons (z 0) (fun j => z j.succ.succ) :
        Fin (n + 1) → Values.Gamma (M := M)) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    change (Fin.cons (z 0) (fun j => z j.succ.succ) ∈ R) ↔ z ∘ π ∈ R
    rw [he]
  have hlt : GammaDefinable B {z : Fin (n + 2) → Values.Gamma (M := M) |
      z 0 < z (0 : Fin (n + 1)).succ} := by
    simpa only [GammaOrderLogic.Formula.Realize] using
      GammaOrderLogic.formula_definable_base B (fun a : Empty => nomatch a) (fun a => nomatch a)
        (.lt (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ)
  exact inter_definable_base B _ _ hR' hlt

def RankGraph {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (k : ℕ) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) :=
  {z | z ∈ R ∧ setRank {x | Fin.cons x (fun j => z j.succ) ∈ R} (z 0) = k}

theorem rankGraph_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite) (k : ℕ) :
    GammaDefinable B (RankGraph R k) := by
  have h := inter_definable_base B R _ hR
    (exactly_definable_base B (lowerRelation R) (lowerRelation_definable B R hR) k)
  convert h using 1
  ext z
  change (z ∈ R ∧ setRank {x | Fin.cons x (fun j => z j.succ) ∈ R} (z 0) = k) ↔
    z ∈ R ∧ (AtLeast (lowerRelation R) k z ∧ ¬ AtLeast (lowerRelation R) (k + 1) z)
  rw [exactly_iff]
  have he : {x | Fin.cons x z ∈ lowerRelation R} =
      {x | Fin.cons x (fun j => z j.succ) ∈ R ∧ x < z 0} := by
    ext x
    rfl
  rw [he]
  have hfin : {x | Fin.cons x (fun j => z j.succ) ∈ R ∧ x < z 0}.Finite :=
    (hf (fun j => z j.succ)).subset (fun _ h => h.1)
  simp only [setRank, Set.mem_ofPred_eq, hfin, true_and]

def point {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite)
    (k : ℕ) (y : Fin n → Values.Gamma (M := M)) (hk : k < {x | Fin.cons x y ∈ R}.ncard) :
    Values.Gamma (M := M) := Classical.choose (exists_unique_setRank _ (hf y) k hk)

theorem point_spec {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite)
    (k : ℕ) (y : Fin n → Values.Gamma (M := M)) (hk : k < {x | Fin.cons x y ∈ R}.ncard) :
    Fin.cons (point R hf k y hk) y ∈ R ∧ setRank {x | Fin.cons x y ∈ R} (point R hf k y hk) = k :=
  (Classical.choose_spec (exists_unique_setRank _ (hf y) k hk)).1

def pointMap {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite)
    (k : ℕ) (y : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  if hk : k < {x | Fin.cons x y ∈ R}.ncard then point R hf k y hk else 1

theorem pointMap_graph_eq {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite) (k : ℕ) :
    {z : Fin (n + 1) → Values.Gamma (M := M) |
      AtLeast R (k + 1) (fun j => z j.succ) ∧ pointMap R hf k (fun j => z j.succ) = z 0} =
      RankGraph R k := by
  ext z
  let y := fun j : Fin n => z j.succ
  have hez : Fin.cons (z 0) y = z := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  change (AtLeast R (k + 1) y ∧ pointMap R hf k y = z 0) ↔
    z ∈ R ∧ setRank {x | Fin.cons x y ∈ R} (z 0) = k
  constructor
  · rintro ⟨hd, he⟩
    have hk := (atLeast_succ_iff R k y (hf y)).mp hd
    have hs := point_spec R hf k y hk
    have hp : point R hf k y hk = z 0 := by simpa only [pointMap, dite_eq_left hk] using he
    rw [hp] at hs
    exact ⟨hez ▸ hs.1, hs.2⟩
  · rintro ⟨hzR, hrank⟩
    have hxR : Fin.cons (z 0) y ∈ R := hez.symm ▸ hzR
    have hk : k < {x | Fin.cons x y ∈ R}.ncard :=
      hrank ▸ setRank_lt_ncard _ (hf y) (z 0) hxR
    refine ⟨(atLeast_succ_iff R k y (hf y)).mpr hk, ?_⟩
    rw [pointMap, dite_eq_left hk]
    exact (exists_unique_setRank _ (hf y) k hk).unique (point_spec R hf k y hk) ⟨hxR, hrank⟩

theorem pointMap_graph_definable (B : Base (M := M)) {n : ℕ}
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite) (k : ℕ) :
    GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      AtLeast R (k + 1) (fun j => z j.succ) ∧ pointMap R hf k (fun j => z j.succ) = z 0} := by
  rw [pointMap_graph_eq]
  exact rankGraph_definable B R hR hf k

end DiamondIntegral.Section4.GammaSortedFibres
