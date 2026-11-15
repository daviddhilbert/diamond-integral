import «section 5».FiniteFrameComparison

/-! Root changes, common-level inflation, and products in the finite
comparison. These are actual coordinate identities before passing to rings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical

theorem finiteFrame_inflate {n : ℕ} (N d : ℕ+) (a : Fin n → ℤ) (x : Fin n → ℂ) :
    finiteFrame (N * d) (fun i => (d : ℤ) * a i) x = finiteFrame N a x := by
  funext i
  apply congrArg (fun q => linePoint q (x i))
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
  push_cast
  field_simp

def rootLevelMap (N d : ℕ+) : rootsOfUnity ((N * d : ℕ+) : ℕ) ℂ →*
    rootsOfUnity (N : ℕ) ℂ where
  toFun ζ := ⟨ζ.val ^ (d : ℕ), by
    rw [mem_rootsOfUnity]
    rw [← pow_mul, Nat.mul_comm (d : ℕ)]
    exact (mem_rootsOfUnity _ ζ.val).mp ζ.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' ζ ξ := by
    apply Subtype.ext
    change (ζ.val * ξ.val) ^ (d : ℕ) = ζ.val ^ (d : ℕ) * ξ.val ^ (d : ℕ)
    exact mul_pow _ _ _

theorem weightedAction_inflate {n : ℕ} (N d : ℕ+) (a : Fin n → ℤ)
    (ζ : rootsOfUnity ((N * d : ℕ+) : ℕ) ℂ) (x : Fin n → ℂ) :
    weightedAction (fun i => (d : ℤ) * a i) ζ.val x =
      weightedAction a (rootLevelMap N d ζ).val x := by
  funext i
  change ((ζ.val ^ ((d : ℤ) * a i) : ℂˣ) : ℂ) * x i =
    (((ζ.val ^ (d : ℕ)) ^ a i : ℂˣ) : ℂ) * x i
  rw [zpow_mul, zpow_natCast]

theorem frameAtRoot_change {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (r s : KummerRVRoot N) (x : Fin n → ℂ) :
    frameAtRoot N a s x = frameAtRoot N a r
      (weightedAction a ((rootPhase N s / rootPhase N r).val) x) := by
  change finiteFrame N a (weightedAction a s.val.2 x) =
    finiteFrame N a (weightedAction a r.val.2 (weightedAction a (s.val.2 / r.val.2) x))
  rw [← weightedAction_mul]
  congr 2
  exact (mul_div_cancel _ _).symm

theorem finiteFrame_append {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℂ) (y : Fin m → ℂ) :
    finiteFrame N (Fin.append a b) (Fin.append x y) =
      Fin.append (finiteFrame N a x) (finiteFrame N b y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [finiteFrame]

theorem weightedAction_append {n m : ℕ} (a : Fin n → ℤ) (b : Fin m → ℤ) (ζ : ℂˣ)
    (x : Fin n → ℂ) (y : Fin m → ℂ) :
    weightedAction (Fin.append a b) ζ (Fin.append x y) =
      Fin.append (weightedAction a ζ x) (weightedAction b ζ y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [weightedAction]

theorem frameAtRoot_append {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (r : KummerRVRoot N) (x : Fin n → ℂ) (y : Fin m → ℂ) :
    frameAtRoot N (Fin.append a b) r (Fin.append x y) =
      Fin.append (frameAtRoot N a r x) (frameAtRoot N b r y) := by
  rw [frameAtRoot, weightedAction_append, finiteFrame_append]
  rfl

def tupleProductSet {K : Type*} {n m : ℕ} (X : Set (Fin n → K)) (Y : Set (Fin m → K)) :
    Set (Fin (n + m) → K) :=
  {z | (fun i => z (Fin.castAdd m i)) ∈ X ∧ (fun j => z (Fin.natAdd n j)) ∈ Y}

theorem tupleProductSet_invariant {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : FiniteInvariant N a X) (hY : FiniteInvariant N b Y) :
    FiniteInvariant N (Fin.append a b) (tupleProductSet X Y) := by
  intro ζ z
  have hx : weightedAction a ζ.val (fun i => z (Fin.castAdd m i)) ∈ X ↔
      (fun i => z (Fin.castAdd m i)) ∈ X := hX ζ _
  have hy : weightedAction b ζ.val (fun j => z (Fin.natAdd n j)) ∈ Y ↔
      (fun j => z (Fin.natAdd n j)) ∈ Y := hY ζ _
  change (fun i => ((ζ.val ^ a i : ℂˣ) : ℂ) * z (Fin.castAdd m i)) ∈ X ↔ _ at hx
  change (fun j => ((ζ.val ^ b j : ℂˣ) : ℂ) * z (Fin.natAdd n j)) ∈ Y ↔ _ at hy
  simpa only [tupleProductSet, Set.mem_ofPred_eq, weightedAction,
    Fin.append_left, Fin.append_right] using and_congr hx hy

end DiamondIntegral.Section5.PuiseuxOriginal
