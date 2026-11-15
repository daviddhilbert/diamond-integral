import «section 5».FiniteKummerFrames

/-! The existential-root construction and its independence of roots, both for
sets and for graphs. Kummer roots are actual normalized RV units. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical

def KummerRVRoot (N : ℕ+) :=
  {r : RationalRVUnits ℂ // r ^ (N : ℕ) = (Multiplicative.ofAdd (1 : ℚ), 1)}

def rootOfPhase (N : ℕ+) (ζ : rootsOfUnity (N : ℕ) ℂ) : KummerRVRoot N :=
  ⟨(Multiplicative.ofAdd ((1 : ℚ) / (N : ℕ)), ζ.val), by
    apply Prod.ext
    · apply congrArg Multiplicative.ofAdd
      change (N : ℚ) * (1 / (N : ℕ)) = 1
      exact mul_one_div_cancel (by exact_mod_cast N.ne_zero)
    · apply Units.ext
      exact (mem_rootsOfUnity' (N : ℕ) ζ.val).mp ζ.property⟩

theorem kummerRVRoot_value (N : ℕ+) (r : KummerRVRoot N) :
    r.val.1 = Multiplicative.ofAdd ((1 : ℚ) / (N : ℕ)) := by
  have h := congrArg (fun u : RationalRVUnits ℂ => u.1.toAdd) r.property
  change (N : ℚ) * r.val.1.toAdd = 1 at h
  apply congrArg Multiplicative.ofAdd
  change r.val.1.toAdd = 1 / (N : ℕ)
  apply (eq_div_iff (by exact_mod_cast N.ne_zero)).mpr
  simpa only [mul_comm] using h

def rootPhase (N : ℕ+) (r : KummerRVRoot N) : rootsOfUnity (N : ℕ) ℂ :=
  ⟨r.val.2, (mem_rootsOfUnity' (N : ℕ) r.val.2).mpr
    (congrArg (fun u : RationalRVUnits ℂ => (u.2 : ℂ)) r.property)⟩

def kummerRootEquiv (N : ℕ+) : rootsOfUnity (N : ℕ) ℂ ≃ KummerRVRoot N where
  toFun := rootOfPhase N
  invFun := rootPhase N
  left_inv _ := rfl
  right_inv r := by
    apply Subtype.ext
    exact Prod.ext (kummerRVRoot_value N r).symm rfl

def frameAtRoot {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (r : KummerRVRoot N)
    (x : Fin n → ℂ) : Fin n → RV :=
  finiteFrame N a (weightedAction a r.val.2 x)

/-- All auxiliary roots occur in this existential; none is added to the base. -/
def descendSet {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (X : Set (Fin n → ℂ)) :
    Set (Fin n → RV) := {u | ∃ r : KummerRVRoot N, ∃ x ∈ X, u = frameAtRoot N a r x}

def FiniteInvariant {n : ℕ} (N : ℕ+) (a : Fin n → ℤ) (X : Set (Fin n → ℂ)) : Prop :=
  ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) (x : Fin n → ℂ), weightedAction a ζ.val x ∈ X ↔ x ∈ X

theorem descendSet_eq_image {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : FiniteInvariant N a X) :
    descendSet N a X = finiteFrame N a '' X := by
  ext u
  constructor
  · rintro ⟨r, x, hx, rfl⟩
    exact ⟨weightedAction a r.val.2 x, (hX (rootPhase N r) x).mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨rootOfPhase N 1, x, hx, ?_⟩
    simp only [frameAtRoot, rootOfPhase, OneMemClass.coe_one, weightedAction_one]

theorem frame_mem_descendSet {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : FiniteInvariant N a X) (r : KummerRVRoot N)
    (x : Fin n → ℂ) : frameAtRoot N a r x ∈ descendSet N a X ↔ x ∈ X := by
  rw [descendSet_eq_image N a X hX]
  change finiteFrame N a (weightedAction a r.val.2 x) ∈ finiteFrame N a '' X ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    exact (hX (rootPhase N r) x).mp ((finiteFrame_injective N a he) ▸ hy)
  · intro hx
    exact ⟨_, (hX (rootPhase N r) x).mpr hx, rfl⟩

def descentEquiv {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) (hX : FiniteInvariant N a X) :
    X ≃ descendSet N a X :=
  _root_.Equiv.ofBijective
    (fun x => ⟨finiteFrame N a x.val, by
      rw [descendSet_eq_image N a X hX]
      exact ⟨x.val, x.property, rfl⟩⟩)
    ⟨(fun x y h => Subtype.ext (finiteFrame_injective N a (congrArg Subtype.val h))), by
      intro u
      have hu := (Set.ext_iff.mp (descendSet_eq_image N a X hX) u.val).mp u.property
      obtain ⟨x, hx, he⟩ := hu
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

def descendedBijection {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : FiniteInvariant N a X) (hY : FiniteInvariant N b Y) (e : X ≃ Y) :
    descendSet N a X ≃ descendSet N b Y :=
  ((descentEquiv N a X hX).symm.trans e).trans (descentEquiv N b Y hY)

theorem descendedBijection_frame {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : FiniteInvariant N a X) (hY : FiniteInvariant N b Y) (e : X ≃ Y) (x : X) :
    descendedBijection N a b X Y hX hY e (descentEquiv N a X hX x) =
      descentEquiv N b Y hY (e x) := by
  change descentEquiv N b Y hY (e ((descentEquiv N a X hX).symm
    (descentEquiv N a X hX x))) = _
  rw [_root_.Equiv.symm_apply_apply]

local instance descentStructure : SpecialTransformations.Milestone0.LRV.Structure Carrier := canonicalInterpret

theorem framed_formula_finiteInvariant {m n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (φ : SpecialTransformations.Milestone0.LRV.BoundedFormula (Fin m) n)
    (v : Fin m → Carrier) (hv : ∀ i, baseCarrier (v i)) :
    FiniteInvariant N a {x | φ.Realize v (fun i => Sum.inr (finiteFrame N a x i))} := by
  intro ζ x
  exact framed_formula_invariant N a φ v hv ζ x

def descendGraph {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (G : Set ((Fin n → ℂ) × (Fin m → ℂ))) : Set ((Fin n → RV) × (Fin m → RV)) :=
  {uv | ∃ r : KummerRVRoot N, ∃ xy ∈ G,
    uv = (frameAtRoot N a r xy.1, frameAtRoot N b r xy.2)}

theorem descendGraph_eq_image {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (G : Set ((Fin n → ℂ) × (Fin m → ℂ)))
    (hG : ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) x y,
      (weightedAction a ζ.val x, weightedAction b ζ.val y) ∈ G ↔ (x, y) ∈ G) :
    descendGraph N a b G = (fun xy => (finiteFrame N a xy.1, finiteFrame N b xy.2)) '' G := by
  ext uv
  constructor
  · rintro ⟨r, xy, hxy, rfl⟩
    refine ⟨(weightedAction a r.val.2 xy.1, weightedAction b r.val.2 xy.2),
      (hG (rootPhase N r) xy.1 xy.2).mpr hxy, rfl⟩
  · rintro ⟨xy, hxy, rfl⟩
    refine ⟨rootOfPhase N 1, xy, hxy, ?_⟩
    simp only [frameAtRoot, rootOfPhase, OneMemClass.coe_one, weightedAction_one]

end DiamondIntegral.Section5.PuiseuxOriginal
