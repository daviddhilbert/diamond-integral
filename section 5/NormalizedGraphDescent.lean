import «section 5».FiniteFrameCompatibility

/-! Equivariant bijection graphs descend with one common root. This is a
set-level graph theorem, prior to the original-language definability adapter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical
variable {n m : ℕ} (N : ℕ+) (a : Fin n → ℤ) (b : Fin m → ℤ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : FiniteInvariant N a X) (hY : FiniteInvariant N b Y) (e : X ≃ Y)

def framedEquivGraph : Set (Fin (n + m) → ℂ) :=
  {z | ∃ x : X, (fun i => z (Fin.castAdd m i)) = x.val ∧
    (fun j => z (Fin.natAdd n j)) = (e x).val}

theorem framedEquivGraph_invariant
    (he : ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) (x : X),
      (e ⟨weightedAction a ζ.val x.val, (hX ζ x.val).mpr x.property⟩).val =
        weightedAction b ζ.val (e x).val) :
    FiniteInvariant N (Fin.append a b) (framedEquivGraph X Y e) := by
  have hclosed (ζ : rootsOfUnity (N : ℕ) ℂ) (z : Fin (n + m) → ℂ)
      (hz : z ∈ framedEquivGraph X Y e) :
      weightedAction (Fin.append a b) ζ.val z ∈ framedEquivGraph X Y e := by
    obtain ⟨x, hx, hy⟩ := hz
    refine ⟨⟨weightedAction a ζ.val x.val, (hX ζ x.val).mpr x.property⟩, ?_, ?_⟩
    · have hl : (fun i => weightedAction (Fin.append a b) ζ.val z (Fin.castAdd m i)) =
          weightedAction a ζ.val (fun i => z (Fin.castAdd m i)) := by
        funext i
        simp [weightedAction]
      rw [hl, hx]
    · have hr : (fun j => weightedAction (Fin.append a b) ζ.val z (Fin.natAdd n j)) =
          weightedAction b ζ.val (fun j => z (Fin.natAdd n j)) := by
        funext j
        simp [weightedAction]
      rw [hr, hy]
      exact (he ζ x).symm
  intro ζ z
  constructor
  · intro hz
    have hh := hclosed ζ⁻¹ _ hz
    have hi : weightedAction (Fin.append a b) (ζ⁻¹).val
        (weightedAction (Fin.append a b) ζ.val z) = z := by
      rw [← weightedAction_mul]
      change weightedAction (Fin.append a b) (ζ.val⁻¹ * ζ.val) z = z
      rw [inv_mul_cancel, weightedAction_one]
    exact hi ▸ hh
  · exact hclosed ζ z

theorem framedEquivGraph_append_mem (x : X) (y : Y) :
    Fin.append x.val y.val ∈ framedEquivGraph X Y e ↔ e x = y := by
  constructor
  · rintro ⟨x', hx, hy⟩
    have hx' : x = x' := Subtype.ext (by simpa only [Fin.append_left] using hx)
    have hy' : y.val = (e x').val := by simpa only [Fin.append_right] using hy
    exact (congrArg e hx').trans (Subtype.ext hy').symm
  · intro he
    refine ⟨x, ?_, ?_⟩
    · simp
    · simpa only [Fin.append_right] using congrArg Subtype.val he.symm

theorem normalized_descended_graph
    (hiG : FiniteInvariant N (Fin.append a b) (framedEquivGraph X Y e))
    (u : descendSet N a X) (v : descendSet N b Y) :
    Fin.append u.val v.val ∈ descendSet N (Fin.append a b) (framedEquivGraph X Y e) ↔
      descendedBijection N a b X Y hX hY e u = v := by
  let E := descentEquiv N a X hX
  let F := descentEquiv N b Y hY
  let x : X := E.symm u
  let y : Y := F.symm v
  have hu : finiteFrame N a x.val = u.val := congrArg Subtype.val (E.apply_symm_apply u)
  have hv : finiteFrame N b y.val = v.val := congrArg Subtype.val (F.apply_symm_apply v)
  have hm : Fin.append u.val v.val ∈ descendSet N (Fin.append a b) (framedEquivGraph X Y e) ↔
      e x = y := by
    rw [← hu, ← hv, ← finiteFrame_append]
    rw [descendSet_eq_image N (Fin.append a b) _ hiG]
    constructor
    · rintro ⟨z, hz, hez⟩
      have hz' : z = Fin.append x.val y.val := finiteFrame_injective N (Fin.append a b) hez
      exact (framedEquivGraph_append_mem X Y e x y).mp (hz' ▸ hz)
    · intro he
      exact ⟨_, (framedEquivGraph_append_mem X Y e x y).mpr he, rfl⟩
  rw [hm]
  constructor
  · intro h
    change F (e x) = v
    rw [h]
    exact F.apply_symm_apply v
  · intro h
    have hh := congrArg F.symm h
    change F.symm (F (e x)) = y at hh
    rwa [F.symm_apply_apply] at hh

end DiamondIntegral.Section5.PuiseuxOriginal
