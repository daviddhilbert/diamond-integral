import «section 7».Lemma720Loc

/-! Lemma 7.20, step 12: the positioning map of the final cells, and the cells over
discs that respect the protected neighbourhood.

`epsHat` is `ε` off the protected neighbourhood `U`, and `ε(z, w)` on it, where `z` is
the closest point of `Q` (`zOf`). For a translated disc `D` in a label fibre `B_w` that
lies inside `U_w` or misses it, the cell over `D` with positioning `ε(·, w)` equals the
cell with positioning `epsHat(·, w)`, and `epsHat(·, w)` is constant on `D`, or
injective, disc-to-disc and rv-affine (`cell_of_disc`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace Final
variable (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
  (lead : Fin a) (Q : Finset (VF M))

/-- The closest point of `Q` to `x`, when there is a strictly closest one. -/
def zOf (x : VF M) : VF M :=
  if h : ∃ z ∈ Q, ∀ z' ∈ Q, z' ≠ z → vfValue (x - z') < vfValue (x - z) then h.choose else 0

/-- The positioning map of the final cells. -/
def epsHat (q : Mixed M 1 a) : VF M :=
  if q ∈ Protect.U B.carrier (εfun B ε) lead Q then εfun B ε (mkPoint (zOf Q (q.1 0)) q.2)
  else εfun B ε q

variable {B ε lead Q}

theorem zOf_eq (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {w : Fin a → RVInfinity M} {z x : VF M} (hz : z ∈ Q)
    (hx : x ∈ Protect.K B.carrier (εfun B ε) lead Q w z) : zOf Q x = z := by
  obtain ⟨β, hβ, hg⟩ := hx
  have hclosest : ∀ z' ∈ Q, z' ≠ z → vfValue (x - z') < vfValue (x - z) := by
    intro z' hz' hne
    have hsep : ¬ β.val < vfValue (z' - z) := hg.2 z' hz' hne
    rw [not_lt] at hsep
    have hlt : vfValue (z - z') < vfValue (x - z) := by
      rw [vfValue_sub_comm hv]
      exact lt_of_le_of_lt hsep hβ
    have he : x - z' = (z - z') + (x - z) := by ring
    rw [he, vfValue_add_eq_of_lt hv hlt]
    exact hlt
  have hex : ∃ z ∈ Q, ∀ z' ∈ Q, z' ≠ z → vfValue (x - z') < vfValue (x - z) := ⟨z, hz, hclosest⟩
  rw [zOf, dif_pos hex]
  obtain ⟨hzQ', hcl'⟩ := hex.choose_spec
  by_contra hne
  have h1 := hcl' z hz (Ne.symm hne)
  have h2 := hclosest _ hzQ' hne
  exact lt_asymm h1 h2

/-- **The cells over discs respecting the protected neighbourhood.** -/
theorem cell_of_disc (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (h00 : M ⊨ Axioms.ACVF00)
    (hgood : ∀ (w : Fin a → RVInfinity M) (c z : VF M) (hz : z ≠ 0),
        (∀ x ∈ tdisc c (rv M z), mkPoint x w ∈ B.carrier) → (∀ x ∈ tdisc c (rv M z), x ∉ Q) →
        (∀ x ∈ tdisc c (rv M z), ∀ x' ∈ tdisc c (rv M z), εfun B ε (mkPoint x w) = εfun B ε (mkPoint x' w)) ∨
        ∃ σ : RV M, Set.InjOn (fun x => εfun B ε (mkPoint x w)) (tdisc c (rv M z)) ∧
          DiscToDisc (tdisc c (rv M z)) (fun x => εfun B ε (mkPoint x w)) ∧
          HasSlope (tdisc c (rv M z)) (fun x => εfun B ε (mkPoint x w)) σ)
    (hloc : Protect.LocConst B.carrier (εfun B ε) lead)
    {w : Fin a → RVInfinity M} {c z₀ : VF M} (hz₀ : z₀ ≠ 0)
    (hDB : ∀ x ∈ tdisc c (rv M z₀), mkPoint x w ∈ B.carrier)
    (hpiece : (∀ x ∈ tdisc c (rv M z₀), mkPoint x w ∈ Protect.U B.carrier (εfun B ε) lead Q) ∨
      (∀ x ∈ tdisc c (rv M z₀), mkPoint x w ∉ Protect.U B.carrier (εfun B ε) lead Q))
    (hlead : w lead ≠ rvZero M) :
    cellOf (tdisc c (rv M z₀)) (fun x => εfun B ε (mkPoint x w)) (w lead) =
        cellOf (tdisc c (rv M z₀)) (fun x => epsHat B ε lead Q (mkPoint x w)) (w lead) ∧
      ((∀ x ∈ tdisc c (rv M z₀), ∀ x' ∈ tdisc c (rv M z₀),
          epsHat B ε lead Q (mkPoint x w) = epsHat B ε lead Q (mkPoint x' w)) ∨
        ∃ σ : RV M, Set.InjOn (fun x => epsHat B ε lead Q (mkPoint x w)) (tdisc c (rv M z₀)) ∧
          DiscToDisc (tdisc c (rv M z₀)) (fun x => epsHat B ε lead Q (mkPoint x w)) ∧
          HasSlope (tdisc c (rv M z₀)) (fun x => epsHat B ε lead Q (mkPoint x w)) σ) := by
  let D := tdisc c (rv M z₀)
  obtain ⟨t₀, ht₀⟩ := rv_surjective (w lead)
  have ht₀0 : t₀ ≠ 0 := fun h => hlead (by rw [← ht₀, h, rv_zero])
  have hvt : vfValue t₀ = Values.vrv (w lead) := by
    change Values.vrv (rv M t₀) = _
    rw [ht₀]
  rcases hpiece with hU | hU
  · -- inside the protected neighbourhood: one ball, constant translates
    obtain ⟨z, hzQ, hDK⟩ := Protect.disc_sub_K hv h00 (tdisc_isOpenDisc hv c (τ := rv M z₀)
      (fun h => hz₀ ((rv_eq_zero_iff z₀).mp h))) (fun x hx => by
        obtain ⟨-, z, hz, hxK⟩ := hU x hx
        exact ⟨z, hz, hxK⟩)
    have hhat : ∀ x ∈ D, epsHat B ε lead Q (mkPoint x w) = εfun B ε (mkPoint z w) := by
      intro x hx
      rw [epsHat, if_pos (hU x hx)]
      change εfun B ε (mkPoint (zOf Q x) w) = _
      rw [zOf_eq hv hzQ (hDK hx)]
    refine ⟨?_, Or.inl fun x hx x' hx' => by rw [hhat x hx, hhat x' hx']⟩
    ext p
    constructor
    · rintro ⟨hp1, hp2⟩
      refine ⟨hp1, ?_⟩
      have hclose := (Protect.mem_K_sub (hDK hp1)).2
      have heq := tdisc_eq_of_close hv ht₀0 (c := εfun B ε (mkPoint p.1 w)) (c' := εfun B ε (mkPoint z w))
        (by rw [hvt]; exact hclose)
      have : p.2 ∈ tdisc (εfun B ε (mkPoint p.1 w)) (rv M t₀) := by
        change rv M (p.2 - _) = rv M t₀
        rw [ht₀]; exact hp2
      rw [heq] at this
      change rv M (p.2 - epsHat B ε lead Q (mkPoint p.1 w)) = w lead
      rw [hhat p.1 hp1, ← ht₀]
      exact this
    · rintro ⟨hp1, hp2⟩
      refine ⟨hp1, ?_⟩
      have hclose := (Protect.mem_K_sub (hDK hp1)).2
      have heq := tdisc_eq_of_close hv ht₀0 (c := εfun B ε (mkPoint p.1 w)) (c' := εfun B ε (mkPoint z w))
        (by rw [hvt]; exact hclose)
      have : p.2 ∈ tdisc (εfun B ε (mkPoint z w)) (rv M t₀) := by
        change rv M (p.2 - _) = rv M t₀
        change rv M (p.2 - epsHat B ε lead Q (mkPoint p.1 w)) = w lead at hp2
        rw [hhat p.1 hp1] at hp2
        rw [ht₀]; exact hp2
      rw [← heq] at this
      change rv M (p.2 - _) = w lead
      rw [← ht₀]
      exact this
  · -- outside: the disc avoids `Q`, and `epsHat = ε` on it
    have hDQ : ∀ x ∈ D, x ∉ Q := by
      intro x hx hxQ
      apply hU x hx
      exact ⟨hDB x hx, x, hxQ, Protect.self_mem_K hv hloc w (hDB x hx)⟩
    have hhat : ∀ x ∈ D, epsHat B ε lead Q (mkPoint x w) = εfun B ε (mkPoint x w) := by
      intro x hx
      rw [epsHat, if_neg (hU x hx)]
    have hcell : cellOf D (fun x => εfun B ε (mkPoint x w)) (w lead) =
        cellOf D (fun x => epsHat B ε lead Q (mkPoint x w)) (w lead) := by
      ext p
      constructor
      · rintro ⟨hp1, hp2⟩
        refine ⟨hp1, ?_⟩
        change rv M (p.2 - epsHat B ε lead Q (mkPoint p.1 w)) = w lead
        rw [hhat p.1 hp1]
        exact hp2
      · rintro ⟨hp1, hp2⟩
        refine ⟨hp1, ?_⟩
        change rv M (p.2 - epsHat B ε lead Q (mkPoint p.1 w)) = w lead at hp2
        rw [hhat p.1 hp1] at hp2
        exact hp2
    refine ⟨hcell, ?_⟩
    rcases hgood w c z₀ hz₀ hDB hDQ with hconst | ⟨σ, hinj, hd2d, hslope⟩
    · left
      intro x hx x' hx'
      rw [hhat x hx, hhat x' hx']
      exact hconst x hx x' hx'
    · right
      refine ⟨σ, ?_, ?_, ?_⟩
      · intro x hx x' hx' he
        apply hinj hx hx'
        change εfun B ε (mkPoint x w) = εfun B ε (mkPoint x' w)
        rw [← hhat x hx, ← hhat x' hx']
        exact he
      · intro E hED hE
        have himg : (fun x => epsHat B ε lead Q (mkPoint x w)) '' E =
            (fun x => εfun B ε (mkPoint x w)) '' E :=
          Set.image_congr (fun x hx => hhat x (hED hx))
        rw [himg]
        exact hd2d E hED hE
      · intro x hx x' hx'
        change rv M (epsHat B ε lead Q (mkPoint x w) - epsHat B ε lead Q (mkPoint x' w)) = _
        rw [hhat x hx, hhat x' hx']
        exact hslope x hx x' hx'

end Final

end DiamondIntegral.Section7.Lemma720
