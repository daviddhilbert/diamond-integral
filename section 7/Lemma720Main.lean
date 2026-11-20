import «section 7».Lemma720UniformDef
import «section 5».GammaQEFiniteLaws
import «section 6».InitialPreparation
import «section 6».BranchedShearDimensionInduction
import «section 6».ZeroCenteredGeometry
import «section 6».ZeroCenteredHomeomorphism

/-! **Lemma 7.20 (`decom:into:2:units`).** A proof of the replaceable input
`TwoCellInput.Lemma720 M G`.

Construction (`section 7/LEMMA-7-20-PLAN.md`):
1. normalize `A`; take a Section 6 first stage contracting the second coordinate, whose
   offset `ε` positions the fibres (`Lemma720Stage1`);
2. on the contracted set `B₁`, find the finite obstacle set `Q` of the positioning data
   (`Lemma720Good`) and its protected neighbourhood `U` (`Lemma720Protect`);
3. take a second stage protecting `U` and `B₁ ∖ U` (`Lemma720Second`);
4. every fibre is the cell over the second-stage disc with positioning map `epsHat`
   (`Lemma720Cells`), classified by `kindOf` (`Lemma720CellGeom`), with uniform data
   definable over the base (`Lemma720Uniform`, `Lemma720UniformDef`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells
open DiamondIntegral.Section7.TwoCellInput

variable (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Lemma 7.20 (`decom:into:2:units`)**: the replaceable input is a theorem. -/
theorem lemma720 : Lemma720 M G := by
  intro hc h00 κ hκ hs hv T V hV hVT hTV hnt hsmall hΓ r A hA
  let lin := DiamondIntegral.Section5.GammaQE.gamma_piecewise_rational_affine (M := M)
  -- normalization and first stage
  obtain ⟨N⟩ := exists_zeroCentered_data h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt A hA
  have hB₀ : ProperInvariant (T : Set M) (normalizedSet N).carrier :=
    reindexedVFSet_properInvariant _ _ (N.image_properInvariant h00 hc hκ hs hv)
  have hB₀D : VFDoublyBounded (normalizedSet N).carrier :=
    reindexedVFSet_doublyBounded _ _ N.image_vfDoublyBounded
  obtain ⟨S₁⟩ := exists_shear_contraction_stage_all_dimensions (G := G) h00 hc lin hκ hs hv
    (T : Set M) V hsmall hΓ hV hVT hTV hnt (normalizedSet N) hB₀ hB₀D
  let B₁ := S₁.stage.contracted
  let ε := Stage.offset S₁.stage S₁.displacement
  let lead := S₁.stage.leading
  have hB₁ : ProperInvariant (T : Set M) B₁.carrier := S₁.stage.contracted_proper
  have hlead : ∀ q ∈ B₁.carrier, q.2 lead ≠ rvZero M := fun q hq => lead_ne_zero S₁.stage q hq
  -- obstacles and the protected neighbourhood
  obtain ⟨Q, hQ, hgood⟩ := exists_good_obstacles hv hc h00 hκ hs hsmall hΓ B₁ ε
  have hloc := locConst_of_stage hv S₁.stage S₁.displacement
  let U := Protect.U B₁.carrier (εfun B₁ ε) lead Q
  obtain ⟨hUp, hVp⟩ := U_pieces_proper hv hc h00 hκ hs B₁ hB₁ ε lead Q hQ hlead hloc
  let C : Fin 2 → DefSet (rawMixedSpace (M := M) 1 S₁.stage.arity) (T : Set M) :=
    ![⟨U, U_definable B₁ ε lead Q hc hQ hlead⟩, ⟨B₁.carrier \ U, hVp.definable⟩]
  have hCA : ∀ i, (C i).carrier ⊆ B₁.carrier := by
    intro i
    fin_cases i
    · exact fun q hq => hq.1
    · exact fun q hq => hq.1
  have hC : ∀ i, ProperInvariant (T : Set M) (C i).carrier := by
    intro i
    fin_cases i
    · exact hUp
    · exact hVp
  -- second stage
  obtain ⟨S₂, hS₂⟩ := exists_protected_stage (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt
    B₁ hB₁ C hCA hC
  let X : Build (G := G) A := ⟨N, S₁, S₂⟩
  let F := X.contraction h00 hc lin hκ hs hv hsmall hΓ
  refine ⟨Equiv.refl (Fin 2), F, ?_⟩
  let T₂ := S₂.stage
  let hD₂ := S₂.displacement
  -- the fibre over a target point is the cell over the second-stage disc
  have hlead₂ : ∀ s : F.rvTarget, s.val.2 T₂.leading ≠ rvZero M := fun s => lead_ne_zero T₂ s.val s.property
  have hcOf : ∀ s : F.rvTarget, Final.cOf T₂ hD₂ s.val.2 = X.eps₂ s := by
    intro s
    have hs : ((Fin.elim0 : Fin 0 → VF M), s.val.2) ∈ T₂.contracted.carrier := by
      have : s.val = ((Fin.elim0 : Fin 0 → VF M), s.val.2) := Prod.ext (funext fun i => i.elim0) rfl
      rw [← this]
      exact s.property
    rw [Final.cOf, dif_pos hs]
    have hss : (⟨((Fin.elim0 : Fin 0 → VF M), s.val.2), hs⟩ : T₂.contracted) = s :=
      Subtype.ext (Prod.ext (funext fun i => i.elim0) rfl)
    rw [hss]
    rfl
  have hfibre : ∀ s : F.rvTarget, ∀ x ∈ Final.Dof T₂ hD₂ s.val.2,
      ∃ b : B₁, T₂.contraction b = s ∧ b.val = mkPoint x (Final.wOf T₂ s.val.2) := by
    intro s x hx
    have hx' : rv M (x - Stage.eps T₂ hD₂ s) = s.val.2 T₂.leading := by
      have := hx
      change rv M (x - Final.cOf T₂ hD₂ s.val.2) = _ at this
      rw [hcOf s] at this
      exact this
    obtain ⟨b, hb, hbx⟩ := Stage.exists_mem_fibre T₂ hD₂ s x hx'
    refine ⟨b, hb, Prod.ext ?_ ?_⟩
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hbx
    · exact ((X.second_contraction_eq_iff b s).mp hb).1
  have hDB : ∀ s : F.rvTarget, ∀ x ∈ Final.Dof T₂ hD₂ s.val.2, mkPoint x (Final.wOf T₂ s.val.2) ∈ B₁.carrier := by
    intro s x hx
    obtain ⟨b, -, hb⟩ := hfibre s x hx
    rw [← hb]
    exact b.property
  have hcell : ∀ s : F.rvTarget, cellAt F s =
      cellOf (Final.Dof T₂ hD₂ s.val.2) (fun x => εfun B₁ ε (mkPoint x (Final.wOf T₂ s.val.2)))
        (Final.wOf T₂ s.val.2 lead) := by
    intro s
    ext ⟨x, y⟩
    rw [X.mem_cellAt_iff h00 hc lin hκ hs hv hsmall hΓ s x y]
    constructor
    · rintro ⟨b, hb, hbx, hby⟩
      obtain ⟨hlab, hrv⟩ := (X.second_contraction_eq_iff b s).mp hb
      have hbv : b.val = mkPoint x (Final.wOf T₂ s.val.2) := by
        refine Prod.ext ?_ hlab
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact hbx
      refine ⟨?_, ?_⟩
      · change rv M (x - Final.cOf T₂ hD₂ s.val.2) = _
        rw [hcOf s, ← hbx]
        exact hrv
      · change rv M (y - εfun B₁ ε (mkPoint x (Final.wOf T₂ s.val.2))) = _
        rw [← hbv, εfun_of_mem B₁ ε b]
        have := hby
        rw [hbv] at this
        exact this
    · rintro ⟨hx, hy⟩
      obtain ⟨b, hb, hbv⟩ := hfibre s x hx
      refine ⟨b, hb, ?_, ?_⟩
      · rw [hbv]; rfl
      · change rv M (y - εfun B₁ ε (mkPoint x (Final.wOf T₂ s.val.2))) = _ at hy
        rw [← hbv, εfun_of_mem B₁ ε b] at hy
        change rv M (y - (ε b).val 0) = b.val.2 lead
        rw [hbv]
        exact hy
  -- the disc of each fibre lies inside the protected neighbourhood or misses it
  have hpiece : ∀ s : F.rvTarget,
      (∀ x ∈ Final.Dof T₂ hD₂ s.val.2, mkPoint x (Final.wOf T₂ s.val.2) ∈ U) ∨
      (∀ x ∈ Final.Dof T₂ hD₂ s.val.2, mkPoint x (Final.wOf T₂ s.val.2) ∉ U) := by
    intro s
    by_cases h : ∃ x ∈ Final.Dof T₂ hD₂ s.val.2, mkPoint x (Final.wOf T₂ s.val.2) ∈ U
    · obtain ⟨x₀, hx₀, hx₀U⟩ := h
      left
      intro x hx
      obtain ⟨b, hb, hbv⟩ := hfibre s x hx
      obtain ⟨b₀, hb₀, hb₀v⟩ := hfibre s x₀ hx₀
      have h0 : b₀.val ∈ (C 0).carrier := by rw [hb₀v]; exact hx₀U
      have := hS₂ 0 b₀ b (hb₀.trans hb.symm) h0
      rw [hbv] at this
      exact this
    · right
      push_neg at h
      exact h
  -- the leading label over a target point is nonzero
  have hDne : ∀ s : F.rvTarget, (Final.Dof T₂ hD₂ s.val.2).Nonempty := by
    intro s
    obtain ⟨z₀, hz₀⟩ := rv_surjective (s.val.2 T₂.leading)
    refine ⟨Final.cOf T₂ hD₂ s.val.2 + z₀, ?_⟩
    change rv M (Final.cOf T₂ hD₂ s.val.2 + z₀ - Final.cOf T₂ hD₂ s.val.2) = _
    rw [add_sub_cancel_left, hz₀]
  have hwlead : ∀ s : F.rvTarget, Final.wOf T₂ s.val.2 lead ≠ rvZero M := by
    intro s
    obtain ⟨x, hx⟩ := hDne s
    exact hlead _ (hDB s x hx)
  have htU : ∀ s : F.rvTarget, (Final.tU lead T₂ s.val.2).val = Final.wOf T₂ s.val.2 lead := by
    intro s
    rw [Final.tU, dif_pos (hwlead s)]
  -- the cells
  have hcells : ∀ s : F.rvTarget, cellAt F s =
      cellOf (Final.Dof T₂ hD₂ s.val.2) (Final.εU ε lead Q T₂ s.val.2) (Final.tU lead T₂ s.val.2).val ∧
      ((∀ x ∈ Final.Dof T₂ hD₂ s.val.2, ∀ x' ∈ Final.Dof T₂ hD₂ s.val.2,
          Final.εU ε lead Q T₂ s.val.2 x = Final.εU ε lead Q T₂ s.val.2 x') ∨
        (Set.InjOn (Final.εU ε lead Q T₂ s.val.2) (Final.Dof T₂ hD₂ s.val.2) ∧
          DiscToDisc (Final.Dof T₂ hD₂ s.val.2) (Final.εU ε lead Q T₂ s.val.2) ∧
          HasSlope (Final.Dof T₂ hD₂ s.val.2) (Final.εU ε lead Q T₂ s.val.2) (Final.σU ε lead Q T₂ hD₂ s.val.2))) := by
    intro s
    obtain ⟨z₀, hz₀⟩ := rv_surjective (s.val.2 T₂.leading)
    have hz₀0 : z₀ ≠ 0 := fun h => hlead₂ s (by rw [← hz₀, h, rv_zero])
    have hDeq : Final.Dof T₂ hD₂ s.val.2 = tdisc (Final.cOf T₂ hD₂ s.val.2) (rv M z₀) := by
      rw [hz₀]; rfl
    have hdisc := Final.cell_of_disc hv h00 hgood hloc hz₀0 (fun x hx => hDB s x (hDeq ▸ hx))
      (by rcases hpiece s with h | h
          · exact Or.inl fun x hx => h x (hDeq ▸ hx)
          · exact Or.inr fun x hx => h x (hDeq ▸ hx)) (hwlead s)
    rw [← hDeq] at hdisc
    refine ⟨?_, ?_⟩
    · rw [hcell s, hdisc.1, htU s]
      rfl
    · rcases hdisc.2 with hconst | ⟨σ, hinj, hd2d, hsl⟩
      · exact Or.inl hconst
      · refine Or.inr ⟨hinj, hd2d, ?_⟩
        have hex : ∃ σ : RV M, HasSlope (Final.Dof T₂ hD₂ s.val.2) (Final.εU ε lead Q T₂ s.val.2) σ := ⟨σ, hsl⟩
        rw [Final.σU, dif_pos hex]
        exact hex.choose_spec
  have hfirst : ∀ s : F.rvTarget, first (cellAt F s) = Final.Dof T₂ hD₂ s.val.2 := by
    intro s
    rw [(hcells s).1, first_cellOf]
  refine ⟨Final.εU ε lead Q T₂, Final.tU lead T₂, Final.t₁U ε lead Q T₂ hD₂, Final.kindU ε lead Q T₂ hD₂,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := Final.def_eps (ε := ε) (lead := lead) (Q := Q) (T₂ := T₂) (hD₂ := hD₂) hc hv hQ hlead
    show (T : Set M).Definable LRV {z : Fin (2 + T₂.arity) → M | ∃ s : T₂.contracted, ∃ a ∈ first (cellAt F s),
      z = Fin.append ![a.val, (Final.εU ε lead Q T₂ s.val.2 a).val] (rvValues s.val.2)}
    convert h using 1
    ext z
    constructor
    · rintro ⟨s, x, hx, rfl⟩
      exact ⟨s, x, hfirst s ▸ hx, rfl⟩
    · rintro ⟨s, x, hx, rfl⟩
      exact ⟨s, x, (hfirst s).symm ▸ hx, rfl⟩
  · exact Final.def_t (lead := lead) (Q := Q) (T₂ := T₂) (hD₂ := hD₂) hc hv hQ hlead
  · refine Final.def_t₁ (ε := ε) (lead := lead) (Q := Q) (T₂ := T₂) (hD₂ := hD₂) hc hv hQ hlead
      (fun s hk => ?_)
    rcases (hcells s).2 with hconst | ⟨-, -, hsl⟩
    · exfalso
      rw [Final.kindU, kindOf, if_pos hconst] at hk
      exact absurd hk (by decide)
    · exact ⟨_, hsl⟩
  · exact fun i => Final.def_kind (ε := ε) (lead := lead) (Q := Q) (T₂ := T₂) (hD₂ := hD₂) hc hv hQ hlead i
  · intro s
    obtain ⟨hceq, hcase⟩ := hcells s
    rw [hceq]
    have hD := tdisc_isOpenDisc hv (Final.cOf T₂ hD₂ s.val.2) (hlead₂ s)
    have hD0 : (0 : VF M) ∉ Final.Dof T₂ hD₂ s.val.2 := by
      intro h0
      have := S₁.stage.contracted_doublyBounded.nonzero (hDB s 0 h0) 0
      exact this rfl
    have hY : ∀ p ∈ cellOf (Final.Dof T₂ hD₂ s.val.2) (Final.εU ε lead Q T₂ s.val.2) (Final.tU lead T₂ s.val.2).val,
        p.2 ≠ 0 := by
      intro p hp
      rw [← hceq] at hp
      obtain ⟨q, -, rfl⟩ := hp
      have hmem : N.point q.val ∈ N.map.image.carrier := by
        rw [N.image_carrier]
        exact ⟨q.val, q.property, rfl⟩
      exact N.image_vfDoublyBounded.nonzero hmem _
    exact cellWith_kindOf hv hD hD0 hY hcase

end DiamondIntegral.Section7.Lemma720
