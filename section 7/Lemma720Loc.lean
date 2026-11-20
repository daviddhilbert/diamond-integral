import «section 7».Lemma720ProtectDef

/-! Lemma 7.20, step 11: local constancy of the first-stage fibres, and properness of
the protected pieces.

* `locConst_of_stage`: for a two-variable stage with label-determined displacement, the
  translates `ε(x, w) + t^♯` are locally constant in `x`, with a radius for each label
  tuple. This follows from the proper covariance of the stage lift: its graph fibres are
  `α`-invariant.
* `lead_ne_zero`: the leading label of a point of the contracted set is nonzero.
* `U_proper`, `compl_proper`: the protected neighbourhood and its complement in a proper
  invariant set are proper invariant (Lemma 6.5). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section Stage
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {A : DefSet (rawMixedSpace (M := M) 2 r) S} (T : StandardContractionStage (G := G) A)
  (hD : SameLabelShearDisplacement T.lift (Fin.last 1))

/-- The leading label of a point of the contracted set is nonzero. -/
theorem lead_ne_zero {n : ℕ} {A' : DefSet (rawMixedSpace (M := M) (n+1) r) S} (T' : StandardContractionStage (G := G) A')
    (q : Mixed M n T'.arity) (hq : q ∈ T'.contracted.carrier) : q.2 T'.leading ≠ rvZero M := by
  obtain ⟨⟨q', hq'⟩, hqq⟩ := hq
  have hrec := (T'.recover_target q').mp hq'
  have hne := T'.doublyBounded.nonzero hq' (Fin.last n)
  have hval : q.2 = q'.2 := by
    have := congrArg Prod.snd hqq
    exact this.symm
  rw [hval, ← hrec.2]
  intro h
  exact hne ((rv_eq_zero_iff _).mp h)

include hv in
/-- **Local constancy of the first-stage translates.** -/
theorem locConst_of_stage :
    Protect.LocConst T.contracted.carrier (εfun T.contracted (Stage.offset T hD)) T.leading := by
  intro w
  let u : Fin r → RVInfinity M := fun i => w (T.oldLabels i)
  obtain ⟨α, β, -, -, hαinv, -, -⟩ := T.home.covariant.radii u w
  refine ⟨α 0, fun x x' hxx' hx => ?_⟩
  let b : T.contracted := ⟨mkPoint x w, hx⟩
  have key : ∀ y : VF M, rv M (y - Stage.eps T hD b) = w T.leading →
      ∃ hx' : mkPoint x' w ∈ T.contracted.carrier,
        rv M (y - Stage.eps T hD ⟨mkPoint x' w, hx'⟩) = w T.leading := by
    intro y hy
    obtain ⟨p, hp, hpy⟩ := Stage.exists_mem_fibre T hD b y hy
    obtain ⟨hinit, hlab, -⟩ := (Stage.contraction_eq_iff T hD p b).mp hp
    have hp1 : p.val.1 = ![x, y] := by
      funext i
      fin_cases i
      · have := congrFun hinit 0
        exact this
      · exact hpy
    have hplab : p.val.2 = u := funext hlab
    have hlift : (T.lift p).val.2 = w := by
      have := congrArg (fun z : T.contracted => z.val.2) hp
      exact this
    have hsrc : p.val.1 ∈ graphFibreSource T.lift u w :=
      ⟨(T.lift p).val.1, p, Prod.ext rfl hplab, Prod.ext rfl hlift⟩
    have hcong : Congruent α p.val.1 ![x', y] := by
      intro i
      fin_cases i
      · rw [hp1]
        exact hxx'
      · rw [hp1]
        change (α 1).val < vfValue (y - y)
        rw [sub_self]
        exact SpecialTransformations.Section9.gamma_lt_value_zero _
    obtain ⟨b', p', hp'1, hp'2⟩ := (hαinv _ _ hcong).mp hsrc
    have hp'v : p'.val = (![x', y], u) := hp'1
    have hc' : (T.contraction p').val = mkPoint x' w := by
      rw [T.contraction_value]
      refine Prod.ext ?_ ?_
      · funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        change (T.lift p').val.1 (Fin.castSucc 0) = x'
        rw [T.relative p' 0, hp'v]
        rfl
      · exact (Prod.mk.inj hp'2).2
    have hmem : mkPoint x' w ∈ T.contracted.carrier := hc' ▸ (T.contraction p').property
    refine ⟨hmem, ?_⟩
    have hcp : T.contraction p' = ⟨mkPoint x' w, hmem⟩ := Subtype.ext hc'
    have := ((Stage.contraction_eq_iff T hD p' _).mp hcp).2.2
    rw [hp'v] at this
    exact this
  have hlead : w T.leading ≠ rvZero M := lead_ne_zero T (mkPoint x w) hx
  obtain ⟨z₀, hz₀⟩ := rv_surjective (w T.leading)
  have hz₀0 : z₀ ≠ 0 := fun h => hlead (by rw [← hz₀, h, rv_zero])
  obtain ⟨hx', hrv⟩ := key (Stage.eps T hD b + z₀) (by rw [add_sub_cancel_left, hz₀])
  refine ⟨hx', ?_⟩
  rw [εfun_of_mem T.contracted (Stage.offset T hD) ⟨mkPoint x w, hx⟩,
    εfun_of_mem T.contracted (Stage.offset T hD) ⟨mkPoint x' w, hx'⟩]
  rw [← hz₀] at hrv
  have h := (rv_eq_iff_value_close hz₀0).mp hrv
  have he : Stage.eps T hD b + z₀ - Stage.eps T hD ⟨mkPoint x' w, hx'⟩ - z₀ =
      Stage.eps T hD b - Stage.eps T hD ⟨mkPoint x' w, hx'⟩ := by ring
  rw [he] at h
  rw [← hz₀]
  exact h

end Stage

section Pieces
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {a : ℕ}

theorem vfBounded_mono {n m : ℕ} {X Y : Set (Mixed M n m)} (h : VFBounded Y) (hXY : X ⊆ Y) : VFBounded X := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, fun p hp i => hγ p (hXY hp) i⟩

theorem rvBounded_mono {n m : ℕ} {X Y : Set (Mixed M n m)} (h : RVSupportDoublyBounded Y) (hXY : X ⊆ Y) :
    RVSupportDoublyBounded X := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, fun p hp i => hγ p (hXY hp) i⟩

include hv in
/-- **The protected pieces are proper invariant.** -/
theorem U_pieces_proper (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (B : DefSet (rawMixedSpace (M := M) 1 a) S) (hB : ProperInvariant S B.carrier)
    (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (lead : Fin a) (Q : Finset (VF M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
    (hlead : ∀ q ∈ B.carrier, q.2 lead ≠ rvZero M)
    (hloc : Protect.LocConst B.carrier (εfun B ε) lead) :
    ProperInvariant S (Protect.U B.carrier (εfun B ε) lead Q) ∧
      ProperInvariant S (B.carrier \ Protect.U B.carrier (εfun B ε) lead Q) := by
  have hUdef := U_definable B ε lead Q hc hQ hlead
  have hUB : Protect.U B.carrier (εfun B ε) lead Q ⊆ B.carrier := fun q hq => hq.1
  have hVdef : (rawMixedSpace (M := M) 1 a).Definable S (B.carrier \ Protect.U B.carrier (εfun B ε) lead Q) :=
    B.definable.inter _ (hUdef.compl _)
  have hUinv (w : Fin a → RVInfinity M) : ∃ β : Gamma M,
      AlphaInvariant (fun _ => β) (vfFibre (Protect.U B.carrier (εfun B ε) lead Q) w) := by
    obtain ⟨β, hβ⟩ := Protect.U_fibre_invariant hv hloc (Q := Q) w
    exact ⟨β, fun x x' hxx' => hβ x x' (hxx' 0)⟩
  refine ⟨(lemma_6_5 h00 hc hκ hs hv _ hUdef (vfBounded_mono hB.vfBounded hUB)
    (rvBounded_mono hB.rvBounded hUB)).mpr fun w => ?_,
    (lemma_6_5 h00 hc hκ hs hv _ hVdef (vfBounded_mono hB.vfBounded Set.diff_subset)
    (rvBounded_mono hB.rvBounded Set.diff_subset)).mpr fun w => ?_⟩
  · obtain ⟨β, hβ⟩ := hUinv w
    exact hβ.isClopen hv
  · obtain ⟨β, hβ⟩ := hUinv w
    obtain ⟨α, -, hα⟩ := hB.radii w
    let γ := max (α 0) β
    have hinv : AlphaInvariant (fun _ => γ)
        (vfFibre (B.carrier \ Protect.U B.carrier (εfun B ε) lead Q) w) := by
      intro x x' hxx'
      have h1 : Congruent α x x' := by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact lt_of_le_of_lt (show (α 0).val ≤ γ.val from le_max_left _ _) (hxx' 0)
      have h2 : Congruent (fun _ => β) x x' := by
        intro i
        exact lt_of_le_of_lt (show β.val ≤ γ.val from le_max_right _ _) (hxx' i)
      exact and_congr (hα x x' h1) (not_congr (hβ x x' h2))
    exact hinv.isClopen hv

end Pieces

end DiamondIntegral.Section7.Lemma720
