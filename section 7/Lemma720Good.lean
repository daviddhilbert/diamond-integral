import «section 7».Lemma720D2D

/-! Lemma 7.20, step 8: good discs.

For a definable set `B ⊆ VF × RVᵃ` and a definable positioning map `ε : B → VF`, there is
a finite definable set `Q ⊆ VF` (the union of the obstacles of the locus, the two code
relations, the slope relation and the disc-to-disc pieces) such that on every translated
disc `c + τ^♯` inside a label fibre `B_w` and avoiding `Q`, the function `ε(·, w)` is
constant, or injective, disc-to-disc and rv-affine (`exists_good_obstacles`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The slope relation of `ε` on `B`, as a unary relation with two extra RV labels. -/
def slopeRel (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    : Set (Mixed M 1 (a + 2)) :=
  {q | slopeRow (rawDom B) (rawFun B ε)
    (Sum.elim (fun i => (q.2 (Fin.castAdd 2 i)).val) ![(q.1 0).val, (q.2 (Fin.natAdd a 0)).val,
      (q.2 (Fin.natAdd a 1)).val])}

theorem slopeRel_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    (rawMixedSpace (M := M) 1 (a + 2)).Definable S (slopeRel B ε) := by
  have h := definable_of_overBase hc (slopeRow_definable (fullBase S) (rawDom B) (rawFun B ε) (rawFun_graph B hc ε))
  let ψ (z : Fin 1 ⊕ Fin (a + 2) → M) : Fin a ⊕ Fin 3 → M :=
    Sum.elim (fun i => z (.inr (Fin.castAdd 2 i))) ![z (.inl 0), z (.inr (Fin.natAdd a 0)), z (.inr (Fin.natAdd a 1))]
  have hψ : S.DefinableMap LRV ψ := by
    rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · fin_cases i <;> exact Set.DefinableFun.proj LRV
  refine mixed_definable_of_codes _ _ (h.preimage_map hψ) ?_
  intro q
  change _ ↔ slopeRow (rawDom B) (rawFun B ε) (ψ (mixedValues q))
  have he : ψ (mixedValues q) = Sum.elim (fun i => (q.2 (Fin.castAdd 2 i)).val)
      ![(q.1 0).val, (q.2 (Fin.natAdd a 0)).val, (q.2 (Fin.natAdd a 1)).val] := by
    funext i
    rcases i with i | i
    · rfl
    · fin_cases i <;> rfl
  rw [he]
  rfl

section Obstacles
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
include hv

/-- A translated disc is an open disc of the valuation. -/
theorem tdisc_eq_openDisc (c z : VF M) (hz : z ≠ 0) :
    ∃ ρ : Balls.OpenRadius G, tdisc c (rv M z) = Balls.openDisc Valued.v (c + z) ρ := by
  have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
  refine ⟨OrderDual.toDual (Units.mk0 (Valued.v z) hvz), ?_⟩
  ext x
  rw [tdisc_mem_iff hv c z hz x, gval_val, vfValue_lt_iff hv]
  rfl

/-- Rows of a relation with controlled obstacles are constant on a translated disc
avoiding them. -/
theorem rows_const {r : ℕ} {Q : Finset (VF M)} {C : Set (Mixed M 1 r)}
    (hQ : UnaryObstacleControl (G := G) Q C) {c z : VF M} (hz : z ≠ 0)
    (hDQ : ∀ x ∈ tdisc c (rv M z), x ∉ Q) {x y : VF M} (hx : x ∈ tdisc c (rv M z))
    (hy : y ∈ tdisc c (rv M z)) (u : Fin r → RVInfinity M) :
    ((fun _ : Fin 1 => x), u) ∈ C ↔ ((fun _ : Fin 1 => y), u) ∈ C := by
  obtain ⟨ρ, heq⟩ := tdisc_eq_openDisc hv c z hz
  rw [heq] at hDQ hx hy
  exact hQ (c + z) ρ (fun q hqQ hq => hDQ q hq hqQ) x hx y hy u

omit hv in
theorem definable_finset_union {Q₁ Q₂ : Finset (VF M)} (h₁ : S.Definable₁ LRV (Subtype.val '' (Q₁ : Set (VF M))))
    (h₂ : S.Definable₁ LRV (Subtype.val '' (Q₂ : Set (VF M)))) :
    S.Definable₁ LRV (Subtype.val '' ((Q₁ ∪ Q₂ : Finset (VF M)) : Set (VF M))) := by
  rw [Finset.coe_union, Set.image_union]
  exact h₁.union h₂

omit hv in
theorem definable_finset_biUnion {k : ℕ} {Q : Fin k → Finset (VF M)}
    (h : ∀ i, S.Definable₁ LRV (Subtype.val '' (Q i : Set (VF M)))) :
    S.Definable₁ LRV (Subtype.val '' ((Finset.univ.biUnion Q : Finset (VF M)) : Set (VF M))) := by
  have he : Subtype.val '' ((Finset.univ.biUnion Q : Finset (VF M)) : Set (VF M)) =
      ⋃ i, Subtype.val '' (Q i : Set (VF M)) := by
    rw [Finset.coe_biUnion]
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.image_iUnion]
  rw [he]
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ ⋃ i, Subtype.val '' (Q i : Set (VF M))}
  have : {z : Fin 1 → M | z 0 ∈ ⋃ i, Subtype.val '' (Q i : Set (VF M))} =
      ⋃ i, {z : Fin 1 → M | z 0 ∈ Subtype.val '' (Q i : Set (VF M))} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [this]
  exact Set.definable_iUnion_of_finite (fun i => h i)

/-- **Good discs.** -/
theorem exists_good_obstacles (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (B : DefSet (rawMixedSpace (M := M) 1 a) S) (ε : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    ∃ Q : Finset (VF M), S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))) ∧
      ∀ (w : Fin a → RVInfinity M) (c z : VF M) (hz : z ≠ 0),
        (∀ x ∈ tdisc c (rv M z), mkPoint x w ∈ B.carrier) → (∀ x ∈ tdisc c (rv M z), x ∉ Q) →
        (∀ x ∈ tdisc c (rv M z), ∀ x' ∈ tdisc c (rv M z), εfun B ε (mkPoint x w) = εfun B ε (mkPoint x' w)) ∨
        ∃ σ : RV M, Set.InjOn (fun x => εfun B ε (mkPoint x w)) (tdisc c (rv M z)) ∧
          DiscToDisc (tdisc c (rv M z)) (fun x => εfun B ε (mkPoint x w)) ∧
          HasSlope (tdisc c (rv M z)) (fun x => εfun B ε (mkPoint x w)) σ := by
  obtain ⟨C⟩ := exists_codes hc h00 hκ hs hsmall hΓ B ε
  obtain ⟨k, P, hPcov, hPsub, hPd2d⟩ := exists_d2d_pieces hc h00 hκ hs hΓ B ε C
  obtain ⟨QL, hQL, hcL⟩ := exists_unary_obstacles (G := G) hc hv C.L
  obtain ⟨Q0, hQ0, hc0⟩ := exists_unary_obstacles (G := G) hc hv C.rel₀
  obtain ⟨Q1, hQ1, hc1⟩ := exists_unary_obstacles (G := G) hc hv C.rel₁
  obtain ⟨Qs, hQs, hcs⟩ := exists_unary_obstacles (G := G) hc hv
    (⟨slopeRel B ε, slopeRel_definable hc B ε⟩ : DefSet (rawMixedSpace (M := M) 1 (a + 2)) S)
  have hPobs : ∀ i, ∃ Q : Finset (VF M), S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))) ∧
      UnaryObstacleControl (G := G) Q (P i).carrier := fun i => exists_unary_obstacles (G := G) hc hv (P i)
  choose QP hQP hcP using hPobs
  let Q : Finset (VF M) := QL ∪ Q0 ∪ Q1 ∪ Qs ∪ Finset.univ.biUnion QP
  refine ⟨Q, ?_, ?_⟩
  · exact definable_finset_union (definable_finset_union (definable_finset_union
      (definable_finset_union hQL hQ0) hQ1) hQs) (definable_finset_biUnion hQP)
  intro w c z hz hDB hDQ
  let D := tdisc c (rv M z)
  have hsubL : ∀ x ∈ D, x ∉ QL := fun x hx h => hDQ x hx (by simp [Q, h])
  have hsub0 : ∀ x ∈ D, x ∉ Q0 := fun x hx h => hDQ x hx (by simp [Q, h])
  have hsub1 : ∀ x ∈ D, x ∉ Q1 := fun x hx h => hDQ x hx (by simp [Q, h])
  have hsubs : ∀ x ∈ D, x ∉ Qs := fun x hx h => hDQ x hx (by simp [Q, h])
  have hsubP : ∀ i, ∀ x ∈ D, x ∉ QP i := fun i x hx h => hDQ x hx (by
    simp only [Q, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨i, h⟩)
  -- the disc is nonempty
  obtain ⟨x₀, hx₀⟩ : D.Nonempty := ⟨c + z, by
    change rv M (c + z - c) = rv M z
    rw [add_sub_cancel_left]⟩
  let g : VF M → VF M := fun x => εfun B ε (mkPoint x w)
  by_cases hL : mkPoint x₀ w ∈ C.L.carrier
  · -- constant case
    left
    have hallL : ∀ x ∈ D, mkPoint x w ∈ C.L.carrier := fun x hx =>
      (rows_const hv hcL hz hsubL hx₀ hx w).mp hL
    intro x hx x' hx'
    have hcode : C.c₀ (mkPoint x w) = C.c₀ (mkPoint x' w) := by
      have hm : ((fun _ : Fin 1 => x), Fin.append w (C.c₀ (mkPoint x w))) ∈ C.rel₀.carrier :=
        (C.rel₀_iff _ w _).mpr ⟨hallL x hx, rfl⟩
      have hm' := (rows_const hv hc0 hz hsub0 hx hx' _).mp hm
      exact ((C.rel₀_iff _ w _).mp hm').2
    have := C.const ⟨mkPoint x w, hDB x hx⟩ ⟨mkPoint x' w, hDB x' hx'⟩ (hallL x hx) (hallL x' hx') rfl hcode
    change εfun B ε (mkPoint x w) = εfun B ε (mkPoint x' w)
    rw [εfun_of_mem B ε ⟨mkPoint x w, hDB x hx⟩, εfun_of_mem B ε ⟨mkPoint x' w, hDB x' hx'⟩, this]
  · right
    have hallL : ∀ x ∈ D, mkPoint x w ∉ C.L.carrier := fun x hx h =>
      hL ((rows_const hv hcL hz hsubL hx hx₀ w).mp h)
    have hcode : ∀ x ∈ D, C.c₁ (mkPoint x w) = C.c₁ (mkPoint x₀ w) := by
      intro x hx
      have hm : ((fun _ : Fin 1 => x₀), Fin.append w (C.c₁ (mkPoint x₀ w))) ∈ C.rel₁.carrier :=
        (C.rel₁_iff _ w _).mpr ⟨hDB x₀ hx₀, hallL x₀ hx₀, rfl⟩
      have hm' := (rows_const hv hc1 hz hsub1 hx₀ hx _).mp hm
      exact ((C.rel₁_iff _ w _).mp hm').2.2.symm
    have hinj : Set.InjOn g D := by
      intro x hx x' hx' he
      have he' : ε ⟨mkPoint x w, hDB x hx⟩ = ε ⟨mkPoint x' w, hDB x' hx'⟩ := by
        apply Subtype.ext
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        have := he
        change εfun B ε (mkPoint x w) = εfun B ε (mkPoint x' w) at this
        rw [εfun_of_mem B ε ⟨mkPoint x w, hDB x hx⟩, εfun_of_mem B ε ⟨mkPoint x' w, hDB x' hx'⟩] at this
        exact this
      have := C.inj ⟨mkPoint x w, hDB x hx⟩ ⟨mkPoint x' w, hDB x' hx'⟩ (hallL x hx) (hallL x' hx') rfl
        ((hcode x hx).trans (hcode x' hx').symm) he'
      have h2 := congrArg (fun q : B => q.val.1 0) this
      exact h2
    -- the piece containing the disc
    obtain ⟨i₀, hi₀⟩ := hPcov (mkPoint x₀ w) (hDB x₀ hx₀) (hallL x₀ hx₀)
    have hallP : ∀ x ∈ D, mkPoint x w ∈ (P i₀).carrier := fun x hx =>
      (rows_const hv (hcP i₀) hz (hsubP i₀) hx₀ hx w).mp hi₀
    have hd2d : DiscToDisc D g := by
      intro E hED hE
      exact hPd2d i₀ w (C.c₁ (mkPoint x₀ w)) E hE (fun x hx => ⟨hallP x (hED hx), hcode x (hED hx)⟩)
    -- the slope
    have hrows : ∀ x ∈ D, ∀ y ∈ D, ∀ b t : M,
        slopeRow (rawDom B) (rawFun B ε) (Sum.elim (rvValues w) ![x.val, b, t]) ↔
          slopeRow (rawDom B) (rawFun B ε) (Sum.elim (rvValues w) ![y.val, b, t]) := by
      intro x hx y hy b t
      by_cases hb : iRV b
      · by_cases ht : iRV t
        · let u : Fin (a + 2) → RVInfinity M := Fin.append w ![⟨b, hb⟩, ⟨t, ht⟩]
          have hux : ∀ v : VF M, ((fun _ : Fin 1 => v), u) ∈ slopeRel B ε ↔
              slopeRow (rawDom B) (rawFun B ε) (Sum.elim (rvValues w) ![v.val, b, t]) := by
            intro v
            change slopeRow _ _ _ ↔ slopeRow _ _ _
            have he : (Sum.elim (fun i => (u (Fin.castAdd 2 i)).val)
                ![v.val, (u (Fin.natAdd a 0)).val, (u (Fin.natAdd a 1)).val] : Fin a ⊕ Fin 3 → M) =
                Sum.elim (rvValues w) ![v.val, b, t] := by
              funext i
              rcases i with i | i
              · simp only [u, Fin.append_left]
                rfl
              · fin_cases i
                · rfl
                · simp only [u, Fin.append_right]
                  rfl
                · simp only [u, Fin.append_right]
                  rfl
            rw [he]
          rw [← hux, ← hux]
          exact rows_const hv hcs hz hsubs hx hy u
        · constructor <;> rintro ⟨-, ht', -⟩ <;> exact absurd ht'.1 ht
      · constructor <;> rintro ⟨hb', -⟩ <;> exact absurd hb'.1 hb
    have hDA : ∀ x ∈ D, x.val ∈ rawDom B (rvValues w) := fun x hx => ⟨⟨mkPoint x w, hDB x hx⟩, rfl, rfl⟩
    have hg : ∀ x ∈ D, (g x).val = rawFun B ε (rvValues w) x.val := by
      intro x hx
      have := rawFun_point B ε ⟨mkPoint x w, hDB x hx⟩
      change rawFun B ε (rvValues w) x.val = ((ε ⟨mkPoint x w, hDB x hx⟩).val 0).val at this
      rw [this]
      change (εfun B ε (mkPoint x w)).val = _
      rw [εfun_of_mem B ε ⟨mkPoint x w, hDB x hx⟩]
    obtain ⟨σ, hσ⟩ := hasSlope_of_rows hv hc h00 hκ hs hsmall (rawDom B) (rawFun B ε) (rawFun_graph B hc ε)
      (rawFun_vf B ε) (rvValues w) c z hz g hDA hg hinj hrows
    exact ⟨σ, hinj, hd2d, hσ⟩

end Obstacles

end DiamondIntegral.Section7.Lemma720
