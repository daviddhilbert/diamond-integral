import «section 2».OpenDiscGeometry
import «section 2».AtomicPolydiscs
import Section3.GammaBaseFiniteExceptions
import Section3.DefinableCosets

/-! Unary ACVF sets whose pairs are enclosed by open discs in the set.
The coordinate-chain argument supplies this geometric hypothesis.
Classification uses proved ACVF geometry, with no T-convex input. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open ValOneEC

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem translated_definable (B : ParameterBase M) (C : Set M)
    (hC : GammaParameters.DefinableAtBase B .vf C) (p : VF M) :
    ∃ E : ParameterBase M, GammaParameters.DefinableAtBase E .vf
      (Subtype.val '' {x : VF M | (x+p).val ∈ C}) := by
  obtain ⟨k, t, hCr⟩ := hC.specialize
  let S := B.real ∪ Set.range (GammaParameters.rawTuple t)
  let B0 : ParameterBase M := ⟨S, ∅⟩
  let a : Fin 1 → M := fun _ => (-p).val
  have hR := GammaParameters.real_definableOverBase B0 (fun _ : Fin 2 => .vf)
    (DefinableCosets.relation C) (DefinableCosets.relation_definable S C hCr)
  have hslice := coordinate_section_definable B0 (0 : Fin 2) a
    (fun _ => (-p).property) (DefinableCosets.relation C) hR
  refine ⟨tupleBase B0 a, ?_⟩
  convert hslice using 1
  ext z
  have hneg : iVFNeg (-p).val = p.val := congrArg Subtype.val (neg_neg p)
  constructor
  · rintro ⟨x, hx, rfl⟩
    change iVF x.val ∧ iVF (-p).val ∧ iVFAdd x.val (iVFNeg (-p).val) ∈ C
    rw [hneg]
    exact ⟨x.property, (-p).property, hx⟩
  · intro hz
    change iVF z ∧ iVF (-p).val ∧ iVFAdd z (iVFNeg (-p).val) ∈ C at hz
    rw [hneg] at hz
    let x : VF M := ⟨z, hz.1⟩
    exact ⟨x, hz.2.2, rfl⟩

private theorem enclosed_downward {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (C : Set M)
    (henclose : ∀ p : VF M, p.val ∈ C → ∀ q : VF M, q.val ∈ C →
      ∃ D, IsOpenDisc D ∧ D ⊆ C ∧ p.val ∈ D ∧ q.val ∈ D)
    (p x y : VF M) (hp : p.val ∈ C) (hx : x.val ∈ C)
    (hy : v (y-p) ≤ v (x-p)) : y.val ∈ C := by
  obtain ⟨D, hD, hDC, hpD, hxD⟩ := henclose p hp x hx
  obtain ⟨_, a, r, _, he⟩ := (isOpenDisc_iff_points v hv D).mp hD
  have hpa : v (p-a) < v r := (Set.ext_iff.mp he p).mp hpD
  have hxa : v (x-a) < v r := (Set.ext_iff.mp he x).mp hxD
  have hxp : v (x-p) < v r := by
    have h := v.map_sub_lt hxa hpa
    simpa only [sub_sub_sub_cancel_right] using h
  have hyp : v (y-p) < v r := hy.trans_lt hxp
  have hya : v (y-a) < v r := by
    have h := v.map_add_lt hyp hpa
    simpa only [sub_add_sub_cancel] using h
  exact hDC ((Set.ext_iff.mp he y).mpr hya)

/-- A proper nonempty definable VF set is an open disc if every pair of
its points lies in an open disc contained in that set. -/
theorem isOpenDisc_of_pairs_enclosed (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (C : Set M)
    (hC : GammaParameters.DefinableAtBase B .vf C) (hne : C.Nonempty)
    (hproper : {x : VF M | x.val ∈ C} ≠ Set.univ)
    (henclose : ∀ p : VF M, p.val ∈ C → ∀ q : VF M, q.val ∈ C →
      ∃ D, IsOpenDisc D ∧ D ⊆ C ∧ p.val ∈ D ∧ q.val ∈ D) : IsOpenDisc C := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : IsAlgClosed (VF M) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨z, hz⟩ := hne
  let p : VF M := ⟨z, hC.proper z hz⟩
  have hp : p.val ∈ C := hz
  have hdown := enclosed_downward v hv C henclose p
  let H : AddSubgroup (VF M) := {
    carrier := {x | (x+p).val ∈ C}
    zero_mem' := by
      change (0+p).val ∈ C
      simpa only [zero_add] using hp
    add_mem' := by
      intro x y hx hy
      rcases le_total (v y) (v x) with hxy | hxy
      · apply hdown (x+p) (x+y+p) hp hx
        simpa only [add_sub_cancel_right] using (v.map_add x y).trans (max_le le_rfl hxy)
      · apply hdown (y+p) (x+y+p) hp hy
        simpa only [add_sub_cancel_right] using (v.map_add x y).trans (max_le hxy le_rfl)
    neg_mem' := by
      intro x hx
      apply hdown (x+p) (-x+p) hp hx
      simp only [add_sub_cancel_right, Valuation.map_neg, le_refl] }
  let R : Set M := Subtype.val '' (H : Set (VF M))
  obtain ⟨E, hE⟩ := translated_definable B C hC p
  have hR : IsBall R := GammaParameters.additive_subgroup_isBall_gamma_base h00 E H hE
  have hshift (x : VF M) : (x-p).val ∈ R ↔ x.val ∈ C := by
    constructor
    · rintro ⟨w, hw, he⟩
      have he' : w = x-p := Subtype.ext he
      subst w
      change ((x-p)+p).val ∈ C at hw
      simpa only [sub_add_cancel] using hw
    · intro hx
      refine ⟨x-p, ?_, rfl⟩
      change ((x-p)+p).val ∈ C
      simpa only [sub_add_cancel] using hx
  rcases ball_points_form v hv R hR with hwhole | ⟨a, r, hr, he⟩ | ⟨a, r, he⟩
  · apply False.elim
    apply hproper
    ext x
    exact iff_true_intro ((hshift x).mp ((Set.ext_iff.mp hwhole (x-p)).mpr (Set.mem_univ _)))
  · apply (isOpenDisc_iff_points v hv C).mpr
    refine ⟨fun x hx => hC.proper x hx, a+p, r, hr, ?_⟩
    ext x
    have hh := Set.ext_iff.mp he (x-p)
    have heq : (x-p)-a = x-(a+p) := by ring
    change (x-p).val ∈ R ↔ v ((x-p)-a) < v r at hh
    rw [heq] at hh
    exact (hshift x).symm.trans hh
  · have heC : {x : VF M | x.val ∈ C} = {x | v (x-(a+p)) ≤ v r} := by
      ext x
      have hh := Set.ext_iff.mp he (x-p)
      have heq : (x-p)-a = x-(a+p) := by ring
      change (x-p).val ∈ R ↔ v ((x-p)-a) ≤ v r at hh
      rw [heq] at hh
      exact (hshift x).symm.trans hh
    let c := a+p
    have hc : c.val ∈ C := (Set.ext_iff.mp heC c).mpr (by simp [c])
    have hcr : (c+r).val ∈ C := (Set.ext_iff.mp heC (c+r)).mpr (by simp [c])
    obtain ⟨D, hD, hDC, hcD, hcrD⟩ := henclose c hc (c+r) hcr
    obtain ⟨_, b, s, _, heD⟩ := (isOpenDisc_iff_points v hv D).mp hD
    have hcb : v (c-b) < v s := (Set.ext_iff.mp heD c).mp hcD
    have hcrb : v ((c+r)-b) < v s := (Set.ext_iff.mp heD (c+r)).mp hcrD
    have hrs : v r < v s := by
      have h := v.map_sub_lt hcrb hcb
      have heq : (c+r-b)-(c-b) = r := by ring
      simpa only [heq] using h
    have hnt : ∃ u : VF M, u ≠ 0 ∧ v u < 1 := by
      obtain ⟨u, hu0, hule⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
      refine ⟨u, hu0, ?_⟩
      apply lt_of_not_ge
      intro h
      apply hule
      exact (hv 1 u).mpr (by simpa only [map_one] using h)
    obtain ⟨w, hrw, hws⟩ := Johnson.exists_val_between' v hnt hrs
    have hcwD : (c+w).val ∈ D := by
      apply (Set.ext_iff.mp heD (c+w)).mpr
      have hh := v.map_add_lt hws hcb
      have heq : w+(c-b) = c+w-b := by ring
      rwa [heq] at hh
    have hcwC := hDC hcwD
    have hh := (Set.ext_iff.mp heC (c+w)).mp hcwC
    change v ((c+w)-(a+p)) ≤ v r at hh
    have hwr : v w ≤ v r := by simpa only [c, add_sub_cancel_left] using hh
    exact (not_le_of_gt hrw hwr).elim

end DiamondIntegral.Section2
