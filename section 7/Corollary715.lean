import «section 7».ContractionChoice
import «section 7».BlowupResults
import «section 7».LiftClasses
import «section 6».DiamondStandardContraction

/-! Corollary 7.15 (`contraction:same:perm:isp`): the reduction to fibres.

The paper's proof applies Lemma 7.13 at good points of the fibres and then
Lemma 7.14 with head start `1` to the sets obtained by contracting the
coordinate `i = σ(1)`. Section 6's standard contractions begin with a
zero-centred normalization of all coordinates, which shifts the first-stage sets
by the centre (GAP-REPAIRS 11). The formal proof avoids the mismatch as follows.

1. **Independence of the centre.** Lemma 7.14 with `A' = A''` and head start `0`
   (the fibres are equal) gives `μIsp^db` between any two standard contractions
   of one object in the same order (`ispRel_same_set`).
2. **A common centre.** Choose contractions `G'₀`, `G''₀` of `A'`, `A''` with the
   same centre (`ContractionChoice.exists_common_center`). Their first-stage sets
   then have the same VF projection (`firstSet_vf_iff`), because the morphism
   fixes the coordinates other than `i` (`proj_of_relativelyUnary`).
3. **Normalized contractions of the first-stage sets.** Take contractions `H'`,
   `H''` of the first-stage sets in the identity order. Lemma 7.14 with head
   start `1` relates their classes, given the fibre hypothesis
   (`FibreHypothesis`).
4. **Grafting.** `graftRest G'₀ H'` is a standard contraction of `A'` whose
   head-start-`0` class is the head-start-`1` class of `H'`
   (`ContractionChoice.cls_graftRest`). Combining with step 1 gives the
   corollary (`reduction_7_15`).

The fibre hypothesis is the content of steps 2–4 of the Lean plan (good points,
Lemma 7.13 at a good point, base extension). It is proved separately. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Corollary715
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.LiftClasses

/-! ### `μIsp^db` in every degree is an equivalence relation -/

section Relation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : GammaParameters.Base (M := M)}

theorem ispRel_refl {m : ℕ} (x : Cls B m) : IspRel x x := by
  by_cases hm : m = 0
  · rw [IspRel, dif_pos hm]
  · rw [IspRel, dif_neg hm]
    exact BlowupCongruence.muIsp_refl _

theorem ispRel_symm {m : ℕ} {x y : Cls B m} (h : IspRel x y) : IspRel y x := by
  by_cases hm : m = 0
  · rw [IspRel, dif_pos hm] at h ⊢
    exact h.symm
  · rw [IspRel, dif_neg hm] at h ⊢
    exact BlowupCongruence.muIsp_symm h

theorem ispRel_trans {m : ℕ} {x y z : Cls B m} (h₁ : IspRel x y) (h₂ : IspRel y z) : IspRel x z := by
  by_cases hm : m = 0
  · rw [IspRel, dif_pos hm] at h₁ h₂ ⊢
    exact h₁.trans h₂
  · rw [IspRel, dif_neg hm] at h₁ h₂ ⊢
    exact BlowupResults.muIsp_transitive h₁ h₂

theorem ispRel_of_eq {m : ℕ} {x y : Cls B m} (h : x = y) : IspRel x y := h ▸ ispRel_refl x

end Relation

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-! ### Level sets and finite fibres -/

section Levels
variable {S : Set M}

include hv in
/-- The form of an object of `μVF^◇` has open level sets. -/
theorem object_levels {n : ℕ} (A : VFObject (M := M) S n) :
    ∀ u γ, IsOpen {a : Fin n → VF M | (a, u) ∈ A.carrier.carrier ∧ gammaFormExtension A.form (a, u) = γ} := by
  intro u γ
  have he : {a : Fin n → VF M | (a, u) ∈ A.carrier.carrier ∧ gammaFormExtension A.form (a, u) = γ} =
      vfFibre (A.levelSet γ) u := by
    ext a
    constructor
    · rintro ⟨ha, hγ⟩
      exact ⟨ha, (gammaFormExtension_at A.form ⟨(a, u), ha⟩).symm.trans hγ⟩
    · rintro ⟨ha, hγ⟩
      exact ⟨ha, (gammaFormExtension_at A.form ⟨(a, u), ha⟩).trans hγ⟩
  rw [he]
  exact ((A.levelSet_geometry γ).clopen_fibres hv u).isOpen

variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n + 1))}

include h00 hc hκ hs hv in
/-- The prepared form of a normalized contraction has open level sets. -/
theorem preparedForm_levels (linear : GammaPiecewiseRationalAffineInput (M := M))
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (hLevels : ∀ u γ, IsOpen {a : Fin (n + 1) → VF M | (a, u) ∈ A.carrier ∧ gammaFormExtension ω (a, u) = γ})
    (F : NormalizedMeasuredContraction (G := G) A ω e) :
    ∀ u γ, IsOpen {a : Fin (n + 1) → VF M | (a, u) ∈ (reindexedVFSet F.normalization.map.image e).carrier ∧
      gammaFormExtension F.preparedForm (a, u) = γ} := by
  let D := F.normalization
  let d := D.bijection
  have hd : SpecialCovariantChain (G := G) A D.map.image d := .zeroCentered A D
  let η := ω.comp (d.inverse (D.bijective h00))
  have hTransportD (p : A) : (η (d p)).val = (ω p).val := by
    change (ω (d.inverse (D.bijective h00) (d p))).val = _
    rw [Map.inverse_apply]
  have hLevelsD := hd.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels η hTransportD
  let E := vfRelabeling D.map.image e
  let θ := η.comp (E.inverse (vfRelabeling_bijective D.map.image e))
  have hLevelsE := vfRelabeling_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ D.map.image e
    (D.image_properInvariant h00 hc hκ hs hv) η hLevelsD
  have hval (y : reindexedVFSet D.map.image e) : (F.preparedForm y).val = (θ y).val := by
    obtain ⟨z, rfl⟩ := (vfRelabeling_bijective D.map.image e).surjective y
    obtain ⟨p, rfl⟩ := (D.bijective h00).surjective z
    refine (F.transport p).trans ?_
    change (ω p).val = (η (E.inverse (vfRelabeling_bijective D.map.image e) (E (d p)))).val
    rw [Map.inverse_apply]
    exact (hTransportD p).symm
  intro u γ
  convert hLevelsE u γ using 1
  ext a
  constructor
  · rintro ⟨ha, hγ⟩
    refine ⟨ha, ?_⟩
    rw [gammaFormExtension_at θ ⟨(a, u), ha⟩, ← hval, ← gammaFormExtension_at F.preparedForm ⟨(a, u), ha⟩]
    exact hγ
  · rintro ⟨ha, hγ⟩
    refine ⟨ha, ?_⟩
    rw [gammaFormExtension_at F.preparedForm ⟨(a, u), ha⟩, hval, ← gammaFormExtension_at θ ⟨(a, u), ha⟩]
    exact hγ

include hc h00 hκ hs in
/-- The prepared set of a normalized contraction has finite RV fibres when the
source has. -/
theorem prepared_finite (hsmall : Cardinal.mk S < κ) (F : NormalizedMeasuredContraction (G := G) A ω e)
    (hA : ∀ a : Fin (n + 1) → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier}.Finite) :
    ∀ a : Fin (n + 1) → VF M,
      {u | (a, u) ∈ (reindexedVFSet F.normalization.map.image e).carrier}.Finite :=
  finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall
    ((vfRelabeling F.normalization.map.image e).comp F.normalization.bijection)
    ((vfRelabeling_bijective _ e).comp (F.normalization.bijective h00)) hA

end Levels

/-! ### VF projections of first-stage sets -/

section Projection
variable {S : Set M}

/-- The zero-centred normalization of one coordinate. -/
def tau (c x : VF M) : VF M := x + if vfValue c < vfValue x then c else 0

theorem point_fst {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} (D : ZeroCenteredData A)
    (p : Mixed M n r) (k : Fin n) : (D.point p).1 k = tau D.center (p.1 k) := by
  simp only [ZeroCenteredData.point, ZeroCenteredData.shift, ZeroCenteredData.core, Pi.add_apply, tau,
    decide_eq_true_eq]

variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n + 1 + 1))}

theorem stage_relative (F : NormalizedMeasuredContraction (G := G) A ω e)
    (q : reindexedVFSet F.normalization.map.image e) (j : Fin (n + 1)) :
    ((headStage F.preparedContraction.data.program).lift q).val.1 j.castSucc = q.val.1 j.castSucc :=
  (headStage F.preparedContraction.data.program).relative q j

/-- The VF projection of the first-stage set of a normalized contraction. -/
theorem firstSet_vf (F : NormalizedMeasuredContraction (G := G) A ω e) (b : Fin (n + 1) → VF M) :
    (∃ u, (b, u) ∈ (headStage F.preparedContraction.data.program).contracted.carrier) ↔
      ∃ p ∈ A.carrier, ∀ j, b j = tau F.normalization.center (p.1 (e j.castSucc)) := by
  let H := headStage F.preparedContraction.data.program
  let D := F.normalization
  constructor
  · rintro ⟨u, t, ht⟩
    have ht' : (vfDropLast H.target t).val = (b, u) := ht
    obtain ⟨q, rfl⟩ := H.home.bijective.surjective t
    have hq := (mem_reindexedVFSet D.map.image e q.val).mp q.property
    rw [D.image_carrier] at hq
    obtain ⟨p, hp, hpq⟩ := hq
    refine ⟨p, hp, fun j => ?_⟩
    have hb : b j = (H.lift q).val.1 j.castSucc := by
      rw [vfDropLast_apply] at ht'
      exact (congrFun (congrArg Prod.fst ht') j).symm
    rw [hb, stage_relative F q j, ← point_fst D p (e j.castSucc), hpq]
    change q.val.1 j.castSucc = q.val.1 (e.symm (e j.castSucc))
    rw [Equiv.symm_apply_apply]
  · rintro ⟨p, hp, hb⟩
    let y := vfRelabeling D.map.image e (D.bijection ⟨p, hp⟩)
    refine ⟨(H.lift y).val.2, H.lift y, ?_⟩
    show (vfDropLast H.target (H.lift y)).val = (b, (H.lift y).val.2)
    rw [vfDropLast_apply]
    congr 1
    funext j
    change (H.lift y).val.1 j.castSucc = b j
    rw [stage_relative F y j, hb j]
    change (D.point p).1 (e j.castSucc) = _
    rw [point_fst]

/-- First-stage sets of normalized contractions with a common centre have the
same VF projection when the sources have the same projection away from the
first contracted coordinate. -/
theorem firstSet_vf_iff {r' r'' : ℕ} {A' : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r') S}
    {A'' : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r'') S}
    {ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) S)}
    {ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F' : NormalizedMeasuredContraction (G := G) A' ω' e) (F'' : NormalizedMeasuredContraction (G := G) A'' ω'' e)
    (hcen : F'.normalization.center = F''.normalization.center)
    (hP : ∀ b : Fin (n + 1) → VF M, (∃ p ∈ A'.carrier, ∀ j, b j = p.1 (e j.castSucc)) ↔
      (∃ p ∈ A''.carrier, ∀ j, b j = p.1 (e j.castSucc))) (b : Fin (n + 1) → VF M) :
    (∃ u, (b, u) ∈ (headStage F'.preparedContraction.data.program).contracted.carrier) ↔
      (∃ v, (b, v) ∈ (headStage F''.preparedContraction.data.program).contracted.carrier) := by
  rw [firstSet_vf F' b, firstSet_vf F'' b, hcen]
  constructor
  · rintro ⟨p, hp, hb⟩
    obtain ⟨q, hq, hpq⟩ := (hP (fun j => p.1 (e j.castSucc))).mp ⟨p, hp, fun _ => rfl⟩
    exact ⟨q, hq, fun j => (hb j).trans (congrArg _ (hpq j))⟩
  · rintro ⟨q, hq, hb⟩
    obtain ⟨p, hp, hpq⟩ := (hP (fun j => q.1 (e j.castSucc))).mpr ⟨q, hq, fun _ => rfl⟩
    exact ⟨p, hp, fun j => (hb j).trans (congrArg _ (hpq j))⟩

/-- A morphism fixing every coordinate except `i = e(last)` preserves the
projection away from `i`. -/
theorem proj_of_relativelyUnary {A' A'' : VFObject (M := M) S (n + 1 + 1)} (F : Morphism G A' A'')
    (hF : VFRelativelyUnary F.map (e (Fin.last (n + 1))) (e (Fin.last (n + 1)))) (b : Fin (n + 1) → VF M) :
    (∃ p ∈ A'.carrier.carrier, ∀ j, b j = p.1 (e j.castSucc)) ↔
      (∃ p ∈ A''.carrier.carrier, ∀ j, b j = p.1 (e j.castSucc)) := by
  have hfix (p : A'.carrier) (j : Fin (n + 1)) : (F.map p).val.1 (e j.castSucc) = p.val.1 (e j.castSucc) := by
    have hne : e j.castSucc ≠ e (Fin.last (n + 1)) := fun h => Fin.castSucc_ne_last j (e.injective h)
    rw [hF p (e j.castSucc) hne, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨p, hp, hb⟩
    exact ⟨(F.map ⟨p, hp⟩).val, (F.map ⟨p, hp⟩).property, fun j => (hb j).trans (hfix ⟨p, hp⟩ j).symm⟩
  · rintro ⟨q, hq, hb⟩
    obtain ⟨p, hp⟩ := F.bijective.surjective ⟨q, hq⟩
    refine ⟨p.val, p.property, fun j => (hb j).trans ?_⟩
    rw [← hfix p j, hp]

end Projection

/-! ### Fibres of degree `0` and independence of the centre -/

section Centre
variable {T : LRV.Substructure M}

theorem fibreObject_zero_doublyBounded {m r : ℕ} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
    (hA : ProperInvariant (T : Set M) A.carrier) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (a : Fin m → VF M)
    (hFin : ∀ t : Fin 0 → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ Fin.elim0 = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i : Fin 0, (p.2 (Fin.elim0 i)).val ≠ iRVZero) :
    (fibreObject T A ω a Fin.elim0 hFin hNZ).doublyBounded := by
  obtain ⟨γ, hγ⟩ := hA.rvBounded
  refine ⟨⟨γ, fun u hu i => hγ (a, u) ((mem_fibreDomain A a u).mp hu) i⟩, ⟨1, fun _ _ i => i.elim0⟩⟩

variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include V hV hVT hTV hnt in
/-- **Independence of the centre.** Any two standard contractions of one object,
in the same order, are `μIsp^db`-related: Lemma 7.14 with equal sets and head
start `0`. -/
theorem ispRel_same_set (h714 : Lemma714 M G) {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1))
    {e : Equiv.Perm (Fin (n + 1))} (F₁ F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    IspRel (cls (objOf hc T (F₁.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A Fin.elim0)) (F₁.headStartObject_doublyBounded 0 Fin.elim0)))
      (cls (objOf hc T (F₂.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A Fin.elim0)) (F₂.headStartObject_doublyBounded 0 Fin.elim0))) :=
  h714 hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ A.carrier A.carrier A.form A.form A.proper A.proper
    (fun _ => Iff.rfl) Fin.elim0 Fin.elim0 (object_hFin A Fin.elim0) (object_hFin A Fin.elim0)
    (fun _ _ i => i.elim0) (fun _ _ i => i.elim0)
    (fun a _ => ⟨fibreObject_zero_doublyBounded A.carrier A.proper A.form a _ _,
      fibreObject_zero_doublyBounded A.carrier A.proper A.form a _ _, ispRel_refl _⟩) F₁ F₂

end Centre

/-! ### The reduction -/

section Reduction
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} {e : Equiv.Perm (Fin (n + 1 + 1))}

include hc h00 hκ hs hsmall in
/-- Finite fibres over the leading label on the first-stage set of a contraction
of an object. -/
theorem firstFin {A : VFObject (M := M) (T : Set M) (n + 1 + 1)}
    (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    ∀ (b : Fin (n + 1) → VF M) (t : Fin 1 → RVInfinity M),
      {u | (b, u) ∈ (firstSet G₀).carrier ∧ u ∘ ![(stage G₀).leading] = t}.Finite :=
  firstStage_finite h00 hc hκ hs hsmall G₀.preparedContraction.data
    (prepared_finite hc h00 hκ hs hsmall G₀ A.finiteRV)

/-- **The fibre hypothesis** of Corollary 7.15 for chosen contractions `G'₀`,
`G''₀`: over every point `a` of the first-stage VF projection, the fibres of the
first-stage sets, with the leading label as head-start label, are
`μIsp^db`-related over `S⟨a⟩`. -/
def FibreHypothesis {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)}
    (G'₀ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
    (G''₀ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e) : Prop :=
  ∀ a : Fin (n + 1) → VF M, (∃ u, (a, u) ∈ (firstSet G'₀).carrier) →
    ∃ (hU' : (fibreObject T (firstSet G'₀) (firstForm G'₀) a ![(stage G'₀).leading]
        (firstFin hc h00 hκ hs hsmall G'₀ a) (firstStage_nonzero G'₀.preparedContraction.data)).doublyBounded)
      (hU'' : (fibreObject T (firstSet G''₀) (firstForm G''₀) a ![(stage G''₀).leading]
        (firstFin hc h00 hκ hs hsmall G''₀ a) (firstStage_nonzero G''₀.preparedContraction.data)).doublyBounded),
      IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU''))

include V hV hVT hTV hnt in
/-- **Corollary 7.15, reduction to fibres.** For contractions `G'₀`, `G''₀` of
`A'`, `A''` with a common centre, whose sources have the same projection away
from `i = e(last)`, the fibre hypothesis implies `μIsp^db` between any standard
contractions `F'`, `F''` of `A'`, `A''` in the order `e`. -/
theorem reduction_7_15 (h714 : Lemma714 M G) {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)}
    (hP : ∀ b : Fin (n + 1) → VF M, (∃ p ∈ A'.carrier.carrier, ∀ j, b j = p.1 (e j.castSucc)) ↔
      (∃ p ∈ A''.carrier.carrier, ∀ j, b j = p.1 (e j.castSucc)))
    (G'₀ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
    (G''₀ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e)
    (hcen : G'₀.normalization.center = G''₀.normalization.center)
    (hFibre : FibreHypothesis hc h00 hκ hs hsmall G'₀ G''₀)
    (F' : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
    (F'' : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e) :
    IspRel (cls (objOf hc T (F'.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A' Fin.elim0)) (F'.headStartObject_doublyBounded 0 Fin.elim0)))
      (cls (objOf hc T (F''.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A'' Fin.elim0)) (F''.headStartObject_doublyBounded 0 Fin.elim0))) := by
  have hLev' := restForm_levels hv G'₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A') G'₀)
  have hLev'' := restForm_levels hv G''₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A'') G''₀)
  obtain ⟨H'⟩ := measured_contraction_any_order (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt
    (firstSet G'₀) (stage G'₀).contracted_proper (firstForm G'₀) hLev' 1
  obtain ⟨H''⟩ := measured_contraction_any_order (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt
    (firstSet G''₀) (stage G''₀).contracted_proper (firstForm G''₀) hLev'' 1
  have hmid := h714 hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ (firstSet G'₀) (firstSet G''₀)
    (firstForm G'₀) (firstForm G''₀) (stage G'₀).contracted_proper (stage G''₀).contracted_proper
    (firstSet_vf_iff G'₀ G''₀ hcen hP) ![(stage G'₀).leading] ![(stage G''₀).leading]
    (firstFin hc h00 hκ hs hsmall G'₀) (firstFin hc h00 hκ hs hsmall G''₀)
    (firstStage_nonzero G'₀.preparedContraction.data) (firstStage_nonzero G''₀.preparedContraction.data)
    hFibre H' H''
  have h1 := cls_graftRest h00 hc lin hκ hs hv hsmall hΓ G'₀ H' (object_hFin A' Fin.elim0)
    (firstFin hc h00 hκ hs hsmall G'₀)
  have h2 := cls_graftRest h00 hc lin hκ hs hv hsmall hΓ G''₀ H'' (object_hFin A'' Fin.elim0)
    (firstFin hc h00 hκ hs hsmall G''₀)
  have hl := ispRel_same_set hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A' F'
    (graftRest h00 hc lin hκ hs hv hsmall hΓ G'₀ H')
  have hr := ispRel_same_set hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A''
    (graftRest h00 hc lin hκ hs hv hsmall hΓ G''₀ H'') F''
  exact ispRel_trans hl (ispRel_trans (ispRel_of_eq h1)
    (ispRel_trans hmid (ispRel_trans (ispRel_of_eq h2.symm) hr)))

end Reduction

end DiamondIntegral.Section7.Corollary715
