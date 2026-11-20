import «section 7».Lemma714HsChart

/-! Lemma 7.14, part 29: identification of the descended objects.

`Frozen P` bundles the freezing of the VF projection `P`: the base preparation
`Φ₀ : P → B₀`, the frozen focus data `F` on `B₀`, the frozen chain
`f : B₀ → Bk` and the regularized target `Bk^reg`, with `Φ = fReg f ∘ Φ₀`. A
unary set `A` over `P` with form `ω` is guarded by the freezing (`Guards`) when
the image of `Φ₀ ⋉ A` and the level sets of its form are coordinate products on
the frozen balls.

For a guarded `A` whose fibre family has constant rows on key classes:
* rows and forms of `A` agree at points of `P` with the same key (`class_rows`,
  `class_forms`);
* the frozen set `Φ ⋉ A` is a head-start chain set (`frHGood`);
* **the descended indexed object of the recoded fibre family has the head-start
  class of `Φ ⋉ A`** (`cls_ind_eq_clsH`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section6
open DiamondIntegral.Section7.Lemma714Prod DiamondIntegral.Section7.Lemma714Schema DiamondIntegral.Section7.Lemma714Head
open DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {T : LRV.Substructure M}

omit hM in
theorem rvValues_fin_append {a b : ℕ} (u : Fin a → RVInfinity M) (t : Fin b → RVInfinity M) :
    rvValues (Fin.append u t) = Fin.append (rvValues u) (rvValues t) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [rvValues]

/-- **The frozen preparation of the VF projection `P`.** -/
structure Frozen (P : DefSet (rawMixedSpace (M := M) 1 0) (T : Set M)) where
  s : ℕ
  B₀ : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)
  Φ₀ : Map P B₀
  bij₀ : Function.Bijective Φ₀
  F : FMT.FocusFreezingData B₀
  sk : ℕ
  Bk : DefSet (rawMixedSpace (M := M) 1 sk) (T : Set M)
  f : Map B₀ Bk
  bijk : Function.Bijective f
  rvBounded : RVSupportDoublyBounded (regT Bk).carrier
  pullback : IsRVPullback (regT Bk).carrier
  finite : ∀ y : Fin 1 → VF M, {u : Fin (1 + sk) → RVInfinity M | (y, u) ∈ (regT Bk).carrier}.Finite
  vfBounded : VFDoublyBounded (regT Bk).carrier
  homeo : ProperCovariantHomeomorphism (G := G) ((fReg f).comp Φ₀)

namespace Frozen
variable {P : DefSet (rawMixedSpace (M := M) 1 0) (T : Set M)} (Z : Frozen (G := G) P)

/-- The full frozen map `P → Bk^reg`. -/
abbrev Φ : Map P (regT Z.Bk) := (fReg Z.f).comp Z.Φ₀

theorem bijR : Function.Bijective (fReg Z.f) := (regularization_bijective Z.Bk).comp Z.bijk

theorem bij : Function.Bijective Z.Φ := Z.bijR.comp Z.bij₀

/-- The inverse of `fReg f`. -/
abbrev ρ : Map (regT Z.Bk) Z.B₀ := (fReg Z.f).inverse Z.bijR

theorem fReg_ρ (q : regT Z.Bk) : fReg Z.f (Z.ρ q) = q := Map.apply_inverse _ _ _

theorem Φ_inverse (q : regT Z.Bk) : Z.Φ.inverse Z.bij q = Z.Φ₀.inverse Z.bij₀ (Z.ρ q) := by
  apply Z.bij.1
  rw [Map.apply_inverse]
  change q = fReg Z.f (Z.Φ₀ (Z.Φ₀.inverse Z.bij₀ (Z.ρ q)))
  rw [Map.apply_inverse, Z.fReg_ρ]

variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- The key relation of the freezing. -/
abbrev K : KeyRel (⟨(T : Set M), ∅⟩ : Base (M := M)) (rvs (1 + Z.sk)) (vfs 1) :=
  keyRel Z.f (Z.Φ₀.inverse Z.bij₀) Z.F hc

/-- The key set of the freezing. -/
abbrev Q : KeySet (⟨(T : Set M), ∅⟩ : Base (M := M)) (1 + Z.sk) :=
  keySet Z.Bk hc Z.rvBounded Z.pullback Z.finite

theorem K_mk (p : Z.B₀) :
    (Z.K hc).R (rvValues (fReg Z.f p).val.2) (vfValues (Z.Φ₀.inverse Z.bij₀ (frz Z.F p)).val.1) :=
  keyRel_mk Z.f (Z.Φ₀.inverse Z.bij₀) Z.F hc p

theorem K_mk_ρ (q : regT Z.Bk) :
    (Z.K hc).R (rvValues q.val.2) (vfValues (Z.Φ₀.inverse Z.bij₀ (frz Z.F (Z.ρ q))).val.1) := by
  have h := Z.K_mk hc (Z.ρ q)
  rw [Z.fReg_ρ] at h
  exact h

end Frozen

/-! ### Guarded sets -/

section Side
variable {P : DefSet (rawMixedSpace (M := M) 1 0) (T : Set M)} (Z : Frozen (G := G) P)
  (hc : CanonicalStructure.IsCanonical (M := M)) {r k : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
  (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (π : Fin k → Fin r) (N : ℕ)
  (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)

/-- `A` and its form are protected by the freezing. -/
structure Guards : Prop where
  rows : ∀ D : Z.F.balls,
    FMT.CoordinateProductDomain (prodMap Z.Φ₀ hAP).image.carrier (FMT.vfOpenBall D.val) (Z.F.centers D) 0
  forms : ∀ γ, ∀ D : Z.F.balls, FMT.CoordinateProductDomain
    {p | p ∈ (prodMap Z.Φ₀ hAP).image.carrier ∧ gammaFormExtension (prodForm Z.Φ₀ Z.bij₀ hAP ω) p = γ}
    (FMT.vfOpenBall D.val) (Z.F.centers D) 0

theorem form_congr {a a' : Fin 1 → VF M} {t : Fin r → RVInfinity M} (e : a = a') (h : (a, t) ∈ A.carrier)
    (h' : (a', t) ∈ A.carrier) : ω ⟨(a, t), h⟩ = ω ⟨(a', t), h'⟩ := by
  subst e
  rfl

variable {Z ω hAP}

theorem frozen_rows (hG : Guards Z ω hAP) (p₀ : Z.B₀) (t : Fin r → RVInfinity M) :
    ((Z.Φ₀.inverse Z.bij₀ p₀).val.1, t) ∈ A.carrier ↔
      ((Z.Φ₀.inverse Z.bij₀ (frz Z.F p₀)).val.1, t) ∈ A.carrier := by
  rw [← mem_prodImage_iff Z.Φ₀ Z.bij₀ hAP p₀ t, ← mem_prodImage_iff Z.Φ₀ Z.bij₀ hAP (frz Z.F p₀) t, frz_val]
  exact freeze_mem_iff Z.F hG.rows _

theorem frozen_forms (hG : Guards Z ω hAP) (p₀ : Z.B₀) (t : Fin r → RVInfinity M)
    (h : ((Z.Φ₀.inverse Z.bij₀ p₀).val.1, t) ∈ A.carrier)
    (h' : ((Z.Φ₀.inverse Z.bij₀ (frz Z.F p₀)).val.1, t) ∈ A.carrier) : ω ⟨_, h⟩ = ω ⟨_, h'⟩ := by
  have hm := (mem_prodImage_iff Z.Φ₀ Z.bij₀ hAP p₀ t).mpr h
  have hm' := (mem_prodImage_iff Z.Φ₀ Z.bij₀ hAP (frz Z.F p₀) t).mpr h'
  let θ := prodForm Z.Φ₀ Z.bij₀ hAP ω
  have hlev := (freeze_mem_iff Z.F (hG.forms (gammaFormExtension θ (p₀.val.1, Fin.append p₀.val.2 t)))
    (p₀.val.1, Fin.append p₀.val.2 t)).mp ⟨hm, rfl⟩
  have he : gammaFormExtension θ ((frz Z.F p₀).val.1, Fin.append (frz Z.F p₀).val.2 t) =
      gammaFormExtension θ (p₀.val.1, Fin.append p₀.val.2 t) := by
    rw [frz_val]
    exact hlev.2
  have e1 : gammaFormExtension θ ((frz Z.F p₀).val.1, Fin.append (frz Z.F p₀).val.2 t) = (θ ⟨_, hm'⟩).val :=
    gammaFormExtension_at θ ⟨_, hm'⟩
  have e2 : gammaFormExtension θ (p₀.val.1, Fin.append p₀.val.2 t) = (θ ⟨_, hm⟩).val :=
    gammaFormExtension_at θ ⟨_, hm⟩
  rw [e1, e2] at he
  rw [← prodForm_at Z.Φ₀ Z.bij₀ hAP ω p₀ t hm h, ← prodForm_at Z.Φ₀ Z.bij₀ hAP ω (frz Z.F p₀) t hm' h']
  exact (Subtype.ext he).symm

variable (Z ω)

/-- Row constancy of the fibre family on the key classes of the freezing. -/
def FamRowConst : Prop := ∀ x, (famSchema hc A ω π N).RowConst (Z.K hc) x

variable {Z ω}

theorem frozen_class_rows (hRC : FamRowConst Z hc ω π N) (p p' : Z.B₀)
    (hl : (fReg Z.f p).val.2 = (fReg Z.f p').val.2) (t : Fin r → RVInfinity M) :
    ((Z.Φ₀.inverse Z.bij₀ (frz Z.F p)).val.1, t) ∈ A.carrier ↔
      ((Z.Φ₀.inverse Z.bij₀ (frz Z.F p')).val.1, t) ∈ A.carrier := by
  have hK' := Z.K_mk hc p'
  rw [← hl] at hK'
  have h : rvValues t ∈ (famSchema hc A ω π N).row (vfValues (Z.Φ₀.inverse Z.bij₀ (frz Z.F p)).val.1) ↔
      rvValues t ∈ (famSchema hc A ω π N).row (vfValues (Z.Φ₀.inverse Z.bij₀ (frz Z.F p')).val.1) :=
    (hRC _).1 _ _ (Z.K_mk hc p) hK' (rvValues t)
  rw [famSchema_mem_row, famSchema_mem_row] at h
  constructor
  · intro ht
    obtain ⟨t', ht', he⟩ := h.mp ⟨t, ht, rfl⟩
    rwa [rvValues_injective he] at ht'
  · intro ht
    obtain ⟨t', ht', he⟩ := h.mpr ⟨t, ht, rfl⟩
    rwa [rvValues_injective he] at ht'

theorem frozen_class_forms (hRC : FamRowConst Z hc ω π N) (p p' : Z.B₀)
    (hl : (fReg Z.f p).val.2 = (fReg Z.f p').val.2) (t : Fin r → RVInfinity M)
    (h : ((Z.Φ₀.inverse Z.bij₀ (frz Z.F p)).val.1, t) ∈ A.carrier)
    (h' : ((Z.Φ₀.inverse Z.bij₀ (frz Z.F p')).val.1, t) ∈ A.carrier) : ω ⟨_, h⟩ = ω ⟨_, h'⟩ := by
  have hK' := Z.K_mk hc p'
  rw [← hl] at hK'
  obtain ⟨c, hc0, hcv⟩ := EndpointLogic.codeValue_surjective (gammaMapValue ω ⟨_, h⟩)
  have h1 : (famSchema hc A ω π N).volRow (vfValues (Z.Φ₀.inverse Z.bij₀ (frz Z.F p)).val.1) (rvValues t) c :=
    (famSchema_volRow hc A ω π N _ t h c).mpr ⟨hc0, hcv⟩
  have h2 : (famSchema hc A ω π N).volRow (vfValues (Z.Φ₀.inverse Z.bij₀ (frz Z.F p')).val.1) (rvValues t) c :=
    ((hRC _).2.2 _ _ (Z.K_mk hc p) hK' (rvValues t) (fun _ => c)).mp h1
  have h3 := ((famSchema_volRow hc A ω π N _ t h' c).mp h2).2
  exact Subtype.ext (hcv.symm.trans h3)

/-- **Rows of `A` agree at points of `P` with the same key.** -/
theorem class_rows (hG : Guards Z ω hAP) (hRC : FamRowConst Z hc ω π N) (q₁ q₂ : regT Z.Bk)
    (hu : q₁.val.2 = q₂.val.2) (t : Fin r → RVInfinity M) :
    ((Z.Φ.inverse Z.bij q₁).val.1, t) ∈ A.carrier ↔ ((Z.Φ.inverse Z.bij q₂).val.1, t) ∈ A.carrier := by
  rw [Z.Φ_inverse, Z.Φ_inverse, frozen_rows hG (Z.ρ q₁) t, frozen_rows hG (Z.ρ q₂) t]
  exact frozen_class_rows hc π N hRC (Z.ρ q₁) (Z.ρ q₂) (by rw [Z.fReg_ρ, Z.fReg_ρ]; exact hu) t

/-- **Forms of `A` agree at points of `P` with the same key.** -/
theorem class_forms (hG : Guards Z ω hAP) (hRC : FamRowConst Z hc ω π N) (q₁ q₂ : regT Z.Bk)
    (hu : q₁.val.2 = q₂.val.2) (t : Fin r → RVInfinity M)
    (h₁ : ((Z.Φ.inverse Z.bij q₁).val.1, t) ∈ A.carrier) (h₂ : ((Z.Φ.inverse Z.bij q₂).val.1, t) ∈ A.carrier) :
    ω ⟨_, h₁⟩ = ω ⟨_, h₂⟩ := by
  have e₁ : (Z.Φ.inverse Z.bij q₁).val.1 = (Z.Φ₀.inverse Z.bij₀ (Z.ρ q₁)).val.1 := by rw [Z.Φ_inverse]
  have e₂ : (Z.Φ.inverse Z.bij q₂).val.1 = (Z.Φ₀.inverse Z.bij₀ (Z.ρ q₂)).val.1 := by rw [Z.Φ_inverse]
  have k₁ : ((Z.Φ₀.inverse Z.bij₀ (Z.ρ q₁)).val.1, t) ∈ A.carrier := e₁ ▸ h₁
  have k₂ : ((Z.Φ₀.inverse Z.bij₀ (Z.ρ q₂)).val.1, t) ∈ A.carrier := e₂ ▸ h₂
  have f₁ := (frozen_rows hG _ t).mp k₁
  have f₂ := (frozen_rows hG _ t).mp k₂
  rw [form_congr ω e₁ h₁ k₁, frozen_forms hG _ t k₁ f₁,
    frozen_class_forms hc π N hRC (Z.ρ q₁) (Z.ρ q₂) (by rw [Z.fReg_ρ, Z.fReg_ρ]; exact hu) t f₁ f₂,
    ← frozen_forms hG _ t k₂ f₂, ← form_congr ω e₂ h₂ k₂]

/-! ### The frozen set -/

/-- A point of the image of `g ⋉ A`. -/
theorem mem_prodImage_split {s' : ℕ} {Q' : DefSet (rawMixedSpace (M := M) 1 s') (T : Set M)} (g : Map P Q')
    (hg : Function.Bijective g) {y : Mixed M 1 (s' + r)} (hy : y ∈ (prodMap g hAP).image.carrier) :
    ∃ (q : Q') (t : Fin r → RVInfinity M), y = (q.val.1, Fin.append q.val.2 t) ∧
      ((g.inverse hg q).val.1, t) ∈ A.carrier := by
  obtain ⟨a, rfl⟩ := hy
  refine ⟨g (baseMap hAP a), a.val.2, prodMap_apply g hAP a, ?_⟩
  rw [Map.inverse_apply, baseMap_apply]
  exact a.property

variable (Z ω hAP)

theorem frTagged : ∀ p ∈ (prodMap Z.Φ hAP).image.carrier, ∀ q ∈ (prodMap Z.Φ hAP).image.carrier,
    p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  obtain ⟨q₁, t₁, rfl, -⟩ := mem_prodImage_split Z.Φ Z.bij hp
  obtain ⟨q₂, t₂, rfl, -⟩ := mem_prodImage_split Z.Φ Z.bij hq
  exact SpecialChains.regularize_tagged Z.Bk q₁.val q₁.property q₂.val q₂.property (appendInj.mp he).1

variable {κ : Cardinal} (h00 : M ⊨ Axioms.ACVF00) (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hA : ProperInvariant (T : Set M) A.carrier)
  (hFin : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)

/-- **The frozen set `Φ ⋉ A` is a head-start chain set.** -/
def frHGood (hG : Guards Z ω hAP) (hRC : FamRowConst Z hc ω π N) :
    HGood (prodMap Z.Φ hAP).image (Fin.natAdd (1 + Z.sk) ∘ π) where
  pullback := by
    apply Set.Subset.antisymm _ (subset_rvHull _)
    intro y hy
    obtain ⟨p, hp, hVF, hRV⟩ := (mem_rvHull_iff _ y).mp hy
    obtain ⟨q₁, t, rfl, ht⟩ := mem_prodImage_split Z.Φ Z.bij hp
    have hq₂ : ((y.1, q₁.val.2) : Mixed M 1 (1 + Z.sk)) ∈ (regT Z.Bk).carrier :=
      rvPullback_mem_of_sameRV Z.pullback q₁.property hVF rfl
    let q₂ : regT Z.Bk := ⟨_, hq₂⟩
    have e : y = (q₂.val.1, Fin.append q₂.val.2 t) := Prod.ext rfl hRV.symm
    rw [e, mem_prodImage_iff Z.Φ Z.bij hAP q₂ t]
    exact (class_rows hc π N hG hRC q₁ q₂ rfl t).mp ht
  finite := unbundle_finite (head_start_finite_rv_fibres_of_bijective hc h00 hκ.le hs hsmall (prodMap Z.Φ hAP).toImage
    (prodMap_toImage_bijective Z.Φ Z.bij hAP) k π (Fin.natAdd (1 + Z.sk) ∘ π)
    (fun p i => prodMap_labels Z.Φ hAP p (π i)) hFin)
  vfBounded := by
    obtain ⟨γ, hγ⟩ := Z.vfBounded
    refine ⟨γ, fun y hy i => ?_⟩
    obtain ⟨q, t, rfl, -⟩ := mem_prodImage_split Z.Φ Z.bij hy
    exact hγ q.val q.property i
  rvBounded := (prodMap_image_properInvariant Z.Φ hAP hv h00 hc hκ hs Z.homeo hA).rvBounded
  form := prodForm Z.Φ Z.bij hAP ω
  form_labels := by
    intro p₁ p₂ he
    obtain ⟨q₁, t₁, e₁, h₁⟩ := mem_prodImage_split Z.Φ Z.bij p₁.property
    obtain ⟨q₂, t₂, e₂, h₂⟩ := mem_prodImage_split Z.Φ Z.bij p₂.property
    have he' : Fin.append q₁.val.2 t₁ = Fin.append q₂.val.2 t₂ := by
      have := he
      rw [e₁, e₂] at this
      exact this
    obtain ⟨hu, rfl⟩ := appendInj.mp he'
    have hp₁ : p₁ = ⟨_, (mem_prodImage_iff Z.Φ Z.bij hAP q₁ t₁).mpr h₁⟩ := Subtype.ext e₁
    have hp₂ : p₂ = ⟨_, (mem_prodImage_iff Z.Φ Z.bij hAP q₂ t₁).mpr h₂⟩ := Subtype.ext e₂
    rw [hp₁, hp₂, prodForm_at Z.Φ Z.bij hAP ω q₁ t₁ _ h₁, prodForm_at Z.Φ Z.bij hAP ω q₂ t₁ _ h₂]
    exact class_forms hc π N hG hRC q₁ q₂ hu t₁ h₁ h₂

theorem frHGood_form (hG : Guards Z ω hAP) (hRC : FamRowConst Z hc ω π N) :
    (frHGood Z hc ω π N hAP h00 hκ hs hv hsmall hA hFin hG hRC).form = prodForm Z.Φ Z.bij hAP ω := rfl

/-! ### The identification -/

variable (hX0 : ∀ b ∈ P.carrier, (famSchema hc A ω π N).Valid (vfValues b.1))

include hX0 in
/-- **The descended indexed object of the recoded fibre family has the
head-start class of the frozen set.** -/
theorem cls_ind_eq_clsH (hG : Guards Z ω hAP) (hRC : FamRowConst Z hc ω π N) (hQ : (Z.Q hc).AllBounds)
    (hW : ∀ x ∈ (Z.Q hc).carrier, ((famSchema hc A ω π N).recode (Z.K hc)).Valid x) :
    cls ((Z.Q hc).indObj hQ.bounds ((famSchema hc A ω π N).recode (Z.K hc)) hW) =
      clsH hc (frHGood Z hc ω π N hAP h00 hκ hs hv hsmall hA hFin hG hRC) := by
  let X₀ := famSchema hc A ω π N
  let W := X₀.recode (Z.K hc)
  let gfr := frHGood Z hc ω π N hAP h00 hκ hs hv hsmall hA hFin hG hRC
  have hT := frTagged Z hAP
  rw [clsH_eq_hsObj hc gfr hT]
  symm
  -- sorting facts
  have hxs : ∀ q : regT Z.Bk, ∀ i, sortEval (rvs (1 + Z.sk) i) (rvValues q.val.2 i) := fun q i => (q.val.2 i).property
  have hzs : ∀ b : P, ∀ i, sortEval (vfs 1 i) (vfValues b.val.1 i) := fun b i => (b.val.1 i).property
  -- the frozen parameter of a key
  let zq : regT Z.Bk → P := fun q => Z.Φ₀.inverse Z.bij₀ (frz Z.F (Z.ρ q))
  have hrow : ∀ (q : regT Z.Bk) (t : Fin r → RVInfinity M),
      rvValues t ∈ W.row (rvValues q.val.2) ↔ ((Z.Φ.inverse Z.bij q).val.1, t) ∈ A.carrier := by
    intro q t
    rw [ChartSchema.recode_row (hxs q) (hzs (zq q)) (Z.K_mk_ρ hc q) (hRC _), famSchema_mem_row, Z.Φ_inverse,
      frozen_rows hG]
    constructor
    · rintro ⟨t', ht', he⟩
      rwa [rvValues_injective he] at ht'
    · intro ht
      exact ⟨t, ht, rfl⟩
  have hdom : rawDom (hsObj gfr hT) = (Z.Q hc).indDom W := by
    rw [hsObj_rawDom]
    ext w
    constructor
    · rintro ⟨v, ⟨y, hy⟩, rfl⟩
      obtain ⟨q, t, e, ht⟩ := mem_prodImage_split Z.Φ Z.bij hy
      obtain ⟨-, rfl⟩ := Prod.mk.inj e
      rw [rvValues_fin_append, KeySet.mem_indDom_iff]
      exact ⟨⟨q.val, q.property, rfl⟩, (hrow q t).mpr ht⟩
    · intro hw
      rw [← KeySet.append_keyOf_rowOf w] at hw ⊢
      obtain ⟨⟨qv, hqv, hx⟩, hr⟩ := ((Z.Q hc).mem_indDom_iff W _ _).mp hw
      let q : regT Z.Bk := ⟨qv, hqv⟩
      rw [← hx] at hr ⊢
      have hrs : ∀ j, sortEval SortTag.rv (KeySet.rowOf w j) := by
        intro j
        have := W.domain_definable.proper _ hw.2 (Fin.natAdd (1 + Z.sk) j)
        simpa only [Fin.append_right] using this
      let t : Fin r → RVInfinity M := fun j => ⟨KeySet.rowOf w j, hrs j⟩
      have ht : rvValues t = KeySet.rowOf w := rfl
      rw [← ht] at hr ⊢
      refine ⟨Fin.append q.val.2 t, ⟨q.val.1, (mem_prodImage_iff Z.Φ Z.bij hAP q t).mpr ((hrow q t).mp hr)⟩, ?_⟩
      exact rvValues_fin_append _ _
  apply cls_eq_of_iso
  refine isoOfMap (chartOf hc (hsObj gfr hT)) ((Z.Q hc).indChart W hW) (fun u => u)
    (RVCoordinateMaps.coordinate_graph_definable _ _ (chartOf hc (hsObj gfr hT)).domain_definable
      (id : Fin ((1 + Z.sk) + r) → Fin ((1 + Z.sk) + r))) ?_ ?_
  · change Set.BijOn (fun u => u) (rawDom (hsObj gfr hT)) ((Z.Q hc).indDom W)
    rw [hdom]
    exact Set.bijOn_id _
  · intro w hw
    change w ∈ rawDom (hsObj gfr hT) at hw
    rw [hsObj_rawDom] at hw
    obtain ⟨v, ⟨y, hy⟩, rfl⟩ := hw
    obtain ⟨q, t, e, ht⟩ := mem_prodImage_split Z.Φ Z.bij hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    rw [hsObj_weight gfr hT hc hy]
    change _ = ((Z.Q hc).indChart W hW).correctedWeight (rvValues (Fin.append q.val.2 t))
    rw [KeySet.indChart_weight, rvValues_fin_append, KeySet.keyOf_append, KeySet.rowOf_append]
    have hb : (zq q).val ∈ P.carrier := (zq q).property
    have hzA : ((zq q).val.1, t) ∈ A.carrier := by
      have := ht
      rw [Z.Φ_inverse, frozen_rows hG] at this
      exact this
    have hrz : rvValues t ∈ X₀.row (vfValues (zq q).val.1) :=
      (famSchema_mem_row hc A ω π N _ _).mpr ⟨t, hzA, rfl⟩
    rw [ChartSchema.recode_weightAt (hxs q) (hzs (zq q)) (Z.K_mk_ρ hc q) (hRC _) (hX0 _ hb)
      (hW _ ⟨q.val, q.property, rfl⟩) hrz, famSchema_weightAt hc A ω π N (hX0 _ hb) t hzA]
    have hlead : (Fin.append (rvValues q.val.2) (rvValues t) : Fin ((1 + Z.sk) + W.arity) → M)
        (Fin.castAdd W.arity ((Z.Q hc).idx)) = (rv M (q.val.1 0)).val := by
      rw [Fin.append_left]
      exact congrArg Subtype.val (regT_lead Z.Bk q.property)
    rw [hlead]
    have hform : gammaMapValue gfr.form ⟨_, hy⟩ = gammaMapValue ω ⟨_, hzA⟩ := by
      unfold gammaMapValue
      rw [frHGood_form, prodForm_at Z.Φ Z.bij hAP ω q t hy ht]
      have e₁ : (Z.Φ.inverse Z.bij q).val.1 = (Z.Φ₀.inverse Z.bij₀ (Z.ρ q)).val.1 := by rw [Z.Φ_inverse]
      have k₁ : ((Z.Φ₀.inverse Z.bij₀ (Z.ρ q)).val.1, t) ∈ A.carrier := e₁ ▸ ht
      rw [form_congr ω e₁ ht k₁, frozen_forms hG _ t k₁ hzA]
    rw [hform]
    have hlab : ∀ i, (Fin.append q.val.2 t ((Fin.natAdd (1 + Z.sk) ∘ π) i)).val = (t (π i)).val := by
      intro i
      simp only [Function.comp_apply, Fin.append_right]
    simp only [hlab]
    exact mul_left_comm _ _ _

end Side

end DiamondIntegral.Section7.Lemma714Frozen
