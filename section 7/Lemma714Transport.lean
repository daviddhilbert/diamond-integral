import «section 7».Lemma714Keys

/-! Lemma 7.14, part 27: transport along product maps and frozen points.

* Product images: membership in the image of `g ⋉ A` at `(q, t)` is membership
  of `(g⁻¹(q), t)` in `A` (`mem_prodImage_iff`); the transported form
  `prodForm` takes the value of `ω` there (`prodForm_at`).
* Frozen points: a set that is a coordinate product on every frozen ball
  contains a point iff it contains its frozen point (`freeze_mem_iff`).
* Accessors: the structural map, volume and corrected weight of a recoded chart
  schema at a key are those of the schema at a related parameter
  (`recode_coordAt`, `recode_volAt`, `recode_weightAt`); for the family of
  fibres they are `t ∘ π` and `ω(a, t)` (`famSchema_coordAt`, `famSchema_volAt`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

/-! ### Accessors of recoded and family schemata -/

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

namespace ChartSchema
variable {d : ℕ} {K : KeyRel B sq sp} {W : ChartSchema B sp d} {x : Fin q → M} {z : Fin p → M}
  (hx : ∀ i, sortEval (sq i) (x i)) (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z) (hc : W.RowConst K x)
include hx hz hK hc

theorem recode_coordAt (hW : W.Valid z) (hW' : (W.recode K).Valid x) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    (W.recode K).coordAt x u = W.coordAt z u := by
  have hu' : u ∈ (W.recode K).row x := (recode_row hx hz hK hc u).mpr hu
  have h1 := coordRow_coordAt hW' hu'
  rw [recode_coordRow hx hz hK hc] at h1
  exact ((coordRow_iff hW u _).mp h1).2.symm

theorem recode_volAt (hW : W.Valid z) (hW' : (W.recode K).Valid x) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    (W.recode K).volAt x u = W.volAt z u := by
  obtain ⟨c, hcz⟩ := hW.vol_total u hu
  have hcx : (W.recode K).volRow x u c := (recode_volRow hx hz hK hc u c).mpr hcz
  rw [← ((volRow_iff hW' u c).mp hcx).2.2, ← ((volRow_iff hW u c).mp hcz).2.2]

theorem recode_weightAt (hW : W.Valid z) (hW' : (W.recode K).Valid x) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    (W.recode K).weightAt x u = W.weightAt z u := by
  unfold weightAt
  rw [recode_volAt hx hz hK hc hW hW' hu, recode_coordAt hx hz hK hc hW hW' hu]

end ChartSchema

section Fam
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {m r k : ℕ}
  (A : DefSet (rawMixedSpace (M := M) m r) S) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
  (π : Fin k → Fin r) (N : ℕ) {a : Fin m → VF M}

theorem famSchema_coordAt (hF : (famSchema hc A ω π N).Valid (vfValues a)) (t : Fin r → RVInfinity M)
    (ht : (a, t) ∈ A.carrier) :
    (famSchema hc A ω π N).coordAt (vfValues a) (rvValues t) = fun i => (t (π i)).val :=
  ((famSchema_coordRow hc A ω π N a _ _).mp
    (ChartSchema.coordRow_coordAt hF ((famSchema_mem_row hc A ω π N a _).mpr ⟨t, ht, rfl⟩))).2

theorem famSchema_volAt (hF : (famSchema hc A ω π N).Valid (vfValues a)) (t : Fin r → RVInfinity M)
    (ht : (a, t) ∈ A.carrier) :
    (famSchema hc A ω π N).volAt (vfValues a) (rvValues t) = (ω ⟨(a, t), ht⟩).val := by
  have hrow := (famSchema_mem_row hc A ω π N a _).mpr ⟨t, ht, rfl⟩
  obtain ⟨c, hcv⟩ := hF.vol_total _ hrow
  rw [← ((ChartSchema.volRow_iff hF _ c).mp hcv).2.2]
  exact ((famSchema_volRow hc A ω π N a t ht c).mp hcv).2

theorem famSchema_weightAt (hF : (famSchema hc A ω π N).Valid (vfValues a)) (t : Fin r → RVInfinity M)
    (ht : (a, t) ∈ A.carrier) :
    (famSchema hc A ω π N).weightAt (vfValues a) (rvValues t) =
      gammaMapValue ω ⟨(a, t), ht⟩ * ∏ i, codeValue (t (π i)).val := by
  unfold ChartSchema.weightAt
  rw [famSchema_volAt hc A ω π N hF t ht, famSchema_coordAt hc A ω π N hF t ht]
  rfl

end Fam

end DiamondIntegral.Section7.Lemma714Schema

/-! ### Product images and frozen points -/

namespace DiamondIntegral.Section7.Lemma714Prod
open DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

theorem appendInj {α : Type*} {a b : ℕ} {x x' : Fin a → α} {z z' : Fin b → α} :
    Fin.append x z = Fin.append x' z' ↔ x = x' ∧ z = z' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrFun h (Fin.castAdd b i)
    · simpa using congrFun h (Fin.natAdd a i)
  · rintro ⟨rfl, rfl⟩
    rfl

section ProdImage
variable {P : DefSet (rawMixedSpace (M := M) 1 0) S} {Q : DefSet (rawMixedSpace (M := M) 1 s) S}
  (g : Map P Q) (hg : Function.Bijective g) {A : DefSet (rawMixedSpace (M := M) 1 r) S}
  (hAP : ∀ p ∈ A.carrier, basePoint p ∈ P.carrier)

include hg in
theorem prodMap_toImage_bijective : Function.Bijective (prodMap g hAP).toImage := by
  refine ⟨fun p q he => prodMap_injective g hAP hg.1 (Subtype.ext (by
    have h := congrArg Subtype.val he
    exact h)), ?_⟩
  rintro ⟨_, p, rfl⟩
  exact ⟨p, rfl⟩

omit hM in
theorem basePoint_mk (b : Mixed M 1 0) (t : Fin r → RVInfinity M) : basePoint ((b.1, t) : Mixed M 1 r) = b :=
  Prod.ext rfl (Subsingleton.elim _ _)

theorem mem_prodImage_iff (q : Q) (t : Fin r → RVInfinity M) :
    ((q.val.1, Fin.append q.val.2 t) : Mixed M 1 (s + r)) ∈ (prodMap g hAP).image.carrier ↔
      ((g.inverse hg q).val.1, t) ∈ A.carrier := by
  constructor
  · rintro ⟨p, hp0⟩
    have hp : (prodMap g hAP p).val = ((q.val.1, Fin.append q.val.2 t) : Mixed M 1 (s + r)) := hp0
    rw [prodMap_apply] at hp
    have h1 := congrArg Prod.fst hp
    obtain ⟨hw, ht⟩ := appendInj.mp (congrArg Prod.snd hp)
    have hq : g (baseMap hAP p) = q := Subtype.ext (Prod.ext h1 hw)
    have hinv : g.inverse hg q = baseMap hAP p := by rw [← hq, Map.inverse_apply]
    rw [hinv, baseMap_apply, ← ht]
    exact p.property
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    show (prodMap g hAP ⟨_, h⟩).val = _
    rw [prodMap_apply]
    have hb : baseMap hAP ⟨_, h⟩ = g.inverse hg q := Subtype.ext (basePoint_mk _ t)
    rw [hb, Map.apply_inverse]

/-- The transported form on the image of `g ⋉ A`. -/
def prodForm (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map (prodMap g hAP).image (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp ((prodMap g hAP).toImage.inverse (prodMap_toImage_bijective g hg hAP))

theorem prodForm_apply (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) :
    prodForm g hg hAP ω ((prodMap g hAP).toImage p) = ω p := by
  unfold prodForm
  rw [Map.comp_apply, Map.inverse_apply]

theorem prodForm_at (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (q : Q) (t : Fin r → RVInfinity M)
    (hm : ((q.val.1, Fin.append q.val.2 t) : Mixed M 1 (s + r)) ∈ (prodMap g hAP).image.carrier)
    (h : ((g.inverse hg q).val.1, t) ∈ A.carrier) :
    prodForm g hg hAP ω ⟨_, hm⟩ = ω ⟨_, h⟩ := by
  have he : (⟨_, hm⟩ : (prodMap g hAP).image) = (prodMap g hAP).toImage ⟨_, h⟩ := by
    apply Subtype.ext
    change _ = (prodMap g hAP ⟨_, h⟩).val
    rw [prodMap_apply]
    have hb : baseMap hAP ⟨_, h⟩ = g.inverse hg q := Subtype.ext (basePoint_mk _ t)
    rw [hb, Map.apply_inverse]
  rw [he, prodForm_apply]

theorem prodForm_labels_iff (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : (prodMap g hAP).image) :
    ∃ a : A, (prodMap g hAP).toImage a = p ∧ prodForm g hg hAP ω p = ω a := by
  obtain ⟨_, a, rfl⟩ := p
  exact ⟨a, rfl, prodForm_apply g hg hAP ω a⟩

end ProdImage

section Frozen
variable {B₀ : DefSet (rawMixedSpace (M := M) 1 s) S} (F : FMT.FocusFreezingData B₀)

/-- **A coordinate product on every frozen ball contains a point iff it contains
its frozen point.** -/
theorem freeze_mem_iff {m : ℕ} {C : Set (Mixed M 1 m)}
    (hC : ∀ D : F.balls, FMT.CoordinateProductDomain C (FMT.vfOpenBall D.val) (F.centers D) 0) (q : Mixed M 1 m) :
    q ∈ C ↔ (((fun _ : Fin 1 => FMT.vfFamilyFreeze F.balls F.centers (q.1 0)), q.2) : Mixed M 1 m) ∈ C := by
  by_cases hx : ∃ D : F.balls, q.1 0 ∈ FMT.vfOpenBall D.val
  · obtain ⟨D, hD⟩ := hx
    have hf : FMT.vfFamilyFreeze F.balls F.centers (q.1 0) = F.centers D := by
      rw [FMT.vfFamilyFreeze_eq F.balls F.centers F.separated]
      exact FMT.familyFreeze_inside _ _ (fun D E x hx hE => F.separated D E x.val hx hE) D _ hD
    have hu : Function.update q.1 0 (F.centers D) = fun _ : Fin 1 => F.centers D := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp
    rw [hf, (hC D q hD), hu]
  · have hf : FMT.vfFamilyFreeze F.balls F.centers (q.1 0) = q.1 0 := by
      rw [FMT.vfFamilyFreeze_eq F.balls F.centers F.separated]
      exact FMT.familyFreeze_outside _ _ _ (not_exists.mp hx)
    have hu : (fun _ : Fin 1 => q.1 0) = q.1 := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
    rw [hf, hu]

end Frozen

end DiamondIntegral.Section7.Lemma714Prod
