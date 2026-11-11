import «section 2».DiscGeometry
import «section 2».BallAlgebraicity
import Section4.PolydiscLocal
import Section3.SmallFiniteParameters
import ValuedFieldExtension

/-! Algebraicity over a finite tuple of genuine disc names. Temporary
centres, radii and the VF point are named only to choose a generic tuple
inside an open box, and are eliminated from the final ground-base result. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private def openBoxRaw {n : ℕ} (a r : Fin n → VF M) : Set (Fin n → M) :=
  {z | ∀ i, z i ∈ OpenBallCodes.rawBall ![(a i).val, (r i).val]}

omit hM in
private theorem openBoxRaw_definable (T : Set M) {n : ℕ} (a r : Fin n → VF M)
    (ha : ∀ i, (a i).val ∈ T) (hr : ∀ i, (r i).val ∈ T) :
    T.Definable LRV (openBoxRaw a r) := by
  have hside (i : Fin n) : T.Definable LRV
      {z : Fin n → M | z i ∈ OpenBallCodes.rawBall ![(a i).val, (r i).val]} := by
    let f : (Fin n → M) → Fin 3 → M := fun z => ![(a i).val, (r i).val, z i]
    have hf : T.DefinableMap LRV f := by
      intro j
      fin_cases j
      · exact LRV.definableFun_const (Fin n) (ha i)
      · exact LRV.definableFun_const (Fin n) (hr i)
      · exact Set.DefinableFun.proj LRV
    have h := Set.Definable.preimage_map hf (OpenBallCodes.membership_raw_definable T)
    convert h using 1
    ext z
    have hi : Fin.init (f z) = ![(a i).val, (r i).val] := by
      funext j
      fin_cases j <;> rfl
    change z i ∈ OpenBallCodes.rawBall ![(a i).val, (r i).val] ↔
      (f z) (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init (f z))
    rw [hi]
    rfl
  convert Set.definable_iInter_of_finite hside using 1
  ext z
  simp only [openBoxRaw, Set.mem_ofPred_eq, Set.mem_iInter]

private noncomputable def openBoxDefSet (T : Set M) {n : ℕ} (a r : Fin n → VF M)
    (ha : ∀ i, (a i).val ∈ T) (hr : ∀ i, (r i).val ∈ T) :
    DefSet (rawVFSpace (M := M) n) T where
  carrier := {x | SpecialTransformations.Section4.vfValues x ∈ openBoxRaw a r}
  definable := by
    let P := rawVFSpace (M := M) n
    have hdom := P.definable_domain T
    have hraw := openBoxRaw_definable T a r ha hr
    change T.Definable LRV (P.preimage _)
    convert hdom.inter hraw using 1
    ext z
    constructor
    · rintro ⟨hz, hdec⟩
      have he : SpecialTransformations.Section4.vfValues (P.decode ⟨z, hz⟩) = z :=
        Space.ofEmbedding_decode _ _ _ ⟨z, hz⟩
      refine ⟨hz, ?_⟩
      change SpecialTransformations.Section4.vfValues (P.decode ⟨z, hz⟩) ∈ openBoxRaw a r at hdec
      rwa [he] at hdec
    · rintro ⟨hz, hrawz⟩
      refine ⟨hz, ?_⟩
      change SpecialTransformations.Section4.vfValues (P.decode ⟨z, hz⟩) ∈ openBoxRaw a r
      have he : SpecialTransformations.Section4.vfValues (P.decode ⟨z, hz⟩) = z :=
        Space.ofEmbedding_decode _ _ _ ⟨z, hz⟩
      rw [he]
      exact hrawz

private theorem raw_open_side {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ) (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (a r : VF M) (hr : r ≠ 0) :
    {x : VF M | x.val ∈ OpenBallCodes.rawBall ![a.val, r.val]} =
      {x | v (x - a) < v r} :=
  OpenBallCodes.ball_eq_open v hv ![a.val, r.val]
    ⟨by intro i; fin_cases i; exact a.property; exact r.property,
      fun he => hr (Subtype.ext he)⟩

private theorem openBox_centres_mem {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ) (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (closed : Fin n → Bool) (a r x : Fin n → VF M) (δ : Fin n → Gamma M)
    (hr : ∀ i, r i ≠ 0) (hval : ∀ i, vfValue (r i) = (δ i).val)
    (hx : SpecialTransformations.Section4.vfValues x ∈ openBoxRaw a r) :
    ∀ i, x i ∈ discPoints (finitePolydiscNames closed a δ i) := by
  intro i
  have hi : v (x i - a i) < v (r i) :=
    (Set.ext_iff.mp (raw_open_side v hv (a i) (r i) (hr i)) (x i)).mp (hx i)
  have hf : finiteValue (r i) (hr i) = δ i := Subtype.ext (hval i)
  cases hc : closed i with
  | false =>
    simp only [finitePolydiscNames, hc, Bool.false_eq_true, ite_false]
    rw [← hf, openDiscCode_points v hv _ _ (hr i)]
    exact hi
  | true =>
    simp only [finitePolydiscNames, hc, ite_true]
    rw [← hval i, closedDiscCode_points v hv _ (r i)]
    exact hi.le

private theorem valuation_nontrivial {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    [Valued (VF M) Γ]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ ε : VF M, ε ≠ 0 ∧ Valued.v ε < 1 := by
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  refine ⟨ε, hε0, lt_of_not_ge ?_⟩
  intro h
  apply hε
  apply (hv 1 ε).mpr
  simpa only [map_one] using h

/-- Lemma 2.18 for the finite-radius open/closed charts, expressed using
actual existing DC names and their full invariant preimages. Neither the
generic tuple nor its centres/radius representatives appear in the final
base. Zero coordinates are included. Singleton-radius coordinates and the
whole-field chart are not included in this finite Gamma chart statement. -/
theorem lemma_2_18_finite_names {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : ParameterBase M) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (b : VF M) (hb : AlgebraicOverFinitePolydiscNames B closed a δ b) :
    GammaParameters.AlgebraicAtBase B .vf b.val := by
  classical
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VF M) Γ := Valued.mk' v
  let r : Fin n → VF M := fun i => radiusRepresentative (δ i).val
  have hval (i : Fin n) : vfValue (r i) = (δ i).val := radiusRepresentative_value _
  have hr (i : Fin n) : r i ≠ 0 :=
    fun hz => (δ i).property ((radiusRepresentative_zero_iff _).mp hz)
  let T : Set M := ((insert b.val B.real) ∪
    Set.range (SpecialTransformations.Section4.vfValues a)) ∪
    Set.range (SpecialTransformations.Section4.vfValues r)
  have hST : B.real ⊆ T :=
    (Set.subset_insert _ _).trans (Set.subset_union_left.trans Set.subset_union_left)
  have hbT : b.val ∈ T := Or.inl (Or.inl (Set.mem_insert _ _))
  have haT (i : Fin n) : (a i).val ∈ T := Or.inl (Or.inr (Set.mem_range_self i))
  have hrT (i : Fin n) : (r i).val ∈ T := Or.inr (Set.mem_range_self i)
  have hTsmall : Cardinal.mk T < κ :=
    small_union_range hκ _
      (small_union_range hκ _ (small_insert hκ B.real hsmall b.val)
        (SpecialTransformations.Section4.vfValues a))
      (SpecialTransformations.Section4.vfValues r)
  let P : ValuedPolydisc v n := ⟨a, r, hr⟩
  have hnt : ∃ ε : VF M, ε ≠ 0 ∧ Valued.v ε < 1 := valuation_nontrivial hv
  let A := (openBoxDefSet T a r haT hrT).prod (DefSet.univ (rawRVSpace (M := M) 0) T)
  have hbox : ∀ x ∈ Set.pi Set.univ P.side, (x, Fin.elim0) ∈ A.carrier := by
    intro x hx
    refine ⟨?_, Set.mem_univ _⟩
    change ∀ i, (x i).val ∈ OpenBallCodes.rawBall ![(a i).val, (r i).val]
    intro i
    exact (Set.ext_iff.mp (raw_open_side v hv (a i) (r i) (hr i)) (x i)).mpr
      (hx i (Set.mem_univ i))
  have hpoint (p : A) :
      AlgebraicAt (B.real ∪ Set.range (SpecialTransformations.Section4.vfValues p.val.1)) .vf b.val := by
    have hp : SpecialTransformations.Section4.vfValues p.val.1 ∈ openBoxRaw a r := p.property.1
    have he := finitePolydiscNames_recenter v hv closed a p.val.1 δ
      (openBox_centres_mem v hv closed a r p.val.1 δ hr hval hp)
    obtain ⟨R, hfin, hbR⟩ := hb
    apply algebraic_over_disc_names_pointwise B closed p.val.1 δ b
    refine ⟨R, ?_, ?_⟩
    · rwa [R.fibre_eq_of_names p.val.1 a δ δ he]
    · rwa [R.fibre_eq_of_names p.val.1 a δ δ he]
  exact (GammaParameters.algebraic_vf_iff_real B b).mpr
    (vf_algebraic_of_uniform_on_box hs B.real T hST hTsmall b hbT A P.side
      (P.side_infinite hnt) hbox hpoint)

end DiamondIntegral.Section2
