import «section 5».InflatedGammaCodePromotion
import «section 5».NativeArbitraryWeakRVPresentation
import «section 5».NativeWeakRVLabelGraphs
import IntegrationSection6.GammaWitnessUniformity

/-! Uniform weak RV-lift data over Gamma parameters.

A datum consists of a family of RV sets `D_γ ⊆ RV^{a+k}` whose label is the
last `k` coordinates, a uniform bound for the label fibres, and a family of
graphs `H_γ`. It is valid at `γ` when the label fibres of `D_γ` are bounded
and `H_γ` is the graph of a bijection from the row `A_γ` onto the lift
`{(b,w) : w ∈ D_γ, last w = rv b}`. Validity is a first-order condition on
`γ` over the original base. Every parameter has a valid datum, obtained over
the base with `γ` adjoined and promoted to a Gamma family. Compactness for the
complete code preimages gives finitely many data, and a definable
disjoint refinement of their validity loci covers `Γ^n`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-! ### Counting -/

theorem inflated_finite_of_no_injective {α : Type*} {T : Set α} {N : ℕ}
    (h : ¬ ∃ w : Fin (N + 1) → α, Function.Injective w ∧ ∀ l, w l ∈ T) : T.Finite := by
  by_contra hinf
  let f := Set.Infinite.natEmbedding T hinf
  exact h ⟨fun l => (f l.val).val, fun a b hab => Fin.ext (f.injective (Subtype.ext hab)),
    fun l => (f l.val).property⟩

theorem inflated_no_injective_of_ncard {α : Type*} {T : Set α} {N : ℕ} (hT : T.Finite)
    (hN : T.ncard ≤ N) : ¬ ∃ w : Fin (N + 1) → α, Function.Injective w ∧ ∀ l, w l ∈ T := by
  rintro ⟨w, hw, hwT⟩
  have h := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set (Fin (N + 1)))) w
    (fun l _ => hwT l) hw.injOn hT
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- Existence of an injective `N`-tuple in the fibres of a definable set. -/
theorem _root_.DiamondIntegral.Section3.GammaGroundDefinable.exists_injective_tuple {P Q : Space LRV M}
    {S : Set (P.prod Q).Carrier} (hS : GammaGroundDefinable hc B (P.prod Q) S) (N : ℕ) :
    GammaGroundDefinable hc B P
      {p | ∃ w : Fin N → Q.Carrier, Function.Injective w ∧ ∀ l, (p, w l) ∈ S} := by
  let T := P.prod (Q.power (Fin N))
  let fst := universalProductFst P (Q.power (Fin N)) B.real
  let snd := universalProductSnd P (Q.power (Fin N)) B.real
  have hmem : ∀ l : Fin N, GammaGroundDefinable hc B T {z | (z.1, z.2 l) ∈ S} := fun l =>
    hS.preimage ((fst.pair ((universalPowerCoordinate Q B.real l).comp snd)).toUniv)
  have hne : ∀ l l' : Fin N, GammaGroundDefinable hc B T {z | l ≠ l' → z.2 l ≠ z.2 l'} := by
    intro l l'
    by_cases h : l = l'
    · apply (GammaGroundDefinable.of_real (T.definable_univ B.real)).congr
      intro z
      simp only [Set.mem_univ, h, ne_eq, not_true_eq_false, IsEmpty.forall_iff, Set.mem_ofPred_eq]
    · apply (GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
        ((universalPowerCoordinate Q B.real l).comp snd)
        ((universalPowerCoordinate Q B.real l').comp snd)).compl.congr
      intro z
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, ne_eq, h, not_false_eq_true, true_implies]
      rfl
  have hall := (GammaGroundDefinable.iInter hmem).inter
    (GammaGroundDefinable.iInter (fun l => GammaGroundDefinable.iInter (hne l)))
  apply (hall.image fst).congr
  intro p
  constructor
  · rintro ⟨z, ⟨hm, hn⟩, hp⟩
    change z.1 = p at hp
    subst hp
    refine ⟨z.2, ?_, fun l => Set.mem_iInter.mp hm l⟩
    intro l l' he
    by_contra hll
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hn l) l' hll he
  · rintro ⟨w, hw, hS'⟩
    refine ⟨(p, w), ⟨Set.mem_iInter.mpr hS', Set.mem_iInter.mpr fun l => Set.mem_iInter.mpr fun l' => ?_⟩, rfl⟩
    exact fun hll he => hll (hw he)

/-! ### Weak-lift data -/

/-- Uniform weak RV-lift data for a Gamma family with rows in `VF^m × RV^s`. -/
structure GammaWeakLiftDatum (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    (n m s : ℕ) where
  degree : ℕ
  arity : ℕ
  bound : ℕ
  domain : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) (arity + degree)))
  graph : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod
    ((rawMixedSpace (M := M) m s).prod (rawMixedSpace (M := M) degree (arity + degree))))

namespace GammaWeakLiftDatum
variable {n m s : ℕ} (D : GammaWeakLiftDatum hc B n m s)

/-- The lift `{(b,w) : w ∈ D_γ, last w = rv b}`. -/
def liftRow (γ : Fin n → Values.Gamma (M := M)) :
    Set (rawMixedSpace (M := M) D.degree (D.arity + D.degree)).Carrier :=
  {q | (γ, q.2) ∈ D.domain.carrier ∧ q.2 ∘ Fin.natAdd D.arity = tupleRV q.1}

/-- A label fibre of `D_γ`. -/
def labelFibre (γ : Fin n → Values.Gamma (M := M)) (y : Fin D.degree → CanonicalRV.RVSort M) :
    Set (Fin (D.arity + D.degree) → CanonicalRV.RVSort M) :=
  {w | (γ, w) ∈ D.domain.carrier ∧ w ∘ Fin.natAdd D.arity = y}

/-- Validity of a datum at a parameter, for the family with domain `A`. -/
structure Valid (A : Set ((inflatedGammaPower hc n).prod (rawMixedSpace (M := M) m s)).Carrier)
    (γ : Fin n → Values.Gamma (M := M)) : Prop where
  bounded : ∀ y, ¬ ∃ w : Fin (D.bound + 1) → (Fin (D.arity + D.degree) → CanonicalRV.RVSort M),
    Function.Injective w ∧ ∀ l, w l ∈ D.labelFibre γ y
  total : ∀ q, (γ, q) ∈ A → ∃! q', (γ, (q, q')) ∈ D.graph.carrier
  maps : ∀ q q', (γ, (q, q')) ∈ D.graph.carrier → (γ, q) ∈ A ∧ q' ∈ D.liftRow γ
  onto : ∀ q', q' ∈ D.liftRow γ → ∃! q, (γ, (q, q')) ∈ D.graph.carrier

theorem Valid.labelFibre_finite {A : Set ((inflatedGammaPower hc n).prod (rawMixedSpace (M := M) m s)).Carrier}
    {γ : Fin n → Values.Gamma (M := M)} (h : D.Valid A γ) (y : Fin D.degree → CanonicalRV.RVSort M) :
    (D.labelFibre γ y).Finite :=
  inflated_finite_of_no_injective (h.bounded y)

theorem valid_definable (A : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawMixedSpace (M := M) m s))) :
    GammaGroundDefinable hc B (inflatedGammaPower hc n) {γ | D.Valid A.carrier γ} := by
  let Γn := inflatedGammaPower hc n
  let Mx := rawMixedSpace (M := M) m s
  let Rk := rawRVSpace (M := M) D.degree
  let Ra := rawRVSpace (M := M) (D.arity + D.degree)
  let Ly := rawMixedSpace (M := M) D.degree (D.arity + D.degree)
  let last := inflatedRVReindexMap B.real (Fin.natAdd D.arity : Fin D.degree → Fin (D.arity + D.degree))
  -- bounded label fibres
  have hSa : GammaGroundDefinable hc B ((Γn.prod Rk).prod Ra)
      {z | (z.1.1, z.2) ∈ D.domain.carrier ∧ z.2 ∘ Fin.natAdd D.arity = z.1.2} := by
    have h1 := D.domain.definable.preimage
      (((universalProductFst Γn Rk B.real).comp (universalProductFst (Γn.prod Rk) Ra B.real)).pair
        (universalProductSnd (Γn.prod Rk) Ra B.real)).toUniv
    have h2 := GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
      (last.comp (universalProductSnd (Γn.prod Rk) Ra B.real))
      ((universalProductSnd Γn Rk B.real).comp (universalProductFst (Γn.prod Rk) Ra B.real))
    exact h1.inter h2
  have hbounded := ((hSa.exists_injective_tuple (D.bound + 1)).compl).forall_snd
  -- totality
  have hG' : GammaGroundDefinable hc B ((Γn.prod Mx).prod Ly)
      {z | (z.1.1, (z.1.2, z.2)) ∈ D.graph.carrier} :=
    D.graph.definable.preimage
      (((universalProductFst Γn Mx B.real).comp (universalProductFst (Γn.prod Mx) Ly B.real)).pair
        (((universalProductSnd Γn Mx B.real).comp (universalProductFst (Γn.prod Mx) Ly B.real)).pair
          (universalProductSnd (Γn.prod Mx) Ly B.real)).toUniv).toUniv
  have htotal := (A.definable.compl.union (gammaGroundDefinable_unique_fibre hG')).forall_snd
  -- the lift condition on the second factor
  have hL : GammaGroundDefinable hc B ((Γn.prod Mx).prod Ly)
      {z | (z.1.1, z.2.2) ∈ D.domain.carrier ∧ z.2.2 ∘ Fin.natAdd D.arity = tupleRV z.2.1} := by
    have h1 := D.domain.definable.preimage
      (((universalProductFst Γn Mx B.real).comp (universalProductFst (Γn.prod Mx) Ly B.real)).pair
        ((universalProductSnd (rawVFSpace (M := M) D.degree) Ra B.real).comp
          (universalProductSnd (Γn.prod Mx) Ly B.real))).toUniv
    have h2 := GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
      ((last.comp (universalProductSnd (rawVFSpace (M := M) D.degree) Ra B.real)).comp
        (universalProductSnd (Γn.prod Mx) Ly B.real))
      (((universalTupleRVMap B.real D.degree).comp (universalProductFst (rawVFSpace (M := M) D.degree) Ra B.real)).comp
        (universalProductSnd (Γn.prod Mx) Ly B.real))
    exact h1.inter h2
  have hA1 := A.definable.preimage (universalProductFst (Γn.prod Mx) Ly B.real)
  have hmaps := ((hG'.compl.union (hA1.inter hL)).forall_snd).forall_snd
  -- surjectivity
  have hL' : GammaGroundDefinable hc B (Γn.prod Ly)
      {p | (p.1, p.2.2) ∈ D.domain.carrier ∧ p.2.2 ∘ Fin.natAdd D.arity = tupleRV p.2.1} := by
    have h1 := D.domain.definable.preimage
      ((universalProductFst Γn Ly B.real).pair
        ((universalProductSnd (rawVFSpace (M := M) D.degree) Ra B.real).comp
          (universalProductSnd Γn Ly B.real))).toUniv
    have h2 := GammaGroundDefinable.diagonal_preimage (hc := hc) (B := B)
      ((last.comp (universalProductSnd (rawVFSpace (M := M) D.degree) Ra B.real)).comp
        (universalProductSnd Γn Ly B.real))
      (((universalTupleRVMap B.real D.degree).comp (universalProductFst (rawVFSpace (M := M) D.degree) Ra B.real)).comp
        (universalProductSnd Γn Ly B.real))
    exact h1.inter h2
  have hG'' : GammaGroundDefinable hc B ((Γn.prod Ly).prod Mx)
      {z | (z.1.1, (z.2, z.1.2)) ∈ D.graph.carrier} :=
    D.graph.definable.preimage
      (((universalProductFst Γn Ly B.real).comp (universalProductFst (Γn.prod Ly) Mx B.real)).pair
        ((universalProductSnd (Γn.prod Ly) Mx B.real).pair
          ((universalProductSnd Γn Ly B.real).comp (universalProductFst (Γn.prod Ly) Mx B.real))).toUniv).toUniv
  have honto := (hL'.compl.union (gammaGroundDefinable_unique_fibre hG'')).forall_snd
  apply (hbounded.inter (htotal.inter (hmaps.inter honto))).congr
  intro γ
  constructor
  · rintro ⟨hb, ht, hm, ho⟩
    refine ⟨fun y => hb y, fun q hq => ?_, fun q q' hqq => ?_, fun q' hq' => ?_⟩
    · exact (ht q).resolve_left (fun h => h hq)
    · rcases hm q q' with h | h
      · exact absurd hqq h
      · exact ⟨h.1, h.2⟩
    · exact (ho q').resolve_left (fun h => h hq')
  · intro h
    refine ⟨fun y => h.bounded y, fun q => ?_, fun q q' => ?_, fun q' => ?_⟩
    · by_cases hq : (γ, q) ∈ A.carrier
      · exact Or.inr (h.total q hq)
      · exact Or.inl hq
    · by_cases hqq : (γ, (q, q')) ∈ D.graph.carrier
      · exact Or.inr (h.maps q q' hqq)
      · exact Or.inl hqq
    · by_cases hq' : q' ∈ D.liftRow γ
      · exact Or.inr (h.onto q' hq')
      · exact Or.inl hq'

end GammaWeakLiftDatum

theorem inflated_append_comp_castAdd {α : Type*} {a k : ℕ} (u : Fin a → α) (v : Fin k → α) :
    Fin.append u v ∘ Fin.castAdd k = u := funext (Fin.append_left u v)

theorem inflated_append_comp_natAdd {α : Type*} {a k : ℕ} (u : Fin a → α) (v : Fin k → α) :
    Fin.append u v ∘ Fin.natAdd a = v := funext (Fin.append_right u v)

theorem inflated_append_split_rows {α : Type*} {a k : ℕ} (w : Fin (a + k) → α) :
    Fin.append (w ∘ Fin.castAdd k) (w ∘ Fin.natAdd a) = w := Fin.append_castAdd_natAdd

namespace GammaVFFamily
variable {n : ℕ}

/-- Every parameter has a valid datum: a weak RV lift of the row is chosen
over the base with `γ` adjoined, in graph form, and promoted to Gamma families. -/
theorem exists_valid_datum (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (A : GammaVFFamily hc B n) (γ : Fin n → Values.Gamma (M := M)) :
    ∃ D : GammaWeakLiftDatum hc B n A.m A.s, D.Valid A.domain.carrier γ := by
  obtain ⟨k, U, ⟨e⟩⟩ := native_arbitrary_weak_rv_lift_exists (B := adjoinGammaTuple B γ) hκ hs h00 hr (A.fibreOver γ)
  have hγC : Cardinal.mk (adjoinGammaTuple B γ).gamma < κ := small_union_range_carrier hκ.le B.gamma hγ γ
  obtain ⟨N, hN⟩ := nativeWeakRVLabelGraph_uniform_bound (B := adjoinGammaTuple B γ) hκ.le hs hr hγC U
  let C := adjoinGammaTuple B γ
  let a := U.arity
  let first := inflatedRVReindexMap C.real (Fin.castAdd k : Fin a → Fin (a + k))
  let last := inflatedRVReindexMap C.real (Fin.natAdd a : Fin k → Fin (a + k))
  let Dγ : GammaGroundDefSet hc C (rawRVSpace (M := M) (a + k)) :=
    ⟨{w | ∃ u : U.domain, u.val = w ∘ Fin.castAdd k ∧ (U.volume u).val = w ∘ Fin.natAdd a},
      U.volume.graph_definable.preimage (first.pair last).toUniv⟩
  let Mx := rawMixedSpace (M := M) A.m A.s
  let Ly := rawMixedSpace (M := M) k (a + k)
  let Vk := rawVFSpace (M := M) k
  let Ra := rawRVSpace (M := M) (a + k)
  let hmap := ((universalProductFst Mx Ly C.real).pair
      (((universalProductFst Vk Ra C.real).comp (universalProductSnd Mx Ly C.real)).pair
        ((first.comp (universalProductSnd Vk Ra C.real)).comp (universalProductSnd Mx Ly C.real))).toUniv).toUniv
  let Hγ : GammaGroundDefSet hc C (Mx.prod Ly) :=
    ⟨{z | (∃ x : (A.fibreOver γ).domain, x.val = z.1 ∧ (e.map x).val = (z.2.1, z.2.2 ∘ Fin.castAdd k)) ∧
        z.2.2 ∘ Fin.natAdd a = tupleRV z.2.1},
      (e.map.graph_definable.preimage hmap).inter
        (GammaGroundDefinable.diagonal_preimage (hc := hc) (B := C)
          ((last.comp (universalProductSnd Vk Ra C.real)).comp (universalProductSnd Mx Ly C.real))
          (((universalTupleRVMap C.real k).comp (universalProductFst Vk Ra C.real)).comp
            (universalProductSnd Mx Ly C.real)))⟩
  obtain ⟨𝒟, h𝒟⟩ := Dγ.exists_gamma_family γ
  obtain ⟨ℋ, hℋ⟩ := Hγ.exists_gamma_family γ
  refine ⟨⟨k, a, N, 𝒟, ℋ⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rintro y ⟨w, hw, hwF⟩
    have hmem : ∀ l, ∃ u : U.domain, u.val = w l ∘ Fin.castAdd k ∧ (U.volume u).val = y := fun l => by
      obtain ⟨u, hu1, hu2⟩ := (h𝒟 (w l)).mp (hwF l).1
      exact ⟨u, hu1, hu2.trans (hwF l).2⟩
    have hfirst : Function.Injective (fun l => rvValues (w l ∘ Fin.castAdd k)) := by
      intro l l' he
      apply hw
      have h1 : w l ∘ Fin.castAdd k = w l' ∘ Fin.castAdd k := rvValues_injective he
      have h2 : w l ∘ Fin.natAdd a = w l' ∘ Fin.natAdd a := (hwF l).2.trans (hwF l').2.symm
      rw [← inflated_append_split_rows (w l), ← inflated_append_split_rows (w l'), h1, h2]
    obtain ⟨hfin, hcard⟩ := hN (rvValues y) (fun j => (y j).property)
    apply inflated_no_injective_of_ncard hfin hcard
    refine ⟨fun l => rvValues (w l ∘ Fin.castAdd k), hfirst, fun l => ?_⟩
    obtain ⟨u, hu1, hu2⟩ := hmem l
    exact (nativeWeakRVLabelGraph_append_iff U _ _).mpr ⟨u, congrArg rvValues hu1, congrArg rvValues hu2⟩
  · intro q hq
    let x : (A.fibreOver γ).domain := ⟨q, hq⟩
    refine ⟨((e.map x).val.1, Fin.append (e.map x).val.2 (tupleRV (e.map x).val.1)), ?_, ?_⟩
    · apply (hℋ _).mpr
      refine ⟨⟨x, rfl, ?_⟩, inflated_append_comp_natAdd _ _⟩
      exact Prod.ext rfl (inflated_append_comp_castAdd _ _).symm
    · rintro ⟨b', w'⟩ h'
      obtain ⟨⟨x', hx', he'⟩, hl'⟩ := (hℋ _).mp h'
      have hxx : x' = x := Subtype.ext hx'
      rw [hxx] at he'
      have h1 : (e.map x).val.1 = b' := congrArg Prod.fst he'
      have h2 : (e.map x).val.2 = w' ∘ Fin.castAdd k := congrArg Prod.snd he'
      refine Prod.ext h1.symm ?_
      change w' = Fin.append (e.map x).val.2 (tupleRV (e.map x).val.1)
      rw [h2, h1, ← hl']
      exact (inflated_append_split_rows w').symm
  · intro q q' hqq
    obtain ⟨⟨x, hx, he⟩, hl⟩ := (hℋ _).mp hqq
    have hxq : x.val = q := hx
    refine ⟨?_, (h𝒟 _).mpr ?_, hl⟩
    · rw [← hxq]
      exact x.property
    · obtain ⟨u, hu1, hu2⟩ := (e.map x).property
      have he1 : (e.map x).val.1 = q'.1 := congrArg Prod.fst he
      refine ⟨u, hu1.trans (congrArg Prod.snd he), ?_⟩
      change (U.volume u).val = q'.2 ∘ Fin.natAdd a
      rw [hl, ← he1]
      exact hu2
  · rintro ⟨b, w⟩ ⟨hw, hl⟩
    obtain ⟨u, hu1, hu2⟩ := (h𝒟 w).mp hw
    have hlift : (b, w ∘ Fin.castAdd k) ∈ (nativeWeakRVObjectLift U).carrier :=
      ⟨u, hu1, hu2.trans hl⟩
    obtain ⟨x, hx⟩ := e.bijective.2 ⟨(b, w ∘ Fin.castAdd k), hlift⟩
    refine ⟨x.val, (hℋ _).mpr ⟨⟨x, rfl, congrArg Subtype.val hx⟩, hl⟩, ?_⟩
    intro q hq
    obtain ⟨⟨x', hx', he'⟩, _⟩ := (hℋ _).mp hq
    have hxq : x'.val = q := hx'
    have hee : e.map x' = e.map x := Subtype.ext (he'.trans (congrArg Subtype.val hx).symm)
    rw [← hxq, e.bijective.1 hee]

/-- Compactness for the complete code preimages of the validity loci. -/
theorem finite_valid_catalog (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (A : GammaVFFamily hc B n) :
    ∃ J : Finset (GammaWeakLiftDatum hc B n A.m A.s), ∀ γ, ∃ D ∈ J, D.Valid A.domain.carrier γ := by
  obtain ⟨J, hJ⟩ := IntegrationInACVF.Section6.gamma_finite_witnesses hκ.le hs hr hγ
    (fun _ : Fin n => SortTag.rv) {z | Proper z} (Section4.GammaOrderLogic.proper_definable_base B n)
    (fun D : GammaWeakLiftDatum hc B n A.m A.s =>
      {z : Fin n → M | Proper z ∧ (fun i => codeValue (z i)) ∈ {γ | D.Valid A.domain.carrier γ}})
    (fun D => (Section4.Section3GammaCodeBridge.native_iff (hc := hc) _).mp (D.valid_definable A.domain))
    (fun z hz => by
      obtain ⟨D, hD⟩ := A.exists_valid_datum h00 hκ hs hr hγ (fun i => codeValue (z i))
      exact ⟨D, hz, hD⟩)
  refine ⟨J, fun γ => ?_⟩
  obtain ⟨D, hDJ, _, hD⟩ := hJ (rawTuple (representatives γ)) (rawTuple_proper _)
  refine ⟨D, hDJ, ?_⟩
  have he : (fun i => codeValue (rawTuple (representatives γ) i)) = γ := funext fun i => by
    change codeValue (raw (representatives γ i)) = γ i
    rw [codeValue_raw]
    exact congrFun (representatives_values γ) i
  rw [he] at hD
  exact hD

/-- A finite catalog of uniform data with a definable disjoint refinement of
their validity loci covering all of `Γ^n`. -/
theorem uniform_lift_catalog (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (A : GammaVFFamily hc B n) :
    ∃ (K : ℕ) (D : Fin K → GammaWeakLiftDatum hc B n A.m A.s)
      (P : Fin K → Set (Fin n → Values.Gamma (M := M))),
      (∀ l, GammaGroundDefinable hc B (inflatedGammaPower hc n) (P l)) ∧
      (∀ l l', l ≠ l' → Disjoint (P l) (P l')) ∧ (∀ γ, ∃ l, γ ∈ P l) ∧
      (∀ l γ, γ ∈ P l → (D l).Valid A.domain.carrier γ) := by
  obtain ⟨J, hJ⟩ := A.finite_valid_catalog h00 hκ hs hr hγ
  let D : Fin J.card → GammaWeakLiftDatum hc B n A.m A.s := fun l => (J.equivFin.symm l).val
  let V : Fin J.card → Set (Fin n → Values.Gamma (M := M)) :=
    fun l => {γ | (D l).Valid A.domain.carrier γ}
  let P : Fin J.card → Set (Fin n → Values.Gamma (M := M)) :=
    fun l => {γ | γ ∈ V l ∧ ∀ l' : Fin J.card, l' < l → γ ∉ V l'}
  have hV : ∀ l, GammaGroundDefinable hc B (inflatedGammaPower hc n) (V l) :=
    fun l => (D l).valid_definable A.domain
  refine ⟨J.card, D, P, fun l => ?_, ?_, ?_, fun l γ h => h.1⟩
  · apply ((hV l).inter (GammaGroundDefinable.iInter
      (fun l' : {l' : Fin J.card // l' < l} => (hV l'.val).compl))).congr
    intro γ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Subtype.forall]
    exact Iff.rfl
  · intro l l' hne
    rw [Set.disjoint_left]
    intro γ h1 h2
    rcases lt_or_gt_of_ne hne with h | h
    · exact h2.2 l h h1.1
    · exact h1.2 l' h h2.1
  · intro γ
    obtain ⟨E, hE, hEv⟩ := hJ γ
    let t := Finset.univ.filter (fun l : Fin J.card => γ ∈ V l)
    have ht : t.Nonempty := by
      refine ⟨J.equivFin ⟨E, hE⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      change (J.equivFin.symm (J.equivFin ⟨E, hE⟩)).val.Valid A.domain.carrier γ
      rw [Equiv.symm_apply_apply]
      exact hEv
    refine ⟨t.min' ht, (Finset.mem_filter.mp (t.min'_mem ht)).2, fun l' hl' hv => ?_⟩
    have hle := t.min'_le l' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
    exact absurd hl' (not_lt.mpr hle)

end GammaVFFamily

end DiamondIntegral.Section5
