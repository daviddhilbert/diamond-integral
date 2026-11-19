import «section 7».StrictCharts
import «section 7».MeasuredRVBridge
import «section 6».TupleFinitaryLifting
import «section 6».ContinuousRVFamilyMaps
import «section 6».RelativeApertureData
import «section 6».NamedGammaFibreValues
import «section 6».GammaFormMaps
import «section 6».ScalarGammaValues
import «section 6».MeasuredRVLiftGeometry

/-! The centres of the VF lift of an elementary blowup (Lemma 7.12,
`blowup:same:RV:coa`).

For an aperture datum `U = (U, f, ω)`, coordinate `j`, aperture `τ`, the
relation sending the inactive leading terms `r = f_{~j}(u)` to the finitely many
pairs `(f_j(u), τ(u) f_j(u))` is finitary, because `pr_{~j} ↾ f(U)` is
finite-to-one. Lemma 6.30 (in its tuple form, with continuous branches) lifts it
to definable centres `b₀(a, u) ∈ f_j(u)^♯` and `b₁(a, u) ∈ (τ(u) f_j(u))^♯`,
over the full inactive VF input `a ∈ r^♯`. No definable point of `τ(u)^♯` is
chosen. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 DiamondIntegral.Section2 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BlowupLiftData
open DiamondIntegral.Section4
open DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open AnnularBlowup BlowupChart RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

section Relation
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

/-- The inactive structural coordinates `f_{~j}(u)`. -/
def inactCoord (u : Fin D.chart.arity → M) : Fin k → M :=
  fun i => D.chart.coordinate u (BlowupRelation.skip D.coordinate i)

/-- The pair `(f_j(u), τ(u) f_j(u))`. -/
def centrePair (u : Fin D.chart.arity → M) : Fin 2 → M :=
  ![D.chart.coordinate u D.coordinate, iRVMul (D.aperture.aperture u) (D.chart.coordinate u D.coordinate)]

theorem centrePair_nonzero {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) (i : Fin 2) :
    NonzeroRV (centrePair D u i) := by
  have hf : NonzeroRV (D.chart.coordinate u D.coordinate) := by
    have := D.chart.coordinate_proper u hu D.coordinate
    exact ⟨this.1, this.2⟩
  fin_cases i
  · exact hf
  · exact BlowupChart.nonzero_mul (D.aperture.nonzero u hu) hf

theorem inactCoord_nonzero {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) (i : Fin k) :
    NonzeroRV (inactCoord D u i) := by
  have := D.chart.coordinate_proper u hu (BlowupRelation.skip D.coordinate i)
  exact ⟨this.1, this.2⟩

/-- The centre relation: inactive leading terms to the pairs of target leading terms. -/
def centreRel (t : Fin k → RVInfinity M) (v : Fin 2 → RVInfinity M) : Prop :=
  ∃ u ∈ D.chart.domain, inactCoord D u = rvValues t ∧ centrePair D u = rvValues v

theorem inactive_eq_of_inactCoord {u u' : Fin D.chart.arity → M}
    (h : inactCoord D u = inactCoord D u') :
    AnnularBlowup.inactive D.chart D.coordinate u = AnnularBlowup.inactive D.chart D.coordinate u' := by
  funext l
  by_cases hl : l = D.coordinate
  · subst hl
    simp only [AnnularBlowup.inactive, Function.update_self]
  · obtain ⟨i, rfl⟩ := BlowupRelation.exists_skip D.coordinate l hl
    simp only [AnnularBlowup.inactive, Function.update_of_ne hl]
    exact congrFun h i

/-- The raw graph of `u ↦ (f_{~j}(u), f_j(u), τ(u) f_j(u))`. -/
def centreMap (u : Fin D.chart.arity → M) : Fin (2 + k) → M := join 2 k (inactCoord D u) (centrePair D u)

theorem centreMap_tupleDef : TupleDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain (centreMap D) := by
  have hI := D.chart.domain_definable
  have hc : TupleDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain D.chart.coordinate := D.chart.coordinate_definable
  have hcomp (l : Fin (1 + k)) : ScalarDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain
      (fun u => D.chart.coordinate u l) := scalarDef_comp_component hI hc l
  apply tupleDef_of_scalar hI
  intro i
  rcases block_cases 2 k i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · simpa only [centreMap, join_head, inactCoord] using hcomp (BlowupRelation.skip D.coordinate i')
  · simp only [centreMap, join_tail]
    fin_cases i'
    · exact hcomp D.coordinate
    · exact scalarDef_mul hI D.aperture.graph_definable (hcomp D.coordinate)

/-- The finitary relation of Lemma 6.30 for the centres. -/
def centreRelation : DiamondIntegral.Section6.FinitaryRVRelation S k 2 where
  rel := centreRel D
  definable := by
    have hW := base_real (BoundedClasses.graph_image_definable D.chart.domain (centreMap D)
      (centreMap_tupleDef D))
    let σ : Fin (2 + k) → Fin k ⊕ Fin 2 := join 2 k Sum.inl Sum.inr
    convert hW.preimage_comp σ using 1
    apply Set.ext
    intro z
    have hzh : (z ∘ σ) ∘ headIndex 2 k = z ∘ Sum.inl := by
      funext i
      simp only [Function.comp_apply, σ, join_head]
    have hzt : (z ∘ σ) ∘ tailIndex 2 k = z ∘ Sum.inr := by
      funext i
      simp only [Function.comp_apply, σ, join_tail]
    constructor
    · rintro ⟨t, v, ⟨u, hu, ht, hv⟩, hzt', hzv⟩
      refine ⟨u, hu, ?_⟩
      change centreMap D u = z ∘ σ
      rw [← join_reconstruct 2 k (z ∘ σ), hzh, hzt, centreMap, ht, hv, hzt', hzv]
    · rintro ⟨u, hu, he⟩
      have he' : centreMap D u = z ∘ σ := he
      have h1 : inactCoord D u = z ∘ Sum.inl := by
        rw [← hzh, ← he']
        funext i
        simp only [Function.comp_apply, centreMap, join_head]
      have h2 : centrePair D u = z ∘ Sum.inr := by
        rw [← hzt, ← he']
        funext i
        simp only [Function.comp_apply, centreMap, join_tail]
      refine ⟨rvTuple (inactCoord D u) (fun i => (inactCoord_nonzero D hu i).1),
        rvTuple (centrePair D u) (fun i => (centrePair_nonzero D hu i).1), ⟨u, hu, rfl, rfl⟩, ?_, ?_⟩
      · exact h1
      · exact h2
  finite := by
    intro t
    by_cases hne : ∃ u0 ∈ D.chart.domain, inactCoord D u0 = rvValues t
    · obtain ⟨u0, hu0, he0⟩ := hne
      have hF := (D.finite (AnnularBlowup.inactive D.chart D.coordinate u0)).image (centrePair D)
      refine Set.Finite.of_finite_image (f := rvValues) (hF.subset ?_) rvValues_injective.injOn
      rintro _ ⟨v, ⟨u, hu, ht, hv⟩, rfl⟩
      exact ⟨u, ⟨hu, inactive_eq_of_inactCoord D (ht.trans he0.symm)⟩, hv⟩
    · apply Set.Finite.subset Set.finite_empty
      rintro v ⟨u, hu, ht, _⟩
      exact hne ⟨u, hu, ht⟩
  source := by
    rintro t v ⟨u, hu, ht, _⟩ i hi
    have h := (inactCoord_nonzero D hu i).2
    rw [ht] at h
    exact h (congrArg Subtype.val hi)

end Relation

/-! ### The centres on the lift -/

section Centres
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : DiamondIntegral.Section6.TupleFinitaryLift (centreRelation D))

/-- The lifted object `𝕃U`: the Section 6 carrier of the measured object. -/
abbrev liftSet : DefSet (rawMixedSpace (M := M) (1 + k) D.chart.arity) S :=
  rvLift (toMeasured hc D.chart).object

/-- The inactive VF coordinates. -/
def inact (x : Fin (1 + k) → VF M) : Fin k → VF M := fun i => x (BlowupRelation.skip D.coordinate i)

/-- The target leading terms of a label, as an RV tuple (zero off the domain). -/
def vpair (l : Fin D.chart.arity → RVInfinity M) : Fin 2 → RVInfinity M :=
  if h : rvValues l ∈ D.chart.domain then
    rvTuple (centrePair D (rvValues l)) (fun i => (centrePair_nonzero D h i).1)
  else fun _ => rvZero M

/-- The centres: `b₀` (index `0`) in `f_j(u)^♯` and `b₁` (index `1`) in
`(τ(u) f_j(u))^♯`. -/
def centre (i : Fin 2) (x : Fin (1 + k) → VF M) (l : Fin D.chart.arity → RVInfinity M) : VF M :=
  L.center (DiamondIntegral.Section6.liftCode (inact D x) (vpair D l)) i

theorem mem_liftSet_iff (p : Mixed M (1 + k) D.chart.arity) :
    p ∈ (liftSet hc D).carrier ↔
      rvValues p.2 ∈ D.chart.domain ∧ rvValues (tupleRV M p.1) = D.chart.coordinate (rvValues p.2) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hd : rvValues u.val ∈ D.chart.domain := u.property
    rw [hu] at hd
    refine ⟨hd, ?_⟩
    have h1 : rvValues (tupleRV M p.1) = rvValues ((toMeasured hc D.chart).object.value u) := by
      rw [hv]
      rfl
    rw [h1, ← hu]
    rfl
  · rintro ⟨hd, hv⟩
    refine ⟨⟨p.2, hd⟩, rfl, ?_⟩
    apply rvValues_injective
    change D.chart.coordinate (rvValues p.2) = rvValues (tupleRV M p.1)
    exact hv.symm

theorem rel_of_mem {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) :
    centreRel D (tupleRV M (inact D p.1)) (vpair D p.2) := by
  obtain ⟨hd, hv⟩ := (mem_liftSet_iff hc D p).mp hp
  refine ⟨rvValues p.2, hd, ?_, ?_⟩
  · funext i
    exact (congrFun hv (BlowupRelation.skip D.coordinate i)).symm
  · rw [vpair, dif_pos hd]
    rfl

theorem centre_rv {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (i : Fin 2) :
    (rv M (centre D L i p.1 p.2)).val = centrePair D (rvValues p.2) i := by
  have h := L.prescribed (inact D p.1) (vpair D p.2) (rel_of_mem hc D hp) i
  obtain ⟨hd, _⟩ := (mem_liftSet_iff hc D p).mp hp
  rw [centre, h, vpair, dif_pos hd]
  rfl

theorem centre_update (i : Fin 2) (x : Fin (1 + k) → VF M) (l : Fin D.chart.arity → RVInfinity M) (c : VF M) :
    centre D L i (Function.update x D.coordinate c) l = centre D L i x l := by
  have h : inact D (Function.update x D.coordinate c) = inact D x := by
    funext m
    exact Function.update_of_ne (BlowupRelation.skip_ne D.coordinate m) _ _
  rw [centre, centre, h]

theorem coord_rv {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (l : Fin (1 + k)) :
    (rv M (p.1 l)).val = D.chart.coordinate (rvValues p.2) l :=
  congrFun ((mem_liftSet_iff hc D p).mp hp).2 l

end Centres

/-! ### Section 6 maps from definable label families -/

section Families

omit hM in
theorem sortEval_rv (x : M) : sortEval SortTag.rv x ↔ iRV x := Iff.rfl

omit hM in
theorem sortEval_vf (x : M) : sortEval SortTag.vf x ↔ iVF x := Iff.rfl

theorem sort_coord_definable {α : Type*} (s : SortTag) (j : α) :
    S.Definable LRV {z : α → M | sortEval s (z j)} := by
  have h := base_real (real_definableOverBase (⟨S, ∅⟩ : Base (M := M)) (fun _ : Fin 1 => s) _
    (sortedUniverse_definable S (fun _ : Fin 1 => s)))
  have h' := h.preimage_comp (fun _ : Fin 1 => j)
  convert h' using 1
  apply Set.ext
  intro z
  constructor
  · intro hz i
    exact hz
  · intro hz
    exact hz 0

theorem sorts_definable {α β : Type*} [Finite β] (s : SortTag) (e : β → α) :
    S.Definable LRV {z : α → M | ∀ i, sortEval s (z (e i))} := by
  have := Fintype.ofFinite β
  have h := Set.definable_biInter_finset (A := S) (L := LRV) (fun i => sort_coord_definable (S := S) s (e i))
    (Finset.univ : Finset β)
  convert h using 1
  apply Set.ext
  intro z
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, true_implies]

/-- The graph of a label-indexed VF family given by a definable map of codes is
definable. -/
theorem rvVFGraph_definable {n r m : ℕ}
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (F : (Fin r ⊕ Fin n → M) → Fin m → M) (hF : S.DefinableMap LRV F)
    (hf : ∀ u x i, (f u x i).val = F (Sum.elim (rvValues u) (vfValues x)) i) :
    S.Definable LRV (DiamondIntegral.Section6.rvVFGraph f) := by
  let code : (Fin r ⊕ (Fin n ⊕ Fin m) → M) → (Fin r ⊕ Fin n → M) :=
    fun z => Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr ∘ Sum.inl)
  have hcode : S.DefinableMap LRV code := by
    rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have hEq (i : Fin m) : S.Definable LRV {z : Fin r ⊕ (Fin n ⊕ Fin m) → M | z (.inr (.inr i)) = F (code z) i} :=
    Set.DefinableFun.ofPred_eq (Set.DefinableFun.proj LRV) (Set.DefinableFun.comp hcode (hF i))
  have hE := Set.definable_biInter_finset (A := S) (L := LRV) (fun i => hEq i) (Finset.univ : Finset (Fin m))
  have h := ((sorts_definable (S := S) SortTag.rv (Sum.inl : Fin r → Fin r ⊕ (Fin n ⊕ Fin m))).inter
    (sorts_definable (S := S) SortTag.vf (fun i : Fin n => (Sum.inr (Sum.inl i) : Fin r ⊕ (Fin n ⊕ Fin m))))).inter hE
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨u, x, rfl⟩
    refine ⟨⟨fun i => (u i).property, fun i => (x i).property⟩, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_setOf_eq]
    intro i
    change (f u x i).val = F (code (Sum.elim (rvValues u) (Sum.elim (vfValues x) (vfValues (f u x))))) i
    rw [hf]
    rfl
  · rintro ⟨⟨hr, hv⟩, he⟩
    simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_setOf_eq] at he
    let u : Fin r → RVInfinity M := fun i => ⟨z (.inl i), hr i⟩
    let x : Fin n → VF M := fun i => ⟨z (.inr (.inl i)), hv i⟩
    refine ⟨u, x, ?_⟩
    funext i
    rcases i with i | i | i
    · rfl
    · rfl
    · change (f u x i).val = z (.inr (.inr i))
      rw [hf, he i]
      rfl

end Families

/-! ### The centres as Section 6 maps -/

section CentreMaps
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : DiamondIntegral.Section6.TupleFinitaryLift (centreRelation D))

/-- The raw target leading terms of a label (zero off the domain). -/
def vcode (y : Fin D.chart.arity → M) : Fin 2 → M :=
  if y ∈ D.chart.domain then centrePair D y else fun _ => iRVZero

theorem rvValues_vpair (l : Fin D.chart.arity → RVInfinity M) : rvValues (vpair D l) = vcode D (rvValues l) := by
  unfold vpair vcode
  by_cases h : rvValues l ∈ D.chart.domain
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]
    rfl

theorem zero_singleton_definable :
    S.Definable LRV {z : Fin 1 → M | z ∈ ({![iRVZero]} : Set (Fin 1 → M))} :=
  base_real (tuple_singleton_definable_base (⟨S, ∅⟩ : Base (M := M)) (fun _ : Fin 1 => .rv) ![iRVZero]
    (fun i => by fin_cases i; exact RVNamedTuples.zero_definable _))

theorem vcode_definable (t : Fin 2) : S.DefinableFun LRV (fun y : Fin D.chart.arity → M => vcode D y t) := by
  have hdom := base_real D.chart.domain_definable
  have hg : ScalarDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain (fun u => centrePair D u t) :=
    scalarDef_comp_component D.chart.domain_definable (centreMap_tupleDef D |> fun h =>
      tupleDef_comp (G := fun w : Fin (2 + k) → M => w ∘ tailIndex 2 k) h
        (tupleDef_coord (BoundedClasses.graph_image_definable _ _ h) _) (fun u hu => ⟨u, hu, rfl⟩)) t |>
    fun h => by
      unfold ScalarDef at h ⊢
      convert h using 3
      funext u
      simp only [Function.comp_apply, centreMap, join_tail]
  have h1 := (base_real hg).preimage_comp (join 1 D.chart.arity Option.some (fun _ => Option.none))
  have h2 := (hdom.compl.preimage_comp Option.some).inter
    ((zero_singleton_definable (S := S)).preimage_comp (fun _ : Fin 1 => (Option.none : Option (Fin D.chart.arity))))
  unfold Set.DefinableFun
  convert h1.union h2 using 1
  apply Set.ext
  intro v
  have hh : (v ∘ join 1 D.chart.arity Option.some (fun _ => Option.none)) ∘ headIndex 1 D.chart.arity =
      v ∘ Option.some := by
    funext i
    simp only [Function.comp_apply, join_head]
  have ht : (v ∘ join 1 D.chart.arity Option.some (fun _ => Option.none)) ∘ tailIndex 1 D.chart.arity =
      ![v Option.none] := by
    funext i
    fin_cases i
    simp only [Function.comp_apply, join_tail]
    rfl
  change vcode D (v ∘ Option.some) t = v Option.none ↔ _
  by_cases hd : v ∘ Option.some ∈ D.chart.domain
  · simp only [vcode, if_pos hd]
    constructor
    · intro he
      refine Or.inl ⟨by rw [hh]; exact hd, ?_⟩
      rw [hh, ht]
      change ![centrePair D (v ∘ Option.some) t] = ![v Option.none]
      rw [he]
    · rintro (⟨_, he⟩ | ⟨hn, _⟩)
      · rw [hh, ht] at he
        exact congrFun he 0
      · exact absurd hd hn
  · simp only [vcode, if_neg hd]
    constructor
    · intro he
      refine Or.inr ⟨hd, ?_⟩
      change (fun _ : Fin 1 => v Option.none) ∈ ({![iRVZero]} : Set (Fin 1 → M))
      rw [← he]
      funext i
      fin_cases i
      rfl
    · rintro (⟨hm, _⟩ | ⟨_, he⟩)
      · rw [hh] at hm
        exact absurd hm hd
      · exact (congrFun he 0).symm

/-- The code of the centre input. -/
def centreCode (w : Fin D.chart.arity ⊕ Fin (1 + k) → M) : Fin k ⊕ Fin 2 → M :=
  Sum.elim (fun m => w (.inr (BlowupRelation.skip D.coordinate m))) (vcode D (w ∘ Sum.inl))

theorem centreCode_definable : S.DefinableMap LRV (centreCode D) := by
  rintro (m | t)
  · exact Set.DefinableFun.proj LRV
  · have hin : S.DefinableMap LRV (fun w : Fin D.chart.arity ⊕ Fin (1 + k) → M => w ∘ Sum.inl) :=
      fun i => Set.DefinableFun.proj LRV
    exact Set.DefinableFun.comp hin (vcode_definable D t)

theorem centre_val (i : Fin 2) (x : Fin (1 + k) → VF M) (l : Fin D.chart.arity → RVInfinity M) :
    (centre D L i x l).val = (L.center (centreCode D (Sum.elim (rvValues l) (vfValues x))) i).val := by
  have h : DiamondIntegral.Section6.liftCode (inact D x) (vpair D l) =
      centreCode D (Sum.elim (rvValues l) (vfValues x)) := by
    funext z
    rcases z with m | t
    · rfl
    · change rvValues (vpair D l) t = vcode D (rvValues l) t
      rw [rvValues_vpair]
  rw [centre, h]

theorem centre_family_definable (i : Fin 2) :
    S.Definable LRV (DiamondIntegral.Section6.rvVFGraph
      (fun (l : Fin D.chart.arity → RVInfinity M) (x : Fin (1 + k) → VF M) => ![centre D L i x l])) := by
  apply rvVFGraph_definable _ (fun w _ => (L.center (centreCode D w) i).val)
  · intro _
    exact Set.DefinableFun.comp (centreCode_definable D) (L.definable i)
  · intro l x t
    fin_cases t
    exact centre_val D L i x l

/-- The centre `b_i` as a Section 6 map on a definable piece of the lift. -/
def centreMapOn (i : Fin 2) (A : DefSet (rawMixedSpace (M := M) (1 + k) D.chart.arity) S) :
    Map A (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  DiamondIntegral.Section6.rvFamilyMap A _ (centre_family_definable D L i)

theorem centreMapOn_apply (i : Fin 2) (A : DefSet (rawMixedSpace (M := M) (1 + k) D.chart.arity) S) (p : A) :
    (centreMapOn D L i A p).val 0 = centre D L i p.val.1 p.val.2 := rfl

end CentreMaps

/-! ### Values of points of the lift -/

section Values
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

theorem vfValue_eq_codeValue {a : VF M} {c : M} (h : (rv M a).val = c) (hc' : NonzeroRV c) :
    vfValue a = (codeValue c).val := by
  have he : rv M a = ⟨c, hc'.1⟩ := Subtype.ext h
  rw [show vfValue a = Values.vrv (rv M a) from rfl, he]
  exact (nonzero_rv_codeValue_val ⟨c, hc'.1⟩ (fun h0 => hc'.2 (congrArg Subtype.val h0))).symm

theorem ne_zero_of_rv {a : VF M} {c : M} (h : (rv M a).val = c) (hc' : NonzeroRV c) : a ≠ 0 := by
  intro h0
  rw [h0] at h
  have := congrArg Subtype.val (rv_zero (M := M))
  exact hc'.2 (h.symm.trans this)

theorem coord_nonzero {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (l : Fin (1 + k)) :
    NonzeroRV (D.chart.coordinate (rvValues p.2) l) := by
  have h := D.chart.coordinate_proper _ ((mem_liftSet_iff hc D p).mp hp).1 l
  exact ⟨h.1, h.2⟩

/-- The Gamma value of coordinate `l` of a lifted point, as a Section 6 map. -/
def coordGammaMap (A : DefSet (rawMixedSpace (M := M) (1 + k) D.chart.arity) S) (l : Fin (1 + k)) :
    Map A (DefSet.univ (DiamondIntegral.Section6.rawGammaPresentation (M := M)) S) :=
  (DiamondIntegral.Section6.scalarGammaValueMap S).comp
    (DiamondIntegral.Section6.rvFamilyMap A (fun _ x => ![x l])
      (rvVFGraph_definable _ (fun w _ => w (.inr l)) (fun _ => Set.DefinableFun.proj LRV)
        (fun _ x t => by fin_cases t; rfl)))

theorem coordGammaMap_val (A : DefSet (rawMixedSpace (M := M) (1 + k) D.chart.arity) S) (l : Fin (1 + k))
    (p : A) (hp : p.val.1 l ≠ 0) : ((coordGammaMap D A l p).val : Gamma M).val = vfValue (p.val.1 l) :=
  DiamondIntegral.Section6.scalarGammaValueMap_nonzero S ![p.val.1 l] hp

include hc in
/-- The value of a coordinate of the lifted fibre over a label is named over the
label. -/
theorem coord_value_named {u : Fin D.chart.arity → RVInfinity M} (hu : rvValues u ∈ D.chart.domain)
    (l : Fin (1 + k)) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {codeValue (D.chart.coordinate (rvValues u) l)}} := by
  let A := liftSet hc D
  let f := coordGammaMap D A l
  have hrv : ∀ m, iRV (D.chart.coordinate (rvValues u) m) := fun m => (D.chart.coordinate_proper _ hu m).1
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun m => (⟨D.chart.coordinate (rvValues u) m, hrv m⟩ :
    RVInfinity M))
  have hmem : (x, u) ∈ A.carrier := by
    refine (mem_liftSet_iff hc D (x, u)).mpr ⟨hu, ?_⟩
    rw [hx]
    rfl
  apply DiamondIntegral.Section6.gamma_value_named_on_rv_fibre A.carrier
    (DiamondIntegral.Section6.gammaFormExtension f) (DiamondIntegral.Section6.gammaFormExtension_graph_definable f)
    u _ ⟨(x, u), hmem, rfl⟩
  intro p hp hpu
  rw [DiamondIntegral.Section6.gammaFormExtension_at f ⟨p, hp⟩]
  have hcr := coord_rv hc D hp l
  rw [hpu] at hcr
  have hnz : NonzeroRV (D.chart.coordinate (rvValues u) l) := ⟨hrv l, (D.chart.coordinate_proper _ hu l).2⟩
  apply Subtype.ext
  rw [coordGammaMap_val D A l ⟨p, hp⟩ (ne_zero_of_rv hcr hnz)]
  exact vfValue_eq_codeValue hcr hnz

end Values

/-! ### The relative aperture data of the lift -/

section ApertureData
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : DiamondIntegral.Section6.TupleFinitaryLift (centreRelation D))
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hU : (toMeasured hc D.chart).doublyBounded)
variable (hP : DiamondIntegral.Section6.ProperInvariant S (liftSet hc D).carrier)
variable (Δ : Values.Gamma (M := M))
variable (hΔ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}})
variable (hΔ1 : 1 ≤ Δ) (hΔb : ∀ u ∈ D.chart.domain, codeValue (D.aperture.aperture u) ≤ Δ)

/-- The active labels: all labels of the lift. -/
abbrev tags : DefSet (rawRVSpace (M := M) D.chart.arity) S := (toMeasured hc D.chart).object.domain

theorem mem_of_focusActive (p : DiamondIntegral.Section6.focusActive (liftSet hc D) (tags hc D)) :
    p.val ∈ (liftSet hc D).carrier := p.property.1

theorem vfValue_centre {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (i : Fin 2) :
    vfValue (centre D L i p.1 p.2) = (codeValue (centrePair D (rvValues p.2) i)).val :=
  vfValue_eq_codeValue (centre_rv hc D L hp i)
    (centrePair_nonzero D ((mem_liftSet_iff hc D p).mp hp).1 i)

theorem centre_ne_zero {p : Mixed M (1 + k) D.chart.arity} (hp : p ∈ (liftSet hc D).carrier) (i : Fin 2) :
    centre D L i p.1 p.2 ≠ 0 :=
  ne_zero_of_rv (centre_rv hc D L hp i) (centrePair_nonzero D ((mem_liftSet_iff hc D p).mp hp).1 i)

theorem centrePair_le {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    codeValue (centrePair D u 0) ≤ codeValue (centrePair D u 1) := by
  have hf : NonzeroRV (D.chart.coordinate u D.coordinate) :=
    ⟨(D.chart.coordinate_proper u hu D.coordinate).1, (D.chart.coordinate_proper u hu D.coordinate).2⟩
  change codeValue (D.chart.coordinate u D.coordinate) ≤
    codeValue (iRVMul (D.aperture.aperture u) (D.chart.coordinate u D.coordinate))
  rw [GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero u hu) hf]
  exact le_mul_of_one_le_left' (D.aperture.nonnegative u hu)

include hv in
theorem centre_continuous (i : Fin 2) (u : Fin D.chart.arity → RVInfinity M) :
    ContinuousOn (fun x => centre D L i (Function.update x D.coordinate 0) u)
      (vfFibre (liftSet hc D).carrier u) := by
  intro x hx
  have hfun : (fun x => centre D L i (Function.update x D.coordinate 0) u) =
      (fun v : Fin 2 → VF M => v i) ∘
        (fun a' => L.center (DiamondIntegral.Section6.liftCode a' (vpair D u))) ∘ inact D := by
    funext y
    rw [centre_update]
    rfl
  rw [hfun]
  have hrel : centreRel D (tupleRV M (inact D x)) (vpair D u) := rel_of_mem hc D (p := (x, u)) hx
  have h1 := L.continuousAt hv (inact D x) (vpair D u) hrel
  have h2 : Continuous (inact D) := continuous_pi (fun m => continuous_apply _)
  exact ((continuous_apply i).continuousAt.comp (h1.comp h2.continuousAt)).continuousWithinAt

include hU hP hΔ hΔ1 hΔb in
/-- Section 6's relative aperture data for the lift of an elementary blowup:
focus `b₀`, endpoint `b₁`, named bound `Δ`. -/
def apertureData : DiamondIntegral.Section6.RelativeApertureData (G := G) (liftSet hc D) where
  coordinate := D.coordinate
  activeTags := tags hc D
  focus := centre D L 0
  focusMap := centreMapOn D L 0 _
  focusMap_eq := fun p => by
    rw [centreMapOn_apply, centre_update]
  sourceProper := hP
  sourceDoublyBounded := DiamondIntegral.Section6.measuredRVLift_vfDoublyBounded _ hU
  tagged := fun p hp q hq he => by
    apply rvValues_injective
    rw [((mem_liftSet_iff hc D p).mp hp).2, ((mem_liftSet_iff hc D q).mp hq).2, he]
  continuous := fun u _ => centre_continuous hc D L hv 0 u
  focusRV := fun p hp _ => by
    apply Subtype.ext
    rw [centre_update, centre_rv hc D L hp 0, coord_rv hc D hp]
    rfl
  endpoint := centre D L 1
  endpointMap := centreMapOn D L 1 _
  endpointMap_eq := fun p => by
    rw [centreMapOn_apply, centre_update]
  endpoint_continuous := fun u _ => centre_continuous hc D L hv 1 u
  endpoint_nonzero := fun p => by
    rw [centre_update]
    exact centre_ne_zero hc D L (mem_of_focusActive hc D p) 1
  endpoint_nonnegative := fun p => by
    rw [centre_update, centre_update, vfValue_centre hc D L (mem_of_focusActive hc D p),
      vfValue_centre hc D L (mem_of_focusActive hc D p)]
    exact centrePair_le D ((mem_liftSet_iff hc D _).mp (mem_of_focusActive hc D p)).1
  endpoint_RV_constant := fun p q he => by
    apply Subtype.ext
    rw [centreMapOn_apply, centreMapOn_apply, centre_rv hc D L (mem_of_focusActive hc D p),
      centre_rv hc D L (mem_of_focusActive hc D q), he]
  apertureBound := Δ
  apertureBound_nonnegative := hΔ1
  apertureBound_named := hΔ
  endpoint_upper_bound := fun p => by
    have hp := mem_of_focusActive hc D p
    have hd := ((mem_liftSet_iff hc D _).mp hp).1
    rw [centreMapOn_apply, vfValue_centre hc D L hp,
      vfValue_eq_codeValue (coord_rv hc D hp D.coordinate) (coord_nonzero hc D hp D.coordinate)]
    have hf := coord_nonzero hc D hp D.coordinate
    change (codeValue (iRVMul (D.aperture.aperture (rvValues p.val.2))
      (D.chart.coordinate (rvValues p.val.2) D.coordinate))).val ≤ _
    rw [GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hd) hf,
      ← SpecialTransformations.Section3.Values.gamma_val_mul]
    exact mul_le_mul_left (hΔb _ hd) _
  covariance := fun u hu => by
    have hu' : rvValues u ∈ D.chart.domain := hu
    refine ⟨codeValue (D.chart.coordinate (rvValues u) D.coordinate),
      fun l => codeValue (D.chart.coordinate (rvValues u) l), coord_value_named hc D hu' D.coordinate,
      fun l => coord_value_named hc D hu' l, ?_, ?_, ?_⟩
    · have hstep : ∀ a b : Fin (1 + k) → VF M, (a, u) ∈ (liftSet hc D).carrier →
          DiamondIntegral.Section6.Congruent (fun l => if l = D.coordinate then
            codeValue (D.chart.coordinate (rvValues u) D.coordinate)
            else codeValue (D.chart.coordinate (rvValues u) l)) b a → (b, u) ∈ (liftSet hc D).carrier := by
        intro a b ha hba
        obtain ⟨hd, hrv⟩ := (mem_liftSet_iff hc D (a, u)).mp ha
        refine (mem_liftSet_iff hc D (b, u)).mpr ⟨hd, ?_⟩
        funext l
        have hal : (rv M (a l)).val = D.chart.coordinate (rvValues u) l := congrFun hrv l
        have hnz : NonzeroRV (D.chart.coordinate (rvValues u) l) :=
          ⟨(D.chart.coordinate_proper _ hd l).1, (D.chart.coordinate_proper _ hd l).2⟩
        have hlt : vfValue (a l) < vfValue (b l - a l) := by
          rw [vfValue_eq_codeValue hal hnz]
          have h := hba l
          by_cases hl : l = D.coordinate
          · subst hl
            simp only [if_true] at h
            exact h
          · simp only [if_neg hl] at h
            exact h
        have he := (DiamondIntegral.Section6.rv_eq_iff_value_close (ne_zero_of_rv hal hnz)).mpr hlt
        change (rv M (b l)).val = _
        rw [he]
        exact hal
      intro a b hab
      exact ⟨fun ha => hstep a b ha (DiamondIntegral.Section6.Congruent.symm hab),
        fun hb => hstep b a hb hab⟩
    · intro a ha b hb _
      rw [centre_update, centre_update]
      have hra := centre_rv hc D L (p := (a, u)) ha 0
      have hrb := centre_rv hc D L (p := (b, u)) hb 0
      have he : rv M (centre D L 0 a u) = rv M (centre D L 0 b u) := Subtype.ext (hra.trans hrb.symm)
      have hlt := (DiamondIntegral.Section6.rv_eq_iff_value_close (centre_ne_zero hc D L (p := (b, u)) hb 0)).mp he
      rw [vfValue_centre hc D L (p := (b, u)) hb 0] at hlt
      exact hlt
    · intro a ha
      rw [centre_update, vfValue_centre hc D L (p := (a, u)) ha 1]
      exact centrePair_le D hu'

end ApertureData

end DiamondIntegral.Section7.BlowupLiftData
