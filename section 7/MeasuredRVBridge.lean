import «section 4».Section3RVCodeBridge
import «section 6».MeasuredRVIsomorphisms
import «section 4».RVMeasuredCharts
import «section 4».RVVolumeMaps
import «section 4».RVMeasuredIsomorphisms

/-! Bridge from Section 4's raw RV charts to the measured RV objects used by
Section 6's lifting theorems, over a base with no Gamma names.

Over `⟨S, ∅⟩` a Section 3 ground-definable set is definable over `S` itself:
no Gamma name can occur, and a definition with the empty tuple of names is a
definition over `S` with the empty code. This lets chart domains and maps be
read as special-transformations `DefSet`s and `Map`s over `S`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M))

/-- Over a base with no Gamma names, ground definability is definability over
the real parameters. -/
theorem noNames_real {S : Set M} {Q : Space LRV M} {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc (⟨S, ∅⟩ : GammaParameters.Base (M := M)) Q A) :
    Q.Definable S A := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  cases k with
  | succ k => exact (hγ 0).elim
  | zero =>
    let c : ((volumeGammaSpace hc).power (Fin 0)).domain := ⟨fun x => x.1.elim0, fun i => i.elim0⟩
    have hp : ((volumeGammaSpace hc).power (Fin 0)).decode c = γ := funext (fun i => i.elim0)
    have h := hA.over_real_code c hp
    have hS : realCodeParameters S c = S := by
      have he : Set.range c.val = ∅ := by
        ext x
        simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false, not_exists]
        intro y
        exact y.1.elim0
      show S ∪ Set.range c.val = S
      rw [he, Set.union_empty]
    rwa [hS] at h

/-- A ground-definable set over `⟨S, ∅⟩`, as a `DefSet` over `S`. -/
def toDefSet {S : Set M} {Q : Space LRV M}
    (A : GammaGroundDefSet hc (⟨S, ∅⟩ : GammaParameters.Base (M := M)) Q) : DefSet Q S :=
  ⟨A.carrier, noNames_real hc A.definable⟩

/-- A ground map over `⟨S, ∅⟩`, as a `Map` over `S`. -/
def toMap {S : Set M} {Q R : Space LRV M}
    {A : GammaGroundDefSet hc (⟨S, ∅⟩ : GammaParameters.Base (M := M)) Q}
    {D : GammaGroundDefSet hc (⟨S, ∅⟩ : GammaParameters.Base (M := M)) R}
    (f : GammaGroundMap A D) : Map (toDefSet hc A) (toDefSet hc D) where
  toFun := fun a => ⟨(f ⟨a.val, a.property⟩).val, (f ⟨a.val, a.property⟩).property⟩
  graph_definable := by
    apply (relationDefinable_iff_product _).mpr
    exact noNames_real hc f.graph_definable

theorem toMap_val {S : Set M} {Q R : Space LRV M}
    {A : GammaGroundDefSet hc (⟨S, ∅⟩ : GammaParameters.Base (M := M)) Q}
    {D : GammaGroundDefSet hc (⟨S, ∅⟩ : GammaParameters.Base (M := M)) R}
    (f : GammaGroundMap A D) (a : toDefSet hc A) :
    ((toMap hc f) a).val = (f ⟨a.val, a.property⟩).val := rfl

/-- Over a base with no Gamma names, raw sorted definability is definability
over the real parameters. -/
theorem base_real {S : Set M} {n : ℕ} {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) sn A) :
    S.Definable LRV A := by
  obtain ⟨k, γ, hγ, hA⟩ := hA
  cases k with
  | succ k => exact (hγ 0).elim
  | zero =>
    have hγ0 : γ = Fin.elim0 := funext (fun i => i.elim0)
    subst hγ0
    exact ((with_zero_iff S Fin.elim0 sn A).mp hA).raw_definable

open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks

/-- A raw definable RV set over `⟨S, ∅⟩`, as a `DefSet` of `rawRVSpace`. -/
def rawDefSet {S : Set M} {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I) :
    DefSet (rawRVSpace (M := M) n) S :=
  toDefSet hc (Section3RVCodeBridge.ofRaw (hc := hc) I hI)

theorem mem_rawDefSet {S : Set M} {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I)
    (a : Fin n → CanonicalRV.RVSort M) : a ∈ (rawDefSet hc I hI).carrier ↔ rvValues a ∈ I :=
  Iff.rfl

theorem decode_rv {n : ℕ} (z : (rawRVSpace (M := M) n).domain) :
    rvValues ((rawRVSpace (M := M) n).decode z) = z.val :=
  Space.ofEmbedding_decode _ _ _ z

/-- The RV tuple with given raw values, when they are RV elements. -/
def rvTuple {k : ℕ} (x : Fin k → M) (hx : ∀ i, iRV (x i)) : Fin k → CanonicalRV.RVSort M :=
  fun i => ⟨x i, hx i⟩

omit [M ⊨ Axioms.ACVF] in
theorem rvValues_rvTuple {k : ℕ} (x : Fin k → M) (hx : ∀ i, iRV (x i)) :
    rvValues (rvTuple x hx) = x := rfl

/-- A raw map with definable graph, as a `Map` into the RV tuples. -/
def rawMap {S : Set M} {n k : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I)
    (F : (Fin n → M) → (Fin k → M))
    (hF : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (k + n) => .rv)
      (graphOn I F))
    (hrv : ∀ x ∈ I, ∀ i, iRV (F x i)) :
    Map (rawDefSet hc I hI) (DefSet.univ (rawRVSpace (M := M) k) S) where
  toFun a := ⟨rvTuple (F (rvValues a.val)) (hrv _ a.property), Set.mem_univ _⟩
  graph_definable := by
    let σ : Fin (k + n) → Fin n ⊕ Fin k := join k n Sum.inl Sum.inr
    have h := (base_real hF).preimage_comp σ
    show S.Definable LRV ((rawRVSpace (M := M) n).relation (rawRVSpace (M := M) k) _)
    have hset : (rawRVSpace (M := M) n).relation (rawRVSpace (M := M) k)
        (fun x y => ∃ a : rawDefSet hc I hI, a.val = x ∧
          (⟨rvTuple (F (rvValues a.val)) (hrv _ a.property), Set.mem_univ _⟩ :
            DefSet.univ (rawRVSpace (M := M) k) S).val = y) =
        (fun g : Fin n ⊕ Fin k → M => g ∘ σ) ⁻¹' graphOn I F := by
      ext z
      constructor
      · rintro ⟨hx, hy, a, ha, hb⟩
        have hzx : z ∘ Sum.inl = rvValues a.val := by
          rw [ha, decode_rv]
        have hzy : z ∘ Sum.inr = F (rvValues a.val) := by
          have := congrArg rvValues hb
          rw [decode_rv] at this
          exact this.symm
        refine ⟨?_, ?_⟩
        · change (z ∘ σ) ∘ headIndex k n ∈ I
          have : (z ∘ σ) ∘ headIndex k n = z ∘ Sum.inl := funext (fun i => by
            simp only [Function.comp_apply, σ, join_head])
          rw [this, hzx]
          exact a.property
        · change F ((z ∘ σ) ∘ headIndex k n) = (z ∘ σ) ∘ tailIndex k n
          have h1 : (z ∘ σ) ∘ headIndex k n = z ∘ Sum.inl := funext (fun i => by
            simp only [Function.comp_apply, σ, join_head])
          have h2 : (z ∘ σ) ∘ tailIndex k n = z ∘ Sum.inr := funext (fun i => by
            simp only [Function.comp_apply, σ, join_tail])
          rw [h1, h2, hzx, hzy]
      · rintro ⟨hz1, hz2⟩
        have h1 : (z ∘ σ) ∘ headIndex k n = z ∘ Sum.inl := funext (fun i => by
          simp only [Function.comp_apply, σ, join_head])
        have h2 : (z ∘ σ) ∘ tailIndex k n = z ∘ Sum.inr := funext (fun i => by
          simp only [Function.comp_apply, σ, join_tail])
        change (z ∘ σ) ∘ headIndex k n ∈ I at hz1
        change F ((z ∘ σ) ∘ headIndex k n) = (z ∘ σ) ∘ tailIndex k n at hz2
        rw [h1] at hz1
        rw [h1, h2] at hz2
        have hx : z ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain :=
          ⟨rvTuple (z ∘ Sum.inl) (hI.proper _ hz1), rfl⟩
        have hy : z ∘ Sum.inr ∈ (rawRVSpace (M := M) k).domain :=
          ⟨rvTuple (z ∘ Sum.inr) (fun i => hz2 ▸ hrv _ hz1 i), rfl⟩
        have hd : rvValues ((rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl, hx⟩) = z ∘ Sum.inl :=
          decode_rv _
        have he : rvValues ((rawRVSpace (M := M) k).decode ⟨z ∘ Sum.inr, hy⟩) = z ∘ Sum.inr :=
          decode_rv _
        have hmem : (rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl, hx⟩ ∈ (rawDefSet hc I hI).carrier := by
          apply (mem_rawDefSet hc I hI _).mpr
          rw [hd]
          exact hz1
        refine ⟨hx, hy, ⟨_, hmem⟩, rfl, ?_⟩
        apply rvValues_injective
        refine Eq.trans ?_ he.symm
        change F (rvValues ((rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl, hx⟩)) = z ∘ Sum.inr
        rw [hd]
        exact hz2
    rw [hset]
    exact h

open DiamondIntegral.Section6 in
/-- A raw volume with definable code graph, as a Section 6 Gamma form. -/
def rawForm {S : Set M} {n : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I)
    (μ : (Fin n → M) → Values.Gamma (M := M))
    (hμ : RVVolumeMaps.VolumeDefinable (⟨S, ∅⟩ : GammaParameters.Base (M := M)) I μ) :
    Map (rawDefSet hc I hI) (DefSet.univ (rawGammaPresentation (M := M)) S) where
  toFun a := ⟨μ (rvValues a.val), Set.mem_univ _⟩
  graph_definable := by
    let σ : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cons (Sum.inr 0) Sum.inl
    have h := (base_real hμ).preimage_comp σ
    show S.Definable LRV ((rawRVSpace (M := M) n).relation (rawGammaPresentation (M := M)) _)
    have ht : ∀ z : Fin n ⊕ Fin 1 → M, Fin.tail (z ∘ σ) = z ∘ Sum.inl := fun z => rfl
    have h0 : ∀ z : Fin n ⊕ Fin 1 → M, (z ∘ σ) 0 = z (Sum.inr 0) := fun z => rfl
    have hset : (rawRVSpace (M := M) n).relation (rawGammaPresentation (M := M))
        (fun x y => ∃ a : rawDefSet hc I hI, a.val = x ∧
          (⟨μ (rvValues a.val), Set.mem_univ _⟩ :
            DefSet.univ (rawGammaPresentation (M := M)) S).val = y) =
        (fun g : Fin n ⊕ Fin 1 → M => g ∘ σ) ⁻¹' RVVolumeMaps.volumeGraph I μ := by
      ext z
      constructor
      · rintro ⟨hx, hy, a, ha, hb⟩
        have hzx : z ∘ Sum.inl = rvValues a.val := by
          rw [ha, decode_rv]
        refine ⟨?_, ?_, ?_⟩
        · change Fin.tail (z ∘ σ) ∈ I
          rw [ht, hzx]
          exact a.property
        · exact hy
        · change GammaParameters.codeValue ((z ∘ σ) 0) = μ (Fin.tail (z ∘ σ))
          rw [h0, ht, hzx]
          exact hb.symm
      · rintro ⟨hz1, hz2, hz3⟩
        change Fin.tail (z ∘ σ) ∈ I at hz1
        rw [ht] at hz1
        change GammaParameters.codeValue ((z ∘ σ) 0) = μ (Fin.tail (z ∘ σ)) at hz3
        rw [h0, ht] at hz3
        have hx : z ∘ Sum.inl ∈ (rawRVSpace (M := M) n).domain :=
          ⟨rvTuple (z ∘ Sum.inl) (hI.proper _ hz1), rfl⟩
        have hy : z ∘ Sum.inr ∈ (rawGammaPresentation (M := M)).domain := hz2
        have hd : rvValues ((rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl, hx⟩) = z ∘ Sum.inl :=
          decode_rv _
        have hmem : (rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl, hx⟩ ∈ (rawDefSet hc I hI).carrier := by
          apply (mem_rawDefSet hc I hI _).mpr
          rw [hd]
          exact hz1
        refine ⟨hx, hy, ⟨_, hmem⟩, rfl, ?_⟩
        change μ (rvValues ((rawRVSpace (M := M) n).decode ⟨z ∘ Sum.inl, hx⟩)) =
          GammaParameters.codeValue (z (Sum.inr (0 : Fin 1)))
        rw [hd]
        exact hz3.symm
    rw [hset]
    exact h

variable {S : Set M} {k : ℕ}

/-- The underlying special-transformations RV object of a chart over `⟨S, ∅⟩`. -/
def toObject (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) : SpecialTransformations.Section4.RVObject (M := M) S k where
  arity := a.arity
  domain := rawDefSet hc a.domain a.domain_definable
  volume := rawMap hc a.domain a.domain_definable a.coordinate a.coordinate_definable
    (fun x hx i => (a.coordinate_proper x hx i).1)

theorem toObject_value (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (x : (toObject hc a).domain) : rvValues ((toObject hc a).value x) = a.coordinate (rvValues x.val) :=
  rfl

theorem toObject_finite (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) :
    (toObject hc a).volume.FiniteFibres := by
  intro t
  refine Set.Finite.of_finite_image (f := fun x : (toObject hc a).domain => rvValues x.val) ?_ ?_
  · apply (a.finite_fibres (rvValues t.val)).subset
    rintro u ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    have := congrArg (fun y : (DefSet.univ (rawRVSpace (M := M) k) S) => rvValues y.val) hx
    exact this
  · intro x _ y _ h
    exact Subtype.ext (rvValues_injective h)

open DiamondIntegral.Section6 in
/-- The Section 6 measured RV object of a chart over `⟨S, ∅⟩`. -/
def toMeasured (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) :
    DiamondIntegral.Section6.MeasuredRVObject (M := M) S k where
  object := toObject hc a
  finiteVolume := toObject_finite hc a
  nonzero := fun x i => (a.coordinate_proper _ x.property i).2
  form := rawForm hc a.domain a.domain_definable a.volume a.volume_definable

/-- A raw map with definable graph between two raw definable sets. -/
def rawMapInto {n m : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I)
    (J : Set (Fin m → M))
    (hJ : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin m => .rv) J)
    (F : (Fin n → M) → (Fin m → M))
    (hF : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (m + n) => .rv)
      (graphOn I F))
    (hmaps : ∀ x ∈ I, F x ∈ J) :
    Map (rawDefSet hc I hI) (rawDefSet hc J hJ) where
  toFun a := ⟨rvTuple (F (rvValues a.val)) (hJ.proper _ (hmaps _ a.property)), hmaps _ a.property⟩
  graph_definable := by
    have h := (rawMap hc I hI F hF (fun x hx => hJ.proper _ (hmaps x hx))).graph_definable
    exact h

theorem rawMapInto_val {n m : ℕ} (I : Set (Fin n → M))
    (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin n => .rv) I)
    (J : Set (Fin m → M))
    (hJ : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin m => .rv) J)
    (F : (Fin n → M) → (Fin m → M))
    (hF : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (m + n) => .rv)
      (graphOn I F))
    (hmaps : ∀ x ∈ I, F x ∈ J) (a : rawDefSet hc I hI) :
    rvValues ((rawMapInto hc I hI J hJ F hF hmaps) a).val = F (rvValues a.val) := rfl

/-- The raw function of a chart isomorphism. -/
def isoRaw {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b)
    (x : Fin a.arity → M) : Fin b.arity → M :=
  if hx : x ∈ a.domain then (F.equiv ⟨x, hx⟩).val else fun _ => iRVOne

theorem isoRaw_mem {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b)
    (x : Fin a.arity → M) (hx : x ∈ a.domain) : isoRaw F x = (F.equiv ⟨x, hx⟩).val := by
  simp [isoRaw, hx]

theorem isoRaw_graph {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b) :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (b.arity + a.arity) => .rv)
      (graphOn a.domain (isoRaw F)) := by
  have he : graphOn a.domain (isoRaw F) =
      {w | ∃ u : a.domain, w = join b.arity a.arity u.val (F.equiv u).val} := by
    ext w
    rw [RVRealProducts.graphOn_exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, by rw [isoRaw_mem F x hx]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, by rw [isoRaw_mem F u.val u.property]⟩
  rw [he]
  exact F.graph_definable

/-- The map of chart domains induced by a chart isomorphism. -/
def isoMap {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b) :
    Map (toObject hc a).domain (toObject hc b).domain :=
  rawMapInto hc a.domain a.domain_definable b.domain b.domain_definable (isoRaw F) (isoRaw_graph F)
    (fun x hx => by rw [isoRaw_mem F x hx]; exact (F.equiv ⟨x, hx⟩).property)

omit [M ⊨ Axioms.ACVF] in
theorem rvWeight_nonzero {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) (ht : ∀ i, (t i).val ≠ iRVZero) :
    rvWeight t = n := by
  rw [rvWeight_eq_card]
  have : (Finset.univ.filter (fun i => (t i).val ≠ iRVZero)) = Finset.univ :=
    Finset.filter_true_of_mem (fun i _ => ht i)
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- The `RVHom` induced by a chart isomorphism. -/
def isoHom {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b) :
    RVHom (toObject hc a) (toObject hc b) where
  map := isoMap hc F
  volumetric := by
    intro x
    rw [rvWeight_nonzero _ (fun i => (a.coordinate_proper _ x.property i).2),
      rvWeight_nonzero _ (fun i => (b.coordinate_proper _ ((isoMap hc F) x).property i).2)]
  finite_volume_images := by
    intro t
    by_cases ht : ∃ x : (toObject hc a).domain, (toObject hc a).value x = t
    · obtain ⟨x0, hx0⟩ := ht
      have hfin := (toObject_finite hc a) ((toObject hc a).volume x0)
      apply (hfin.image (fun x => (toObject hc b).value ((isoMap hc F) x))).subset
      rintro s ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      apply Subtype.ext
      change (toObject hc a).value x = (toObject hc a).value x0
      rw [hx, hx0]
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro s ⟨x, hx, _⟩
      exact ht ⟨x, hx⟩

theorem isoMap_val {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b)
    (x : (toObject hc a).domain) :
    rvValues ((isoMap hc F) x).val = (F.equiv ⟨rvValues x.val, x.property⟩).val := by
  change isoRaw F (rvValues x.val) = _
  rw [isoRaw_mem F _ x.property]

/-- A chart isomorphism gives an isomorphism of the underlying RV objects. -/
def isoObject {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b) :
    toObject hc a ≅ toObject hc b where
  hom := isoHom hc F
  inv := isoHom hc (RVMeasuredIsomorphisms.symm F)
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro x
    apply Subtype.ext
    apply rvValues_injective
    change rvValues ((isoMap hc (RVMeasuredIsomorphisms.symm F)) ((isoMap hc F) x)).val = rvValues x.val
    rw [isoMap_val]
    have h1 : (⟨rvValues ((isoMap hc F) x).val, ((isoMap hc F) x).property⟩ : b.domain) =
        F.equiv ⟨rvValues x.val, x.property⟩ := Subtype.ext (isoMap_val hc F x)
    change ((F.equiv.symm) ⟨rvValues ((isoMap hc F) x).val, ((isoMap hc F) x).property⟩).val = _
    rw [h1, Equiv.symm_apply_apply]
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro y
    apply Subtype.ext
    apply rvValues_injective
    change rvValues ((isoMap hc F) ((isoMap hc (RVMeasuredIsomorphisms.symm F)) y)).val = rvValues y.val
    rw [isoMap_val]
    have h1 : (⟨rvValues ((isoMap hc (RVMeasuredIsomorphisms.symm F)) y).val,
        ((isoMap hc (RVMeasuredIsomorphisms.symm F)) y).property⟩ : a.domain) =
        F.equiv.symm ⟨rvValues y.val, y.property⟩ := Subtype.ext (isoMap_val hc _ y)
    rw [h1, Equiv.apply_symm_apply]

theorem codeValue_gammaOf (t : CanonicalRV.RVSort M) (h : t.val ≠ iRVZero) :
    codeValue t.val = Values.gammaOf t h := by
  have hp : NonzeroRV t.val := ⟨t.property, h⟩
  simp only [codeValue, dif_pos hp]
  rfl

/-- The Section 6 total weight is the chart's corrected weight. -/
theorem totalWeight_eq (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (u : (toObject hc a).domain) :
    (toMeasured hc a).totalWeight u = a.correctedWeight (rvValues u.val) := by
  change a.volume (rvValues u.val) * SpecialTransformations.Section9.rvVolumeGamma ((toObject hc a).value u) _ =
    a.volume (rvValues u.val) * ∏ i, codeValue (a.coordinate (rvValues u.val) i)
  congr 1
  unfold SpecialTransformations.Section9.rvVolumeGamma
  apply Finset.prod_congr rfl
  intro i _
  exact (codeValue_gammaOf _ _).symm

/-- A chart isomorphism gives a measured RV isomorphism of the Section 6 objects. -/
def measuredIso {a b : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k} (F : Iso a b) :
    DiamondIntegral.Section6.MeasuredRVIso (toMeasured hc a) (toMeasured hc b) where
  iso := isoObject hc F
  balance := by
    intro u
    rw [totalWeight_eq, totalWeight_eq]
    change a.correctedWeight (rvValues u.val) = b.correctedWeight (rvValues ((isoMap hc F) u).val)
    rw [isoMap_val]
    exact F.weight_eq ⟨rvValues u.val, u.property⟩

end DiamondIntegral.Section7.MeasuredRVBridge
