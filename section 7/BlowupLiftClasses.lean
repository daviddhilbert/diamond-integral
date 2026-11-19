import «section 7».BlowupLiftContraction
import «section 7».Remark74

/-! The tag split of the contraction (Lemma 7.12, `blowup:same:RV:coa`).

The label domain of the contraction `W` is the union of the endpoint labels
(tag `rv(-1)`) and the shell labels (tag `rv(1)`). The two pieces are
isomorphic in `μRV^db[1+k]` to the endpoint and shell charts of
Definition 7.2: the raw maps `Fe`, `Fs` of `BlowupLiftImage` are bijections
of label domains that preserve the leading terms and the forms. -/

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
open SpecialTransformations.Section9 (liftLabelMap)

namespace DiamondIntegral.Section7.BlowupLiftClasses
open DiamondIntegral.Section4
open DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open AnnularBlowup BlowupChart RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.BlowupLiftImage
open DiamondIntegral.Section7.BlowupLiftContraction
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondLiftHomomorphism

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- Measured objects with equal values have equal volume factors. -/
theorem volumeGamma_eq {n : ℕ} {U V : MeasuredRVObject (M := M) S n} {u : U.object.domain} {v : V.object.domain}
    (h : U.object.value u = V.object.value v) : U.volumeGamma u = V.volumeGamma v := by
  unfold MeasuredRVObject.volumeGamma
  generalize U.nonzero u = hu
  generalize V.nonzero v = hv
  revert hu hv
  rw [h]
  intro hu hv
  rfl

section Split
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : TupleFinitaryLift (centreRelation D))
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hU : (toMeasured hc D.chart).doublyBounded)
variable (hP : ProperInvariant S (liftSet hc D).carrier)
variable (Δ : Values.Gamma (M := M))
variable (hΔ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}})
variable (hΔ1 : 1 ≤ Δ) (hΔb : ∀ u ∈ D.chart.domain, codeValue (D.aperture.aperture u) ≤ Δ)
variable (h00 : M ⊨ Axioms.ACVF00)

local notation "𝓥" => Vreg (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb
local notation "𝓦" => W (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb h00
local notation "𝓕" => Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb

theorem mem_W_domain (t : Fin (labN D) → RVInfinity M) :
    t ∈ (𝓦).object.domain.carrier ↔ rvValues t ∈ Icore D ∪ Ishell D := by
  constructor
  · intro ht
    obtain ⟨p, hp⟩ := pureRVTagQuotient_surjective (𝓥) (⟨t, ht⟩ : pureRVTagDomain (𝓥))
    have h := (mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb p.val).mp p.property
    have he : p.val.2 = t := congrArg Subtype.val hp
    rw [← he]
    exact h.1
  · intro ht
    obtain ⟨y, hy⟩ := SpecialTransformations.Section4.tupleRV_surjective
      (fun i => t (Fin.castAdd (1 + D.chart.arity) i))
    have hmem : (y, t) ∈ (𝓥).carrier := by
      refine (mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb (y, t)).mpr ⟨ht, ?_⟩
      change rvValues (SpecialTransformations.Section4.tupleRV y) = _
      rw [hy]
      rfl
    exact (pureRVTagQuotient (𝓥) ⟨(y, t), hmem⟩).property

/-- The value of the contraction at a label: its leading terms. -/
theorem W_value (u : (𝓦).object.domain) : rvValues ((𝓦).object.value u) = hd D (rvValues u.val) := by
  obtain ⟨q, rfl⟩ := pureRVTagQuotient_surjective (𝓥) u
  have h := preparedRVObject_value (𝓥) (vreg_tagged hc D L hv hU hP Δ hΔ hΔ1 hΔb) q
  change rvValues ((preparedRVObject (𝓥) (vreg_tagged hc D L hv hU hP Δ hΔ hΔ1 hΔb)).value
    (pureRVTagQuotient (𝓥) q)) = _
  rw [h]
  exact ((mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb q.val).mp q.property).2

/-- The form of the contraction at a label: the source volume at its original label. -/
theorem W_form (u : (𝓦).object.domain) :
    gammaMapValue (𝓦).form u = D.chart.volume (lb D (rvValues u.val)) := by
  obtain ⟨q, rfl⟩ := pureRVTagQuotient_surjective (𝓥) u
  rw [show gammaMapValue (𝓦).form (pureRVTagQuotient (𝓥) q) =
      gammaMapValue (form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00) q from contractedMeasuredRVObject_form _ _ _ _ _ _ _ _]
  have hF := Fmap_bijective hc D L hv hU hP Δ hΔ hΔ1 hΔb h00
  have hq := Map.apply_inverse (𝓕) hF q
  have hl : rvValues ((𝓕).inverse hF q).val.2 = lb D (rvValues q.val.2) := by
    funext i
    change (((𝓕).inverse hF q).val.2 i).val = (q.val.2 (Fin.natAdd (1 + k) (Fin.natAdd 1 i))).val
    rw [← Fmap_labels hc D L hv hU hP Δ hΔ hΔ1 hΔb _ i, hq]
  change D.chart.volume (rvValues ((𝓕).inverse hF q).val.2) = _
  rw [hl]
  rfl

/-- The endpoint labels, as a definable set of RV labels. -/
abbrev Dcore : DefSet (rawRVSpace (M := M) (labN D)) S := rawDefSet hc (Icore D) (Icore_definable D)

theorem Dcore_sub : (Dcore hc D).carrier ⊆ (𝓦).object.domain.carrier :=
  fun t ht => (mem_W_domain hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 t).mpr (Or.inl ht)

/-- The endpoint piece of the contraction. -/
abbrev Wcore : MeasuredRVObject (M := M) S (1 + k) :=
  (𝓦).restrict (Dcore hc D) (Dcore_sub hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)

/-- The shell piece of the contraction. -/
abbrev Wshell : MeasuredRVObject (M := M) S (1 + k) := restrictCompl (𝓦) (Dcore hc D)

/-! ### The endpoint isomorphism -/

/-- The endpoint chart. -/
abbrev cE : Chart (⟨S, ∅⟩ : Base (M := M)) (1 + k) := endpointChart D.chart D.coordinate D.finite D.aperture

/-- The shell chart. -/
abbrev cS : Chart (⟨S, ∅⟩ : Base (M := M)) (1 + k) := shellChart D.chart D.coordinate D.finite D.aperture

/-- The endpoint label map. -/
def mapE : Map (toMeasured hc (cE D)).object.domain (Dcore hc D) :=
  rawMapInto hc (cE D).domain (cE D).domain_definable (Icore D) (Icore_definable D) (Fe D) (Fe_tupleDef D)
    (fun w hw => ⟨w, hw, rfl⟩)

theorem mapE_val (a : (toMeasured hc (cE D)).object.domain) :
    rvValues (mapE hc D a).val = Fe D (rvValues a.val) := rfl

theorem mapE_bijective : Function.Bijective (mapE hc D) := by
  constructor
  · intro a b he
    have hFe : Fe D (rvValues a.val) = Fe D (rvValues b.val) := by
      rw [← mapE_val, ← mapE_val, he]
    have hl := congrArg (lb D) hFe
    simp only [Fe, lb_mk] at hl
    have ha : rvValues a.val ∈ (graphChart D.chart D.aperture).domain := a.property
    have hb : rvValues b.val ∈ (graphChart D.chart D.aperture).domain := b.property
    apply Subtype.ext
    apply rvValues_injective
    rw [graph_canonical _ _ ha, graph_canonical _ _ hb, hl]
  · intro b
    obtain ⟨v, hv, hFe⟩ := (b.property : rvValues b.val ∈ Icore D)
    have hs := (cE D).domain_definable.proper v hv
    refine ⟨⟨rvTuple v hs, ?_⟩, ?_⟩
    · show rvValues (rvTuple v hs) ∈ (cE D).domain
      rw [rvValues_rvTuple]
      exact hv
    · apply Subtype.ext
      apply rvValues_injective
      rw [mapE_val, rvValues_rvTuple, hFe]

/-- The endpoint chart is isomorphic in `μRV^db[1+k]` to the endpoint piece. -/
def isoE : MeasuredRVIso (toMeasured hc (cE D)) (Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00) where
  iso := rvIsoOfFiniteFibres (mapE hc D) (mapE_bijective hc D) (toMeasured hc (cE D)).finiteVolume
    (Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).finiteVolume (toMeasured hc (cE D)).nonzero
    (Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).nonzero
  balance a := by
    rw [rvIsoOfFiniteFibres_map]
    unfold MeasuredRVObject.totalWeight
    have hW : (Dcore hc D).carrier ⊆ (𝓦).object.domain.carrier := Dcore_sub hc D L hv hU hP Δ hΔ hΔ1 hΔb h00
    let b : (𝓦).object.domain := ⟨(mapE hc D a).val, hW (mapE hc D a).property⟩
    have hform : gammaMapValue (Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).form (mapE hc D a) =
        gammaMapValue (𝓦).form b := rfl
    have hval : (Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object.value (mapE hc D a) = (𝓦).object.value b := rfl
    have he : (toMeasured hc (cE D)).object.value a = (Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object.value (mapE hc D a) := by
      apply rvValues_injective
      rw [hval, W_value hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 b]
      change (cE D).coordinate (rvValues a.val) = hd D (rvValues (mapE hc D a).val)
      rw [mapE_val, Fe, hd_mk]
      rfl
    rw [volumeGamma_eq he, hform, W_form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 b]
    change (cE D).volume (rvValues a.val) * _ = D.chart.volume (lb D (rvValues (mapE hc D a).val)) * _
    rw [mapE_val, Fe, lb_mk]
    rfl

/-! ### The shell isomorphism -/

theorem Ishell_sub : (rawDefSet hc (Ishell D) (Ishell_definable D)).carrier ⊆
    ((𝓦).object.domain.sdiff (Dcore hc D)).carrier := fun t ht =>
  ⟨(mem_W_domain hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 t).mpr (Or.inr ht),
    fun hc' => Icore_Ishell_disjoint D h00 hc' ht⟩

/-- The shell label map. -/
def mapS : Map (toMeasured hc (cS D)).object.domain (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object.domain :=
  (Map.inclusion (Ishell_sub hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)).comp
    (rawMapInto hc (cS D).domain (cS D).domain_definable (Ishell D) (Ishell_definable D) (Fs D) (Fs_tupleDef D)
      (fun w hw => ⟨w, hw, rfl⟩))

theorem mapS_val (a : (toMeasured hc (cS D)).object.domain) :
    rvValues (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a).val = Fs D (rvValues a.val) := rfl

theorem mapS_bijective : Function.Bijective (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00) := by
  constructor
  · intro a b he
    have hFs : Fs D (rvValues a.val) = Fs D (rvValues b.val) := by
      rw [← mapS_val, ← mapS_val, he]
    obtain ⟨hh, _, hl⟩ := mk_injective D hFs
    have ha : rvValues a.val ∈ shellDomain D.chart D.aperture := a.property
    have hb : rvValues b.val ∈ shellDomain D.chart D.aperture := b.property
    have hsa : rvValues a.val (sIdx D.chart) = rvValues b.val (sIdx D.chart) := by
      have h1 := congrFun hh D.coordinate
      rw [blownCoordinate_at, blownCoordinate_at, hl] at h1
      have hf : NonzeroRV (D.chart.coordinate (rvValues b.val ∘ xIdx D.chart) D.coordinate) := by
        have hd := (shell_points D.chart D.aperture hb).1
        exact ⟨(D.chart.coordinate_proper _ hd _).1, (D.chart.coordinate_proper _ hd _).2⟩
      exact AnnularBlowup.rvMul_right_cancel ((shell_points D.chart D.aperture ha).2.1).1
        ((shell_points D.chart D.aperture hb).2.1).1 hf h1
    apply Subtype.ext
    apply rvValues_injective
    rw [shell_canonical _ _ ha, shell_canonical _ _ hb, hl, hsa]
  · intro b
    have hb := b.property
    have hbI : rvValues b.val ∈ Ishell D := by
      rcases (mem_W_domain hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 b.val).mp hb.1 with h | h
      · exact absurd h hb.2
      · exact h
    obtain ⟨v, hv', hFs⟩ := hbI
    have hs := (cS D).domain_definable.proper v hv'
    refine ⟨⟨rvTuple v hs, ?_⟩, ?_⟩
    · show rvValues (rvTuple v hs) ∈ (cS D).domain
      rw [rvValues_rvTuple]
      exact hv'
    · apply Subtype.ext
      apply rvValues_injective
      rw [mapS_val, rvValues_rvTuple, hFs]

/-- The shell chart is isomorphic in `μRV^db[1+k]` to the shell piece. -/
def isoS : MeasuredRVIso (toMeasured hc (cS D)) (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00) where
  iso := rvIsoOfFiniteFibres (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)
    (mapS_bijective hc D L hv hU hP Δ hΔ hΔ1 hΔb h00) (toMeasured hc (cS D)).finiteVolume
    (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).finiteVolume (toMeasured hc (cS D)).nonzero
    (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).nonzero
  balance a := by
    rw [rvIsoOfFiniteFibres_map]
    unfold MeasuredRVObject.totalWeight
    let b : (𝓦).object.domain := ⟨(mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a).val,
      (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a).property.1⟩
    have hform : gammaMapValue (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).form
        (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a) = gammaMapValue (𝓦).form b := rfl
    have hval : (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object.value (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a) =
        (𝓦).object.value b := rfl
    have he : (toMeasured hc (cS D)).object.value a =
        (Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object.value (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a) := by
      apply rvValues_injective
      rw [hval, W_value hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 b]
      change (cS D).coordinate (rvValues a.val) = hd D (rvValues (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a).val)
      rw [mapS_val, Fs, hd_mk]
      rfl
    rw [volumeGamma_eq he, hform, W_form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 b]
    change (cS D).volume (rvValues a.val) * _ =
      D.chart.volume (lb D (rvValues (mapS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 a).val)) * _
    rw [mapS_val, Fs, lb_mk]
    rfl

end Split

/-! ### Lemma 7.12 for `∞`-free data -/

section NoInfinity
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

theorem endpoint_noInfinity (hn : MeasuredRVBounds.NoInfinity D.chart) :
    MeasuredRVBounds.NoInfinity (endpointChart D.chart D.coordinate D.finite D.aperture) := by
  intro w hw i
  rcases block_cases 1 D.chart.arity i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · exact hn _ hw.1 i'
  · rw [Subsingleton.elim i' 0]
    exact graph_aperture_nonzero D.chart D.aperture w hw

theorem shell_noInfinity (hn : MeasuredRVBounds.NoInfinity D.chart) :
    MeasuredRVBounds.NoInfinity (shellChart D.chart D.coordinate D.finite D.aperture) := by
  intro w hw i
  obtain ⟨hg, hp, _, _⟩ := shell_mem D.chart D.aperture hw
  rcases block_cases 1 (1 + D.chart.arity) i with ⟨i', rfl⟩ | ⟨i', rfl⟩
  · exact endpoint_noInfinity D hn _ hg i'
  · exact ⟨(hp i').1, (hp i').2⟩

end NoInfinity

section Final
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section6.DiamondGrothendieck
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (B₀ : VFGeneratedFieldBase T) (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- Lemma 7.12 in `K₊ μVF^◇` for an `∞`-free datum: the lift of the source
equals the lift of the shell plus the lift of the endpoint. -/
theorem lift_blowup (D : AnnularDatum (BT T) k) (hn : MeasuredRVBounds.NoInfinity D.chart) :
    liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt
        (DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ D.chart D.bounded hn)) =
      liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt
          (DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ (cS D)
            (shell_domain_bounded _ _ _ _ D.bounded) (shell_noInfinity D hn))) +
        liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt
          (DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ (cE D)
            (endpoint_domain_bounded _ _ _ _ D.bounded) (endpoint_noInfinity D hn))) := by
  obtain ⟨L⟩ := lemma_6_30_tuple_vfGenerated (G := G) hc h00 hκ.le hs hv T B₀ hnt hsmall hΓ (centreRelation D)
  obtain ⟨Δ, hΔ, hΔ1, hΔb⟩ := Remark74.remark_7_4_named hc h00 D.chart D.aperture
  have hU := (dbOf hc h00 hκ hs T hsmall hΓ D.chart D.bounded hn).2
  have hP := measuredRVLift_properInvariant h00 hc hκ hs hv _ hU
  have hiso := lift_isomorphic hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 hκ hs hsmall hΓ
  have hWdb := W_doublyBounded hc D L hv hU hP Δ hΔ hΔ1 hΔb h00
  have hsc := DiamondIntegral.Section3.positiveClass_scissor (rvPresentation (T : Set M) (1 + k))
    (a := ⟨Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00,
      (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).restrict_doublyBounded _ _ hWdb⟩)
    (b := ⟨Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00,
      (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).restrict_doublyBounded _ _ hWdb⟩)
    (c := ⟨W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00, hWdb⟩) (d := ⟨emptyRV (T : Set M) (1 + k), emptyRV_doublyBounded⟩)
    ⟨W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00, hWdb, Dcore hc D, Dcore_sub hc D L hv hU hP Δ hΔ hΔ1 hΔb h00,
      rfl, rfl, rfl, rfl⟩
  have he0 : DiamondIntegral.Section3.positiveClass (rvPresentation (T : Set M) (1 + k))
      ⟨emptyRV (T : Set M) (1 + k), emptyRV_doublyBounded⟩ = 0 :=
    DiamondIntegral.Section3.positiveClass_empty (rvPresentation (T : Set M) (1 + k))
  rw [he0, add_zero] at hsc
  have hE := DiamondIntegral.Section3.positiveClass_iso (rvPresentation (T : Set M) (1 + k))
    (a := dbOf hc h00 hκ hs T hsmall hΓ (cE D) (endpoint_domain_bounded _ _ _ _ D.bounded) (endpoint_noInfinity D hn))
    (b := ⟨Wcore hc D L hv hU hP Δ hΔ hΔ1 hΔb h00,
      (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).restrict_doublyBounded _ _ hWdb⟩)
    ⟨isoE hc D L hv hU hP Δ hΔ hΔ1 hΔb h00⟩
  have hS := DiamondIntegral.Section3.positiveClass_iso (rvPresentation (T : Set M) (1 + k))
    (a := dbOf hc h00 hκ hs T hsmall hΓ (cS D) (shell_domain_bounded _ _ _ _ D.bounded) (shell_noInfinity D hn))
    (b := ⟨Wshell hc D L hv hU hP Δ hΔ hΔ1 hΔb h00,
      (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).restrict_doublyBounded _ _ hWdb⟩)
    ⟨isoS hc D L hv hU hP Δ hΔ hΔ1 hΔb h00⟩
  have h1 : liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt
        (DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ D.chart D.bounded hn)) =
      vfClass G hc (liftObject (toMeasured hc D.chart) hP) :=
    liftHom_class (G := G) (k := 1 + k) h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt _
  have h2 : liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt
        (DiamondIntegral.Section3.positiveClass _ ⟨W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00, hWdb⟩) =
      vfClass G hc (liftObject (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)
        (measuredRVLift_properInvariant h00 hc hκ hs hv _ hWdb)) :=
    liftHom_class (G := G) (k := 1 + k) h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt _
  rw [h1, vfClass_iso hc hiso, ← h2, ← hsc, map_add, hE, hS]
  exact add_comm _ _

/-- Lemma 7.12 on Section 7's classes, for an `∞`-free datum:
`μ𝕃[U^{τ,j}] = μ𝕃[U]`. -/
theorem lemma_7_12_noInfinity (D : AnnularDatum (BT T) k) (hn : MeasuredRVBounds.NoInfinity D.chart) :
    liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls D.annularObject) =
      liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls D.source) := by
  have key : ∀ (a : Obj (BT T) (1 + k)) (ha : MeasuredRVBounds.NoInfinity a.toChart),
      liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls a) =
        liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt
          (DiamondIntegral.Section3.positiveClass _ (dbOf hc h00 hκ hs T hsmall hΓ a.toChart a.domain_bounded ha)) := by
    intro a ha
    change liftHom (1 + k) G h00 hc lin hκ hs hv T B₀ hsmall hΓ hnt (rvCls hc h00 hκ hs T hsmall hΓ (cls a)) = _
    rw [rvCls_cls]
    congr 1
    exact positiveClass_dbOf_eq hc h00 hκ hs T hsmall hΓ _ _ _ _
      ⟨RVMeasuredIsomorphisms.symm (strictIso h00 a.toChart)⟩
  rw [ElementaryBlowups.cls_annular, map_add,
    key _ (shell_noInfinity D hn), key _ (endpoint_noInfinity D hn), key D.source hn]
  exact (lift_blowup hc h00 hκ hs T hsmall hΓ hv B₀ hnt D hn).symm

end Final

end DiamondIntegral.Section7.BlowupLiftClasses
