import «section 7».OrderIndependence
import «section 7».PieceCombination
import «section 7».LabelPieces
import «section 7».KernelBaseChange
import «section 7».ProvedResults

/-! Additivity of contraction classes under the scissor relation of
`K₊ μVF^◇[n]` (for Proposition 7.24).

Let `U` be an object of `μVF^◇[n + 1]`, `X ⊆ U` a definable proper invariant
subset, and `F`, `F₁`, `F₂` standard contractions, in any orders, of `U`, of the
restriction `U|X` and of the complement `U ∖ X` (`DiamondGrothendieck.Scissor`).
Then `[F(U)]` and `[F₁(U|X)] + [F₂(U ∖ X)]` are `μIsp^db`-related
(`scissor_classes`; `scissor_classes_of_scissor` for the scissor relation). So
the class of a contraction is additive along the scissor relation, up to
`μIsp^db`.

`X` need not be label-saturated in `U`, so a contraction of `U` does not
restrict to `X` directly. The proof grafts the indicator of `X` as a new label.

* `tagMap X A`: the map `A → RV`, `p ↦ rv(-1)` on `X` and `rv(1)` off `X`. It is
  proper covariant when `A` and `X` are proper invariant
  (`tagMap_properCovariant`): its graph fibres are the fibres of `X` and `A ∖ X`.
* `U' = graft(U)`: the graft of the tag (`GraftObjects.graftObject`), with the
  graft morphism `U → U'`.
* `graftPiece Y`: the image of a proper invariant piece `Y ⊆ U` under the graft.
  It is proper invariant, and the graft restricted to `Y` is a morphism
  `U|Y → U'|graft(Y)` (`graftPiece_morphism`): the restriction of a relatively
  unary proper covariant homeomorphism, with the restricted unit charts.
  The images of `X` and `U ∖ X` are label-saturated in `U'` (the new label
  records membership in `X`), disjoint, and cover `U'`.
* The graft maps fix every VF coordinate. A morphism fixing the VF coordinates
  relates the classes of any two contractions of its source and target
  (`ispRel_of_vfFixing`): by Corollary 7.15 in the same order and `(∗)` to change
  the order (`OrderIndependence.star`) when `n + 1 ≥ 2`, and by Lemma 7.13 when
  `n + 1 = 1`.
* A contraction of `U'` splits along the two label-saturated pieces
  (`RestrictContractions.cls_headStart_zero_split`), and `μIsp^db` is a
  congruence (`PieceCombination.ispRel_add`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ScissorClasses
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.RestrictContractions DiamondIntegral.Section7.GraftObjects
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.KernelBaseChange

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### The tag of a piece -/

section Tag
variable {S : Set M} {n r : ℕ}

/-- The tag of a point: `rv(-1)` on `X` and `rv(1)` off `X`. -/
def tagValue (X : Set (Mixed M n r)) (p : Mixed M n r) : RVInfinity M :=
  if p ∈ X then branchTag true else branchTag false

/-- The tag as a point of `RV^1`. -/
def tagPoint (X : Set (Mixed M n r)) (p : Mixed M n r) : Mixed M 0 1 :=
  (Fin.elim0, fun _ => tagValue X p)

/-- **The tag map** `A → RV^1` of a definable set `X`. -/
def tagMap (X A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) 0 1) S) := by
  let P := rawMixedSpace (M := M) n r
  let codes (z : Fin n ⊕ Fin r → M) : Fin 0 ⊕ Fin 1 → M :=
    Sum.elim Fin.elim0 (fun _ => if z ∈ P.preimage X.carrier then (branchTag (M := M) true).val
      else (branchTag (M := M) false).val)
  have hd : S.DefinableMap LRV codes := by
    rintro (i | i)
    · exact i.elim0
    · exact Set.DefinableFun.ite X.definable (branchTag_definable S true) (branchTag_definable S false)
  have hcode (c : P.domain) : codes c.val = mixedValues (tagPoint X.carrier (P.decode c)) := by
    have hcond : c.val ∈ P.preimage X.carrier ↔ P.decode c ∈ X.carrier :=
      ⟨fun h => h.2, fun h => ⟨c.property, h⟩⟩
    funext i
    rcases i with i | i
    · exact i.elim0
    · by_cases hc : P.decode c ∈ X.carrier
      · have hc' := hcond.mpr hc
        simp only [codes, Sum.elim_inr, mixedValues, tagPoint, tagValue, rvValues, hc, hc', ite_true]
      · have hc' : c.val ∉ P.preimage X.carrier := fun h => hc (hcond.mp h)
        simp only [codes, Sum.elim_inr, mixedValues, tagPoint, tagValue, rvValues, hc, hc', ite_false]
  have hdom (c : P.domain) : codes c.val ∈ (rawMixedSpace (M := M) 0 1).domain := by
    rw [hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A (tagPoint X.carrier) codes hd hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨codes c.val, hdom c⟩).trans (hcode c)

theorem tagMap_apply (X A : DefSet (rawMixedSpace (M := M) n r) S) (p : A) :
    (tagMap X A p).val = tagPoint X.carrier p.val := rfl

theorem tagValue_value (X : Set (Mixed M n r)) (p : Mixed M n r) : Values.vrv (tagValue X p) = 1 := by
  unfold tagValue
  split_ifs
  · exact branchTag_value true
  · exact branchTag_value false

/-- The tag separates `X` from its complement. -/
theorem tagValue_eq_iff (h00 : M ⊨ Axioms.ACVF00) (X : Set (Mixed M n r)) (p q : Mixed M n r) :
    tagValue X p = tagValue X q ↔ (p ∈ X ↔ q ∈ X) := by
  have hne : branchTag (M := M) true ≠ branchTag false := fun h => by cases branchTag_injective h00 h
  unfold tagValue
  by_cases hp : p ∈ X <;> by_cases hq : q ∈ X <;> simp [hp, hq, hne, hne.symm]

/-- The source graph fibres of the tag map. -/
theorem mem_tagSource (X A : DefSet (rawMixedSpace (M := M) n r) S) (u : Fin r → RVInfinity M)
    (v : Fin 1 → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (tagMap X A) u v ↔ (a, u) ∈ A.carrier ∧ v = fun _ => tagValue X.carrier (a, u) := by
  constructor
  · rintro ⟨b, ⟨pv, hpA⟩, hp, hfp⟩
    change pv = (a, u) at hp
    subst hp
    exact ⟨hpA, (congrArg Prod.snd hfp).symm⟩
  · rintro ⟨h, hv⟩
    exact ⟨Fin.elim0, ⟨(a, u), h⟩, rfl, Prod.ext (funext fun i => i.elim0) hv.symm⟩

/-- **The tag map is proper covariant.** -/
theorem tagMap_properCovariant {X A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ProperInvariant S A.carrier) (hX : ProperInvariant S X.carrier) : ProperCovariant (tagMap X A) := by
  refine ⟨hA.vfBounded, ⟨1, fun _ _ i => i.elim0⟩, hA.rvBounded, ⟨1, ?_⟩, fun u v => ?_⟩
  · rintro _ ⟨p, rfl⟩ i
    change ((1 : Gamma M)⁻¹).val ≤ Values.vrv (tagValue X.carrier p.val) ∧
      Values.vrv (tagValue X.carrier p.val) ≤ (1 : Gamma M).val
    rw [tagValue_value, inv_one]
    exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨α₁, hα₁, hinv₁⟩ := hX.radii u
    obtain ⟨α₂, hα₂, hinv₂⟩ := hA.radii u
    refine ⟨fun i => max (α₁ i) (α₂ i), fun i => i.elim0, fun i => ((hα₁.max hα₂) i).mono Set.subset_union_left,
      fun i => i.elim0, ?_, ?_, ?_⟩
    · intro a b hab
      have e₁ : (a, u) ∈ X.carrier ↔ (b, u) ∈ X.carrier :=
        hinv₁ a b (Congruent.of_larger_radius (fun i => le_max_left (α₁ i) (α₂ i)) hab)
      have e₂ : (a, u) ∈ A.carrier ↔ (b, u) ∈ A.carrier :=
        hinv₂ a b (Congruent.of_larger_radius (fun i => le_max_right (α₁ i) (α₂ i)) hab)
      have e₃ : tagValue X.carrier (a, u) = tagValue X.carrier (b, u) := by
        unfold tagValue
        by_cases h : (a, u) ∈ X.carrier
        · simp only [h, e₁.mp h, ite_true]
        · have h' : (b, u) ∉ X.carrier := fun h' => h (e₁.mpr h')
          simp only [h, h', ite_false]
      rw [mem_tagSource, mem_tagSource, e₃, e₂]
    · intro a b _
      rw [Subsingleton.elim a b]
    · intro a _ b _ _ i
      exact i.elim0

end Tag

/-! ### Restricted charts -/

section Charts
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hv in
/-- A chart of a map at a point of a proper invariant subset is a chart of the
restriction. -/
theorem chart_restrict {S : Set M} {n r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) {Y : DefSet (rawMixedSpace (M := M) n r) S}
    (hY : Y.carrier ⊆ A.carrier) (hPY : ProperInvariant S Y.carrier) (p : Y)
    {F : (Fin n → VF M) → Fin n → VF M} (hF : IsVFChartAt f ⟨p.val, hY p.property⟩ F) :
    IsVFChartAt (f.restrict hY).toImage p F := by
  obtain ⟨ρ, hρ⟩ := hF
  have hmem : p.val.1 ∈ vfFibre Y.carrier p.val.2 := p.property
  obtain ⟨δ, hδ⟩ := exists_vfBall_subset_nhds hv p.val.1 ((hPY.clopen_fibres hv p.val.2).isOpen.mem_nhds hmem)
  refine ⟨max ρ δ, fun x hx => ?_⟩
  have hxY : (x, p.val.2) ∈ Y.carrier := hδ (vfBall_anti (le_max_right _ _) hx)
  obtain ⟨_, he⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
  exact ⟨hxY, he⟩

end Charts

/-! ### Grafted pieces -/

section Graft
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {n q : ℕ} (A : VFObject (M := M) S n) {D : DefSet (rawMixedSpace (M := M) 0 q) S}
variable (τ : Map A.carrier D) (hτ : ProperCovariant τ)

/-- The image of a piece `Y ⊆ A` under the graft. -/
def graftPiece (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier) :
    DefSet (rawMixedSpace (M := M) n (A.labels + q)) S :=
  ((graft hc τ).restrict hY).image

theorem mem_graftPiece (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier)
    (p : A.carrier) (hp : p.val ∈ Y.carrier) : (graft hc τ p).val ∈ (graftPiece hc A τ Y hY).carrier :=
  ⟨⟨p.val, hp⟩, rfl⟩

theorem graftPiece_subset (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier) :
    (graftPiece hc A τ Y hY).carrier ⊆ (graftObject h00 hc hκ hs hv A τ hτ).carrier.carrier := by
  rintro _ ⟨p, rfl⟩
  exact (((graft hc τ).restrict hY) p).property

/-- A point of the graft image of a piece comes from a point of the piece. -/
theorem graftPiece_point (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier)
    (p : A.carrier) (hp : (graft hc τ p).val ∈ (graftPiece hc A τ Y hY).carrier) : p.val ∈ Y.carrier := by
  obtain ⟨y, hy⟩ := hp
  have he : graft hc τ ⟨y.val, hY y.property⟩ = graft hc τ p := Subtype.ext hy
  have hyp : (⟨y.val, hY y.property⟩ : A.carrier) = p := (graft_bijective hc τ).injective he
  rw [← hyp]
  exact y.property

include hτ in
/-- The graft images of two pieces are label-saturated in the graft when the
graft labels decide membership. -/
theorem graftPiece_saturated (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier)
    (hdec : ∀ p p' : A.carrier, (τ p).val = (τ p').val → p.val ∈ Y.carrier → p'.val ∈ Y.carrier) :
    LabelSaturated (graftPiece hc A τ Y hY) (graftObject h00 hc hκ hs hv A τ hτ).carrier := by
  refine ⟨graftPiece_subset h00 hc hκ hs hv A τ hτ Y hY, ?_⟩
  rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ hl hpY
  have hpY' : p.val ∈ Y.carrier := graftPiece_point hc A τ Y hY p hpY
  have hl' : Fin.append p.val.2 (τ p).val.2 = Fin.append p'.val.2 (τ p').val.2 := hl
  have hnew : (τ p).val = (τ p').val := by
    refine Prod.ext (funext fun i => i.elim0) (funext fun i => ?_)
    have := congrFun hl' (Fin.natAdd A.labels i)
    simpa only [Fin.append_right] using this
  exact mem_graftPiece hc A τ Y hY p' (hdec p p' hnew hpY')

theorem graftPiece_disjoint (Y Y' : DefSet (rawMixedSpace (M := M) n A.labels) S)
    (hY : Y.carrier ⊆ A.carrier.carrier) (hY' : Y'.carrier ⊆ A.carrier.carrier) (hd : Disjoint Y.carrier Y'.carrier) :
    Disjoint (graftPiece hc A τ Y hY).carrier (graftPiece hc A τ Y' hY').carrier := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨y, rfl⟩ hy'
  have h := graftPiece_point hc A τ Y' hY' ⟨y.val, hY y.property⟩ hy'
  exact Set.disjoint_left.mp hd y.property h

theorem graftPiece_cover (Y Y' : DefSet (rawMixedSpace (M := M) n A.labels) S)
    (hY : Y.carrier ⊆ A.carrier.carrier) (hY' : Y'.carrier ⊆ A.carrier.carrier)
    (hcov : A.carrier.carrier ⊆ Y.carrier ∪ Y'.carrier) :
    (graftObject h00 hc hκ hs hv A τ hτ).carrier.carrier ⊆
      (graftPiece hc A τ Y hY).carrier ∪ (graftPiece hc A τ Y' hY').carrier := by
  rintro _ ⟨p, rfl⟩
  rcases hcov p.property with h | h
  · exact Or.inl (mem_graftPiece hc A τ Y hY p h)
  · exact Or.inr (mem_graftPiece hc A τ Y' hY' p h)

include h00 hκ hs hv hsmall hΓ hτ in
/-- The graft restricted to a proper invariant piece is a proper covariant
homeomorphism onto its image. -/
theorem graftPiece_home (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier)
    (hPY : ProperInvariant S Y.carrier) : ProperCovariantHomeomorphism (G := G) ((graft hc τ).restrict hY).toImage :=
  (graft_properHomeomorphism (G := G) h00 hc lin hκ hs hv hsmall hΓ τ A.proper hτ).restrict h00 hc lin hκ hs hv
    hsmall hΓ Y hY hPY

include h00 hκ hs hv hsmall hΓ hτ in
/-- The graft image of a proper invariant piece is proper invariant. -/
theorem graftPiece_proper (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier)
    (hPY : ProperInvariant S Y.carrier) : ProperInvariant S (graftPiece hc A τ Y hY).carrier :=
  (graftPiece_home (G := G) h00 hc hκ hs hv hsmall hΓ A τ hτ Y hY hPY).covariant.target_properInvariant h00 hc lin
    hκ hs hv hsmall hΓ (graftPiece_home (G := G) h00 hc hκ hs hv hsmall hΓ A τ hτ Y hY hPY).bijective.surjective

include hsmall hΓ in
/-- **The graft restricted to a piece is a morphism of `μVF^◇[n]`** from the
restriction of `A` to the restriction of the graft. -/
theorem graftPiece_morphism (Y : DefSet (rawMixedSpace (M := M) n A.labels) S) (hY : Y.carrier ⊆ A.carrier.carrier)
    (hPY : ProperInvariant S Y.carrier) :
    ∃ K : Morphism G (restrictObject A Y hY hPY)
      (restrictObject (graftObject h00 hc hκ hs hv A τ hτ) (graftPiece hc A τ Y hY)
        (graftPiece_subset h00 hc hκ hs hv A τ hτ Y hY)
        (graftPiece_proper (G := G) h00 hc hκ hs hv hsmall hΓ A τ hτ Y hY hPY)),
      K.map = ((graft hc τ).restrict hY).toImage := by
  let f : Map (restrictObject A Y hY hPY).carrier
      (restrictObject (graftObject h00 hc hκ hs hv A τ hτ) (graftPiece hc A τ Y hY)
        (graftPiece_subset h00 hc hκ hs hv A τ hτ Y hY)
        (graftPiece_proper (G := G) h00 hc hκ hs hv hsmall hΓ A τ hτ Y hY hPY)).carrier :=
    ((graft hc τ).restrict hY).toImage
  have homeo : ProperCovariantHomeomorphism (G := G) f :=
    graftPiece_home (G := G) h00 hc hκ hs hv hsmall hΓ A τ hτ Y hY hPY
  refine morphism_of_step h00 hc hs hsmall f homeo ?_ (fun p _ => ?_)
  · rcases n with _ | n
    · exact Or.inl rfl
    · refine Or.inr ⟨0, 0, fun p k _ => ?_⟩
      simp only [Equiv.symm_apply_apply]
      rfl
  · obtain ⟨L, ⟨F, hF, hL⟩, hdet⟩ := graft_unit_derivative hc hv τ hτ ⟨p.val, hY p.property⟩
    refine ⟨L, ⟨F, chart_restrict hv (graft hc τ) hY hPY p hF, hL⟩, ?_⟩
    rw [hdet]
    change vfValue 1 = (gammaMapValue A.form ⟨p.val, hY p.property⟩ /
      gammaMapValue (graftForm hc A τ) (graft hc τ ⟨p.val, hY p.property⟩)).val
    unfold gammaMapValue
    rw [graftForm_graft, div_self']
    change Values.vfValueHom 1 = Values.gammaValHom 1
    rw [map_one, map_one]

end Graft

/-! ### Morphisms fixing the VF coordinates -/

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ in
/-- A contraction of an object, in any order, exists. -/
theorem exists_nmc {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1)) (e : Equiv.Perm (Fin (n + 1))) :
    Nonempty (NormalizedMeasuredContraction (G := G) A.carrier A.form e) := by
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.proper
  obtain ⟨F, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.form (object_levels hv A) e D
  exact ⟨F⟩

include V hV hVT hTV hnt in
/-- **A morphism fixing the VF coordinates relates the classes of any two
contractions**, in any orders, of its source and target: Corollary 7.15 and `(∗)`
in dimension at least `2`, Lemma 7.13 in dimension `1`. -/
theorem ispRel_of_vfFixing {n : ℕ} {A B : VFObject (M := M) (T : Set M) (n + 1)} (K : Morphism G A B)
    (hK : ∀ p : A.carrier, (K.map p).val.1 = p.val.1) {σ σ' : Equiv.Perm (Fin (n + 1))}
    (FA : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (FB : NormalizedMeasuredContraction (G := G) B.carrier B.form σ') :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A FA) (clsOf h00 hc hκ hs hv hsmall hΓ B FB) := by
  cases n with
  | zero =>
    have h := lemma_7_13_of_support hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ⟨K⟩ FA FB
    exact (ispRel_iff (show 0 + 1 = 1 + 0 from rfl) _ _).mpr h
  | succ n =>
    obtain ⟨FB'⟩ := exists_nmc (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B σ
    have hu : VFRelativelyUnary K.map (σ (Fin.last (n + 1))) (σ (Fin.last (n + 1))) := fun p k _ => by
      rw [Equiv.symm_apply_apply]
      exact congrFun (hK p) k
    exact ispRel_trans (ProvedResults.corollary_7_15 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ K hu FA FB')
      (OrderIndependence.star h00 hc hκ hs hv (n + 1) T V hV hVT hTV hnt hsmall hΓ B FB' FB)

/-! ### Additivity along the scissor relation -/

include V hV hVT hTV hnt in
/-- **Additivity of contraction classes under the scissor relation.** For an
object `U` of `μVF^◇[n + 1]`, a definable proper invariant subset `X ⊆ U`, and
standard contractions `F`, `F₁`, `F₂` (in any orders) of `U`, `U|X` and `U ∖ X`,
the class of `F` is `μIsp^db`-related to the sum of the classes of `F₁` and
`F₂`. -/
theorem scissor_classes {n : ℕ} (U : VFObject (M := M) (T : Set M) (n + 1))
    (X : DefSet (rawMixedSpace (M := M) (n + 1) U.labels) (T : Set M)) (hX : X.carrier ⊆ U.carrier.carrier)
    (hP : ProperInvariant (T : Set M) X.carrier) {σ σ₁ σ₂ : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) U.carrier U.form σ)
    (F₁ : NormalizedMeasuredContraction (G := G) (restrictObject U X hX hP).carrier
      (restrictObject U X hX hP).form σ₁)
    (F₂ : NormalizedMeasuredContraction (G := G) (complObject U X hP).carrier (complObject U X hP).form σ₂) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ U F)
      (clsOf h00 hc hκ hs hv hsmall hΓ (restrictObject U X hX hP) F₁ +
        clsOf h00 hc hκ hs hv hsmall hΓ (complObject U X hP) F₂) := by
  let τ := tagMap X U.carrier
  have hτ : ProperCovariant τ := tagMap_properCovariant U.proper hP
  let U' := graftObject h00 hc hκ hs hv U τ hτ
  obtain ⟨K, hK⟩ := graftMorphism (G := G) h00 hc lin hκ hs hv hsmall hΓ U τ hτ
  obtain ⟨F'⟩ := exists_nmc (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ U' σ
  have h₀ := ispRel_of_vfFixing h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ K
    (fun p => by rw [hK]; rfl) F F'
  -- the two pieces
  let Y := U.carrier.sdiff X
  have hY : Y.carrier ⊆ U.carrier.carrier := fun _ h => h.1
  have hPY : ProperInvariant (T : Set M) Y.carrier := U.proper.diff hP
  have hdecX : ∀ p p' : U.carrier, (τ p).val = (τ p').val → p.val ∈ X.carrier → p'.val ∈ X.carrier :=
    fun p p' he hp => ((tagValue_eq_iff h00 X.carrier p.val p'.val).mp
      (congrFun (congrArg Prod.snd he) 0)).mp hp
  have hdecY : ∀ p p' : U.carrier, (τ p).val = (τ p').val → p.val ∈ Y.carrier → p'.val ∈ Y.carrier :=
    fun p p' he hp => ⟨p'.property, fun h => hp.2 (((tagValue_eq_iff h00 X.carrier p.val p'.val).mp
      (congrFun (congrArg Prod.snd he) 0)).mpr h)⟩
  have hCs := graftPiece_saturated h00 hc hκ hs hv U τ hτ X hX hdecX
  have hC's := graftPiece_saturated h00 hc hκ hs hv U τ hτ Y hY hdecY
  have hCp := graftPiece_proper (G := G) h00 hc hκ hs hv hsmall hΓ U τ hτ X hX hP
  have hC'p := graftPiece_proper (G := G) h00 hc hκ hs hv hsmall hΓ U τ hτ Y hY hPY
  have hdisj := graftPiece_disjoint hc U τ X Y hX hY (Set.disjoint_left.mpr fun _ h h' => h'.2 h)
  have hcover := graftPiece_cover h00 hc hκ hs hv U τ hτ X Y hX hY (fun p hp => by
    by_cases h : p ∈ X.carrier
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩)
  have split := cls_headStart_zero_split h00 hc lin hκ hs hv hsmall hΓ F' _ _ hCs hC's hCp hC'p hdisj hcover
    (object_hFin U' Fin.elim0)
  -- the pieces of the graft against the pieces of `U`
  obtain ⟨K₁, hK₁⟩ := graftPiece_morphism (G := G) h00 hc hκ hs hv hsmall hΓ U τ hτ X hX hP
  obtain ⟨K₂, hK₂⟩ := graftPiece_morphism (G := G) h00 hc hκ hs hv hsmall hΓ U τ hτ Y hY hPY
  have r₁ := ispRel_of_vfFixing h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ K₁ (fun p => by rw [hK₁]; rfl) F₁
    (restrictContraction h00 hc lin hκ hs hv hsmall hΓ F' _ hCs hCp)
  have r₂ := ispRel_of_vfFixing h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ K₂ (fun p => by rw [hK₂]; rfl) F₂
    (restrictContraction h00 hc lin hκ hs hv hsmall hΓ F' _ hC's hC'p)
  refine ispRel_trans h₀ ?_
  unfold clsOf at r₁ r₂ ⊢
  rw [split]
  exact ispRel_add (ispRel_symm r₁) (ispRel_symm r₂)

include V hV hVT hTV hnt in
/-- `scissor_classes` on the scissor relation of `K₊ μVF^◇[n + 1]`
(`DiamondGrothendieck.Scissor`): for a scissor `(A, B, D, ∅)`, the class of a
contraction of `D` is `μIsp^db`-related to the sum of the classes of contractions
of `A` and `B`. -/
theorem scissor_classes_of_scissor {n : ℕ} {A B D E : VFObject (M := M) (T : Set M) (n + 1)}
    (h : Scissor hc A B D E) {σ σ₁ σ₂ : Equiv.Perm (Fin (n + 1))}
    (FD : NormalizedMeasuredContraction (G := G) D.carrier D.form σ)
    (FA : NormalizedMeasuredContraction (G := G) A.carrier A.form σ₁)
    (FB : NormalizedMeasuredContraction (G := G) B.carrier B.form σ₂) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ D FD)
      (clsOf h00 hc hκ hs hv hsmall hΓ A FA + clsOf h00 hc hκ hs hv hsmall hΓ B FB) := by
  obtain ⟨U, X, hX, hP, rfl, rfl, rfl, -⟩ := h
  exact scissor_classes h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ _ X hX hP FD FA FB

end DiamondIntegral.Section7.ScissorClasses
