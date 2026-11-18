import «section 6».RowMeasuredDimensionPreparation
import «section 6».ProperPreparation
import «section 6».ProtectedInitialPreparation
import «section 6».UniformMixedRadius
import «section 6».InvarianceTopology

/-! Remark 6.20 (`cons:extra`) in every VF-dimension.

A proper covariant powerset-valued function `f : H → 𝒫(RV^q)` is given, as in
the text after Definition 6.2, by its membership relation
`Rel = {(p, s) : s ∈ f(p)} ⊆ VF^{n+1} × RV^{r+q}`. Proper covariance is
`ProperInvariant S Rel`: the RV-support of `Rel` is doubly bounded and every
membership section is proper invariant. The conclusion of Proposition 6.19
can then demand that `f ∘ T⁻¹` be rv-contractible: the rows of `Rel` agree at
points whose images have the same RV coordinates.

The rows are carried through the measured preparation as a row form
(`RowFormOn`). To have at least one row coordinate for the domain marker, a
constant coordinate `1` is appended (`paddedRow`). The case `n + 1 = 1` with
extra hypotheses is `remark_6_20_unary`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q k : ℕ}

/-- The row `f(p) ⊆ RV^q` of a membership relation `Rel ⊆ VFⁿ × RV^{r+q}`. -/
def rvDataRow (Rel : DefSet (rawMixedSpace (M := M) n (r+q)) S) (p : Mixed M n r) :
    Set (Fin q → RVInfinity M) :=
  {u | (p.1, Fin.append p.2 u) ∈ Rel.carrier}

/-- The rows of `Rel`, padded by a constant last coordinate `1`. -/
def paddedRow (Rel : DefSet (rawMixedSpace (M := M) n (r+q)) S)
    (x : (rawMixedSpace (M := M) n r).Carrier) (w : (rawRVSpace (M := M) (q+1)).Carrier) : Prop :=
  (x.1, Fin.append x.2 (Fin.init w)) ∈ Rel.carrier ∧ w (Fin.last q) = 1

theorem paddedRow_snoc_iff (Rel : DefSet (rawMixedSpace (M := M) n (r+q)) S) (p : Mixed M n r)
    (v : Fin q → RVInfinity M) :
    paddedRow Rel p (Fin.snoc v 1) ↔ v ∈ rvDataRow Rel p := by
  unfold paddedRow rvDataRow
  rw [Fin.init_snoc, Fin.snoc_last]
  simp only [Set.mem_setOf_eq, and_true]

/-- Coordinates of a padded row inside the coordinates of `Rel`. -/
def paddedIndex : Fin n ⊕ Fin (r+q) → (Fin n ⊕ Fin r) ⊕ Fin (q+1) :=
  Sum.elim (fun i => .inl (.inl i)) (Fin.addCases (fun a => .inl (.inr a)) (fun b => .inr (Fin.castSucc b)))

theorem paddedIndex_values (x : (rawMixedSpace (M := M) n r).Carrier)
    (w : Fin (q+1) → CanonicalRV.RVSort M) :
    Sum.elim (mixedValues x) (rvValues w) ∘ paddedIndex (n := n) (r := r) (q := q) =
      mixedValues (x.1, Fin.append x.2 (Fin.init w)) := by
  funext i
  rcases i with i | j
  · rfl
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simp only [Function.comp_apply, paddedIndex, Sum.elim_inr, Fin.addCases_left, Sum.elim_inl,
        mixedValues, rvValues, Fin.append_left]
    · simp only [Function.comp_apply, paddedIndex, Sum.elim_inr, Fin.addCases_right, mixedValues,
        rvValues, Fin.append_right, Fin.init]

theorem rvOne_coordinate_definable_at (S : Set M) {ι : Type} (i : ι) :
    S.Definable LRV {z : ι → M | z i = iRVOne} := by
  have hc : S.DefinableFun LRV (fun _ : ι → M => iRVOne) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvOne)).comp
      (show S.DefinableMap LRV (fun _ : ι → M => Fin.elim0) from fun j => j.elim0)
  exact (Set.DefinableFun.proj LRV).ofPred_eq hc

theorem paddedRow_definable (Rel : DefSet (rawMixedSpace (M := M) n (r+q)) S) :
    (rawMixedSpace (M := M) n r).RelationDefinable (rawRVSpace (M := M) (q+1)) S (paddedRow Rel) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawRVSpace (M := M) (q+1)
  let P' := rawMixedSpace (M := M) n (r+q)
  have h1 := (P.definable_domain S).preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
  have h2 := (Q.definable_domain S).preimage_comp (Sum.inr : Q.Index → P.Index ⊕ Q.Index)
  have h3 : S.Definable LRV (P'.preimage Rel.carrier) := Rel.definable
  have h3' := h3.preimage_comp (paddedIndex (n := n) (r := r) (q := q))
  have h4 := rvOne_coordinate_definable_at S (Sum.inr (Fin.last q) : P.Index ⊕ Q.Index)
  change S.Definable LRV (P.relation Q (paddedRow Rel))
  convert ((h1.inter h2).inter h3').inter h4 using 1
  ext z
  have key : ∀ (hx : z ∘ Sum.inl ∈ P.domain) (hy : z ∘ Sum.inr ∈ Q.domain),
      z = Sum.elim (mixedValues (P.decode ⟨z ∘ Sum.inl, hx⟩)) (rvValues (Q.decode ⟨z ∘ Sum.inr, hy⟩)) := by
    intro hx hy
    funext i
    rcases i with i | i
    · exact (congrFun (mixedValues_decode (n := n) (r := r) ⟨z ∘ Sum.inl, hx⟩) i).symm
    · exact (congrFun (rvValues_decode (M := M) ⟨z ∘ Sum.inr, hy⟩) i).symm
  constructor
  · rintro ⟨hx, hy, hRel, hlast⟩
    have hz := key hx hy
    refine ⟨⟨⟨hx, hy⟩, ?_⟩, ?_⟩
    · change z ∘ paddedIndex ∈ P'.preimage Rel.carrier
      rw [hz, paddedIndex_values]
      exact (P'.preimage_decode Rel.carrier ⟨_, mixedValues_mem_domain _⟩).mpr
        (by rw [decode_mixedValues]; exact hRel)
    · change z (Sum.inr (Fin.last q)) = iRVOne
      rw [hz]
      change (Q.decode ⟨z ∘ Sum.inr, hy⟩ (Fin.last q)).val = iRVOne
      rw [hlast]
      exact RVOperations.one_val
  · rintro ⟨⟨⟨hx, hy⟩, hR⟩, hlast⟩
    have hz := key hx hy
    refine ⟨hx, hy, ?_, ?_⟩
    · change z ∘ paddedIndex ∈ P'.preimage Rel.carrier at hR
      rw [hz, paddedIndex_values] at hR
      have h := (P'.preimage_decode Rel.carrier ⟨_, mixedValues_mem_domain _⟩).mp hR
      rwa [decode_mixedValues] at h
    · apply Subtype.ext
      have h : z (Sum.inr (Fin.last q)) = iRVOne := hlast
      rw [hz] at h
      exact h.trans RVOperations.one_val.symm

theorem paddedRow_bounded (A : DefSet (rawMixedSpace (M := M) n r) S)
    (Rel : DefSet (rawMixedSpace (M := M) n (r+q)) S) (hRel : RVSupportDoublyBounded Rel.carrier) :
    ∃ γ : Gamma M, ∀ a : A, ∀ v, paddedRow Rel a.val v → ∀ i,
      (γ⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ γ.val := by
  obtain ⟨η, hη⟩ := hRel
  have hone : (1 : Values.Gamma (M := M)) ≤ max η η⁻¹ := by
    rcases le_total (1 : Values.Gamma (M := M)) η with h | h
    · exact h.trans (le_max_left _ _)
    · exact (one_le_inv'.mpr h).trans (le_max_right _ _)
  refine ⟨max η η⁻¹, ?_⟩
  rintro a v ⟨hv, hlast⟩ i
  refine Fin.lastCases ?_ (fun b => ?_) i
  · rw [hlast, RVOperations.vrv_one, ← Values.gamma_val_one]
    have h1 : (max η η⁻¹)⁻¹ ≤ (1 : Values.Gamma (M := M)) := inv_le_one'.mpr hone
    exact ⟨h1, hone⟩
  · have h := hη _ hv (Fin.natAdd r b)
    change (η⁻¹).val ≤ Values.vrv (Fin.append a.val.2 (Fin.init v) (Fin.natAdd r b)) ∧
      Values.vrv (Fin.append a.val.2 (Fin.init v) (Fin.natAdd r b)) ≤ η.val at h
    rw [Fin.append_right] at h
    change (η⁻¹).val ≤ Values.vrv (v (Fin.castSucc b)) ∧ Values.vrv (v (Fin.castSucc b)) ≤ η.val at h
    have h2 : (max η η⁻¹)⁻¹ ≤ η⁻¹ := inv_le_inv_iff.mpr (le_max_left η η⁻¹)
    have h3 : η ≤ max η η⁻¹ := le_max_left η η⁻¹
    exact ⟨le_trans (h2 : ((max η η⁻¹)⁻¹).val ≤ (η⁻¹).val) h.1,
      le_trans h.2 (h3 : η.val ≤ (max η η⁻¹).val)⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem paddedRow_levels_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (Rel : DefSet (rawMixedSpace (M := M) n (r+q)) S) (hRel : ProperInvariant S Rel.carrier)
    (hB : ∃ γ : Gamma M, ∀ a : A, ∀ v, paddedRow Rel a.val v → ∀ i,
      (γ⁻¹).val ≤ Values.vrv (v i) ∧ Values.vrv (v i) ≤ γ.val) :
    ∀ u γ, IsOpen {x : Fin n → VF M | (x,u) ∈ A.carrier ∧
      rowFormExtension (rowFormOfRelation A (paddedRow Rel) (paddedRow_definable Rel) hB) (x,u) = γ} := by
  obtain ⟨δ, -, -, hδ⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hRel
  intro u γ
  let X : Set (Fin n → VF M) := {x | ∀ w, paddedRow Rel (x,u) w ↔ w ∈ γ}
  have hX : AlphaInvariant (fun _ => δ) X := by
    intro x y hxy
    have hrow : ∀ w, paddedRow Rel (x,u) w ↔ paddedRow Rel (y,u) w := by
      intro w
      unfold paddedRow
      exact and_congr (hδ (Fin.append u (Fin.init w)) x y hxy) Iff.rfl
    constructor
    · intro hx w
      exact (hrow w).symm.trans (hx w)
    · intro hy w
      exact (hrow w).trans (hy w)
  have he : {x : Fin n → VF M | (x,u) ∈ A.carrier ∧
      rowFormExtension (rowFormOfRelation A (paddedRow Rel) (paddedRow_definable Rel) hB) (x,u) = γ} =
      vfFibre A.carrier u ∩ X := by
    ext x
    constructor
    · rintro ⟨hxA, hx⟩
      refine ⟨hxA, fun w => ?_⟩
      rw [← hx, rowFormExtension, dif_pos (show (x,u) ∈ A.carrier from hxA)]
      rfl
    · rintro ⟨hxA, hx⟩
      refine ⟨hxA, ?_⟩
      rw [rowFormExtension, dif_pos (show (x,u) ∈ A.carrier from hxA)]
      ext w
      exact hx w
  rw [he]
  exact (hA.clopen_fibres hv u).isOpen.inter (hX.isOpen hv)

/-- **Remark 6.20** (`cons:extra`) in VF-dimension `n + 1`. With the hypotheses
of Proposition 6.19, let `Rel ⊆ VF^{n+1} × RV^{r+q}` be the membership relation
of a proper covariant `f : A → 𝒫(RV^q)` (`ProperInvariant S Rel`). Then the
special covariant bijection `T` of Proposition 6.19 can be chosen so that, in
addition, `f ∘ T⁻¹` is rv-contractible: points whose images under `T` have the
same RV coordinates have the same row `f(p) = rvDataRow Rel p`. -/
theorem remark_6_20
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V, iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (Rel : DefSet (rawMixedSpace (M := M) (n+1) (r+q)) S) (hRel : ProperInvariant S Rel.carrier) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) (n+1) s) S, ∃ f : Map A B,
      SpecialCovariantChain (G := G) A B f ∧ ProperInvariant S B.carrier ∧
      VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      (∀ i, SpecialCovariantChain (G := G) (P i) (f.restrict (hPA i)).image (f.restrict (hPA i)).toImage ∧
        IsRVPullback (f.restrict (hPA i)).image.carrier) ∧
      ∀ p z : A, (f p).val.2 = (f z).val.2 → rvDataRow Rel p.val = rvDataRow Rel z.val := by
  obtain ⟨A₀, f₀, hf₀, hA₀, hD₀, hRP₀, hTag₀, hPieces₀⟩ := exists_initial_preparation_protecting_family
    (G := G) h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA P hPA hP
  have hB := paddedRow_bounded A Rel hRel.rvBounded
  let ρ := rowFormOfRelation A (paddedRow Rel) (paddedRow_definable Rel) hB
  have hLevels := paddedRow_levels_open (G := G) h00 hc linear hκ hs hv hsmall hΓ A hA Rel hRel hB
  have hbij := hf₀.bijective h00
  let ρ₀ : RowFormOn A₀ (q+1) := ρ.comp (f₀.inverse hbij)
  have hTransport₀ : ∀ p : A, (ρ₀ (f₀ p)).val = (ρ p).val := by
    intro p
    change (ρ (f₀.inverse hbij (f₀ p))).val = _
    rw [Map.inverse_apply]
  have hLevels₀ := hf₀.exact_gamma_levels_open_row h00 hc linear hκ hs hv hsmall hΓ ρ hLevels ρ₀ hTransport₀
  let P₀ (i : Fin k) := (f₀.restrict (hPA i)).image
  have hP₀A₀ (i : Fin k) : (P₀ i).carrier ⊆ A₀.carrier := by
    rintro q' ⟨p, hp⟩
    exact hp ▸ (f₀ ⟨p.val, hPA i p.property⟩).property
  obtain ⟨F, -⟩ := measured_form_compatible_preparation_all_dimensions_row (qR := q+1) (G := G)
    h00 hc linear hκ hs hv n S V hsmall hΓ hV hVS hSV hnt k _ A₀ hA₀ hD₀ (hRP₀ hARV) P₀ hP₀A₀
    (fun i => (hPieces₀ i).2) ρ₀ hLevels₀
  let g := F.map.comp f₀
  refine ⟨F.arity, F.target, g, .comp hf₀ F.special, F.proper, F.doublyBounded, F.prepared,
    fun i => ?_, ?_⟩
  · have hComp := SpecialCovariantChain.comp (hPieces₀ i).1 (F.pieces i).1
    have hImage : (F.map.restrict (hP₀A₀ i)).image = (g.restrict (hPA i)).image :=
      image_eq_of_surjective_liesOver g
        ((F.map.restrict (hP₀A₀ i)).toImage.comp (f₀.restrict (hPA i)).toImage)
        (hComp.bijective h00).surjective (hPA i) (fun _ => rfl)
    exact ⟨hComp.restriction_of_liesOver h00 g (hPA i) (fun _ => rfl), hImage ▸ (F.pieces i).2⟩
  · intro p z hpz
    have h1 := F.constant (g p).val (g p).property (g z).val (g z).property hpz
    change rowFormExtension F.form (F.map (f₀ p)).val = rowFormExtension F.form (F.map (f₀ z)).val at h1
    rw [rowFormExtension_at, rowFormExtension_at, F.transportRow, F.transportRow,
      hTransport₀, hTransport₀] at h1
    ext v
    rw [← paddedRow_snoc_iff, ← paddedRow_snoc_iff]
    have hm := congrArg (fun T : Set (rawRVSpace (M := M) (q+1)).Carrier => Fin.snoc v 1 ∈ T) h1
    exact iff_of_eq hm

end DiamondIntegral.Section6
