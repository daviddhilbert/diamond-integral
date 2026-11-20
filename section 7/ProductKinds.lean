import «section 7».Lemma722Cells
import «section 7».ProductCells
import «section 7».TwoCellGeometry
import «section 6».InitialPreparation

/-! Cells with constant or narrow positioning are products (for Lemma 7.22).

A `2`-cell of kind `0` (constant positioning function) or kind `1` (injective,
disc-to-disc, image an open disc of radius at least `vrv(t)`) has the same
fibre over every point of its first projection: translating `t^♯` by an
element of value larger than `vrv(t)` does not change it
(`sharp_translate`). So such a cell is the product of its two projections
(`product_of_kind`). This is the first case in the paper's proof of Lemma 7.21:
"`A` is a product of two open discs".

In the object `A*` of Lemma 7.22 the kind is a function of the labels. The
labels of kind `0` or `1` form a definable set `prodLabels`, and the piece of
`A*` over it is a fibre product over its labels (`prodPiece_product`), so
`ProductCells` applies to it. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ProductKinds
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.TwoCells DiamondIntegral.Section7.TwoCellGeometry DiamondIntegral.Section7.TwoCellInput

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Geometry of the cells -/

section Geometry
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Points closer to `b` than `b` is to `0` have the leading term of `b`. -/
theorem rv_eq_of_value_lt {a b : VF M} (hb : b ≠ 0) (h : vfValue b < vfValue (a - b)) : rv M a = rv M b := by
  apply Subtype.ext
  change iRv a.val = iRv b.val
  rw [CanonicalRV.encoded_eq_iff_close a.property b.property (fun he => hb (Subtype.ext he))]
  change ¬ VFValued.predV b (a - b)
  rw [Values.vf_pred_iff_gamma_le]
  exact not_le.mpr h

/-- A point of an open disc of radius `γ` around `x` is at value larger than
`γ` from `x`. -/
theorem lt_value_of_mem_openDisc (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {x y : VF M} {γ : Gamma M} (hy : y.val ∈ BallImaginaries.underlying (openDiscCode x γ)) :
    γ.val < vfValue (y - x) := by
  have hr : radiusRepresentative γ.val ≠ 0 := fun he => γ.property ((radiusRepresentative_zero_iff γ.val).mp he)
  have hγ : finiteValue (radiusRepresentative γ.val) hr = γ := Subtype.ext (radiusRepresentative_value γ.val)
  have h := openDiscCode_points Valued.v hv x (radiusRepresentative γ.val) hr
  rw [hγ] at h
  have hy' : y ∈ discPoints (openDiscCode x γ) := hy
  rw [h, Balls.openDisc_openRadius] at hy'
  have hnot : ¬ VFValued.predV (radiusRepresentative γ.val) (y - x) := fun hp =>
    absurd ((hv _ _).mp hp) (not_le.mpr hy')
  rw [Values.vf_pred_iff_gamma_le] at hnot
  have hlt := lt_of_not_ge hnot
  have hrv : vfValue (radiusRepresentative γ.val) = γ.val := radiusRepresentative_value γ.val
  rw [← hrv]
  exact hlt

/-- Translating `t^♯` by an element of value larger than `vrv(t)` does not
change it. -/
theorem sharp_translate {t : RV M} {c d : VF M} (hd : Values.vrv t.val < vfValue d) :
    (· + c) '' sharpSet t.val = (· + (c + d)) '' sharpSet t.val := by
  have key : ∀ (y e : VF M), rv M y = t.val → Values.vrv t.val < vfValue e → rv M (y + e) = t.val := by
    intro y e hy he
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, rv_zero] at hy
      exact t.property hy.symm
    have hval : vfValue y = Values.vrv t.val := by rw [vfValue, hy]
    rw [← hy]
    apply rv_eq_of_value_lt hy0
    rw [hval, add_sub_cancel_left]
    exact he
  have hneg : Values.vrv t.val < vfValue (-d) := by
    have h := SpecialTransformations.Section9.vfValue_neg (M := M) d
    change Values.vrv t.val < Values.vfValueHom (-d)
    rw [h]
    exact hd
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - d, ?_, ?_⟩
    · show rv M (y - d) = t.val
      rw [sub_eq_add_neg]
      exact key y (-d) hy hneg
    · change y - d + (c + d) = y + c
      ring
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y + d, key y d hy hd, ?_⟩
    change y + d + c = y + (c + d)
    ring

/-- In a cell with narrow image, all fibres agree. -/
theorem fibres_eq_of_narrow (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : Set (VF M × VF M)} {ε : VF M → VF M} {t : RV M}
    (hfib : ∀ a ∈ first C, fibre C a = (· + ε a) '' sharpSet t.val) (hn : NarrowCase C ε t) :
    ∀ a ∈ first C, ∀ a' ∈ first C, fibre C a = fibre C a' := by
  obtain ⟨-, -, x, γ, himg, hγt⟩ := hn
  have hmem : ∀ a ∈ first C, γ.val < vfValue (ε a - x) := by
    intro a ha
    have h : (ε a).val ∈ Subtype.val '' (ε '' first C) := ⟨ε a, ⟨a, ha, rfl⟩, rfl⟩
    rw [himg] at h
    exact lt_value_of_mem_openDisc hv h
  intro a ha a' ha'
  rw [hfib a ha, hfib a' ha']
  have hmin := SpecialTransformations.Section9.vfValue_min_le_sub (M := M) (ε a' - x) (ε a - x)
  change min (vfValue (ε a' - x)) (vfValue (ε a - x)) ≤ vfValue ((ε a' - x) - (ε a - x)) at hmin
  have hd : Values.vrv t.val < vfValue (ε a' - ε a) := by
    rw [show (ε a' - x) - (ε a - x) = ε a' - ε a by ring] at hmin
    exact lt_of_le_of_lt hγt (lt_of_lt_of_le (lt_min (hmem a' ha') (hmem a ha)) hmin)
  rw [sharp_translate (c := ε a) hd]
  congr 1
  funext y
  ring

/-- In a cell of kind `0` or `1`, all fibres agree. -/
theorem fibres_eq_of_kind (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : Set (VF M × VF M)} {ε : VF M → VF M} {t : RV M} {t₁ : RVInfinity M} {k : Fin 3}
    (h : CellWith C ε t t₁ k) (hk : k ≠ 2) : ∀ a ∈ first C, ∀ a' ∈ first C, fibre C a = fibre C a' := by
  obtain ⟨-, -, hfib, h0, h1, -⟩ := h
  match k, hk, h0, h1 with
  | 0, _, h0, _ => exact fibres_eq_of_constant hfib (h0 rfl)
  | 1, _, _, h1 => exact fibres_eq_of_narrow hv hfib (h1 rfl)
  | 2, hk, _, _ => exact absurd rfl hk

/-- **A cell of kind `0` or `1` is a product.** -/
theorem product_of_kind (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : Set (VF M × VF M)} {ε : VF M → VF M} {t : RV M} {t₁ : RVInfinity M} {k : Fin 3}
    (h : CellWith C ε t t₁ k) (hk : k ≠ 2) (a b : VF M) : (a, b) ∈ C ↔ a ∈ first C ∧ b ∈ second C := by
  have hfe := fibres_eq_of_kind hv h hk
  constructor
  · intro hab
    exact ⟨⟨(a, b), hab, rfl⟩, ⟨(a, b), hab, rfl⟩⟩
  · rintro ⟨⟨⟨a', b'⟩, hab', rfl⟩, ⟨⟨a'', b''⟩, hab'', rfl⟩⟩
    have h1 : b'' ∈ fibre C a'' := hab''
    have ha' : a' ∈ first C := ⟨(a', b'), hab', rfl⟩
    have ha'' : a'' ∈ first C := ⟨(a'', b''), hab'', rfl⟩
    rw [hfe a'' ha'' a' ha'] at h1
    exact h1

end Geometry

/-! ### The product piece of `A*` -/

section Object
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {T : LRV.Substructure M} {r : ℕ} {A : DefSet (rawMixedSpace (M := M) 2 r) (T : Set M)}
variable {e : Equiv.Perm (Fin 2)}
open DiamondIntegral.Section7.Lemma722Cells DiamondIntegral.Section7.LabelPieces

/-- The uniform cell data of the Lemma 7.20 input, as data. -/
structure CellData (F : StandardContraction (G := G) A e) where
  ε : (Fin F.arity → RVInfinity M) → VF M → VF M
  t : (Fin F.arity → RVInfinity M) → RV M
  t₁ : (Fin F.arity → RVInfinity M) → RVInfinity M
  kind : (Fin F.arity → RVInfinity M) → Fin 3
  focusGraph : (T : Set M).Definable LRV {z : Fin (2 + F.arity) → M | ∃ s : F.rvTarget, ∃ a ∈ first (cellAt F s),
    z = Fin.append ![a.val, (ε s.val.2 a).val] (rvValues s.val.2)}
  paradigmGraph : (T : Set M).Definable LRV {z : Fin (1 + F.arity) → M | ∃ s : F.rvTarget,
    z = Fin.append ![(t s.val.2).val.val] (rvValues s.val.2)}
  secondGraph : (T : Set M).Definable LRV {z : Fin (1 + F.arity) → M | ∃ s : F.rvTarget, kind s.val.2 = 2 ∧
    z = Fin.append ![(t₁ s.val.2).val] (rvValues s.val.2)}
  kindPieces : ∀ i : Fin 3, (T : Set M).Definable LRV {z : Fin F.arity → M | ∃ s : F.rvTarget, kind s.val.2 = i ∧
    z = rvValues s.val.2}
  cells : ∀ s : F.rvTarget, CellWith (cellAt F s) (ε s.val.2) (t s.val.2) (t₁ s.val.2) (kind s.val.2)

theorem nonempty_cellData {F : StandardContraction (G := G) A e} (h : UniformTwoCells F) : Nonempty (CellData F) := by
  obtain ⟨ε, t, t₁, kind, h1, h2, h3, h4, h5⟩ := h
  exact ⟨⟨ε, t, t₁, kind, h1, h2, h3, h4, h5⟩⟩

/-- The codes of the RV points of kind `0` or `1`. -/
def prodCodes {F : StandardContraction (G := G) A e} (Dt : CellData F) {m : ℕ} : Set (Fin (m + F.arity) → M) :=
  (fun z => fun j => z (Fin.natAdd m j)) ⁻¹'
    ({z | ∃ s : F.rvTarget, Dt.kind s.val.2 = 0 ∧ z = rvValues s.val.2} ∪
      {z | ∃ s : F.rvTarget, Dt.kind s.val.2 = 1 ∧ z = rvValues s.val.2})

theorem prodCodes_definable {F : StandardContraction (G := G) A e} (Dt : CellData F) (m : ℕ) :
    (T : Set M).Definable LRV (prodCodes Dt (m := m)) :=
  ((Dt.kindPieces 0).union (Dt.kindPieces 1)).preimage_comp (Fin.natAdd m)

/-- **The labels of kind `0` or `1`**, read on the last `F.arity` labels. -/
def prodLabels {F : StandardContraction (G := G) A e} (Dt : CellData F) (m : ℕ) :
    DefSet (rawRVSpace (M := M) (m + F.arity)) (T : Set M) :=
  ⟨{w | rvValues w ∈ prodCodes Dt (m := m)}, rvValues_preimage_definable _ (prodCodes_definable Dt m)⟩

theorem kind_ne_two {k : Fin 3} : k ≠ 2 ↔ k = 0 ∨ k = 1 := by
  constructor
  · intro h
    match k, h with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr rfl
    | 2, h => exact absurd rfl h
  · rintro (rfl | rfl) <;> decide

theorem mem_prodLabels {F : StandardContraction (G := G) A e} (Dt : CellData F) {m : ℕ}
    (w : Fin (m + F.arity) → RVInfinity M) :
    w ∈ (prodLabels Dt m).carrier ↔
      ∃ s : F.rvTarget, Dt.kind s.val.2 ≠ 2 ∧ (fun j => w (Fin.natAdd m j)) = s.val.2 := by
  have hinj : ∀ s : F.rvTarget, (fun j => rvValues w (Fin.natAdd m j)) = rvValues s.val.2 ↔
      (fun j => w (Fin.natAdd m j)) = s.val.2 := by
    intro s
    constructor
    · intro h
      exact rvValues_injective h
    · intro h
      rw [← h]
      rfl
  show rvValues w ∈ prodCodes Dt (m := m) ↔ _
  rw [prodCodes, Set.mem_preimage]
  constructor
  · rintro (⟨s, hk, hs⟩ | ⟨s, hk, hs⟩)
    · exact ⟨s, kind_ne_two.mpr (Or.inl hk), (hinj s).mp hs⟩
    · exact ⟨s, kind_ne_two.mpr (Or.inr hk), (hinj s).mp hs⟩
  · rintro ⟨s, hk, hs⟩
    rcases kind_ne_two.mp hk with hk | hk
    · exact Or.inl ⟨s, hk, (hinj s).mpr hs⟩
    · exact Or.inr ⟨s, hk, (hinj s).mpr hs⟩

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable (A' : VFObject (M := M) (T : Set M) 2) (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z)
variable (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F)

/-- The piece of `A*` over the labels of kind `0` or `1`. -/
abbrev prodPiece : VFObject (M := M) (T : Set M) 2 :=
  pieceObject (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F) (prodLabels Dt (2 + A'.labels))

omit [M ⊨ Axioms.ACVF] in
/-- A point of `Fin 2 → VF M` is determined by its values at `e 0` and `e 1`. -/
theorem eq_of_perm_values (e : Equiv.Perm (Fin 2)) {x x' : Fin 2 → VF M} (h0 : x' (e 0) = x (e 0))
    (h1 : x' (e 1) = x (e 1)) : x' = x := by
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  match j with
  | 0 => exact h0
  | 1 => exact h1

/-- **The product piece is a fibre product over its labels.** -/
theorem prodPiece_product (x : Fin 2 → VF M) (w : Fin ((2 + A'.labels) + F.arity) → RVInfinity M) :
    (x, w) ∈ (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier ↔
      (∃ y : Fin 2 → VF M, (y, w) ∈ (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier ∧
        y 0 = x 0) ∧
      (∃ y : Fin 2 → VF M, (y, w) ∈ (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier ∧
        y 1 = x 1) := by
  constructor
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨y, hy, hy0⟩, ⟨y', hy', hy1⟩⟩
    obtain ⟨hyA, hw⟩ := hy
    obtain ⟨s, hk, hsw⟩ := (mem_prodLabels Dt w).mp hw
    have hex : ∃ x : Fin 2 → VF M, (x, w) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier :=
      ⟨y, hyA⟩
    have hpt : pointOf h00 hc linear hκ hs hv hsmall hΓ A' hω F w hex = s :=
      Subtype.ext (Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) hsw)
    have hcell := cellOf_eq h00 hc linear hκ hs hv hsmall hΓ A' hω F w hex
    rw [hpt] at hcell
    have hprod := product_of_kind hv (Dt.cells s) hk
    have hmemcell : ∀ z : Fin 2 → VF M, (z, w) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier →
        (z (e 0), z (e 1)) ∈ cellAt F s := by
      intro z hz
      rw [← hcell]
      exact ⟨z, hz, rfl⟩
    have hval : ∀ i : Fin 2, ∃ z : Fin 2 → VF M,
        (z, w) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier ∧ z i = x i := by
      intro i
      match i with
      | 0 => exact ⟨y, hyA, hy0⟩
      | 1 => exact ⟨y', hy'.1, hy1⟩
    obtain ⟨z₀, hz₀, hz₀e⟩ := hval (e 0)
    obtain ⟨z₁, hz₁, hz₁e⟩ := hval (e 1)
    have hfirst : x (e 0) ∈ first (cellAt F s) := hz₀e ▸ ⟨_, hmemcell z₀ hz₀, rfl⟩
    have hsecond : x (e 1) ∈ second (cellAt F s) := hz₁e ▸ ⟨_, hmemcell z₁ hz₁, rfl⟩
    have hin : (x (e 0), x (e 1)) ∈ cellAt F s := (hprod _ _).mpr ⟨hfirst, hsecond⟩
    rw [← hcell] at hin
    obtain ⟨x', hx', he⟩ := hin
    have hxx : x' = x := eq_of_perm_values e (congrArg Prod.fst he).symm (congrArg Prod.snd he).symm
    rw [hxx] at hx'
    exact ⟨hx', hw⟩

theorem prodPiece_doublyBounded :
    VFDoublyBounded (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier := by
  obtain ⟨δ, hδ⟩ := cellObject_doublyBounded h00 hc linear hκ hs hv hsmall hΓ A' hω F
  exact ⟨δ, fun p hp i => hδ p hp.1 i⟩

theorem prodPiece_form_labels :
    ∀ p z : (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier, p.val.2 = z.val.2 →
      (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).form p =
        (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).form z :=
  fun p z he => cellObject_form_labels h00 hc linear hκ hs hv hsmall hΓ A' hω F ⟨p.val, p.property.1⟩
    ⟨z.val, z.property.1⟩ he

open DiamondIntegral.Section7.PieceCombination DiamondIntegral.Section7.ProductCells
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Corollary715

/-- **Lemma 7.21 on the product piece of `A*`.** -/
theorem prodPiece_orders (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
    (hTV : (T : Set M) ⊆ algebraicClosureSet V) (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    OrdersRelated (G := G) h00 hc hκ hs hv hsmall hΓ (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt) := by
  obtain ⟨DP⟩ := exists_zeroCentered_data (G := G) h00 hc linear hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier
    (prodPiece h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).proper
  have hW : ImageProduct DP := imageProduct_of_product DP
    (prodPiece_doublyBounded h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt)
    (prodPiece_product h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt)
  obtain ⟨G₁, G₂, h⟩ := exists_product_orders (G := G) h00 hc lin hκ hs hv hsmall hΓ V hV hVT hTV hnt hW
    (prodPiece_form_labels h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt)
  exact ⟨G₁, G₂, ispRel_of_eq (h _ _)⟩

end Object

end DiamondIntegral.Section7.ProductKinds
