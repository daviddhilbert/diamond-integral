import «section 7».Lemma723Two
import «section 7».BalancedShearStages

/-! The balanced piece of `A*` as input of the balanced translation (for
Lemma 7.21).

In the object `A*` of Lemma 7.22 the labels of kind `2` form the balanced piece
`balObj` (the complement of `ProductKinds.prodLabels`). Each of its label fibres,
read in the order `(x_{e 0}, x_{e 1})` of the Lemma 7.20 contraction, is a
balanced `2`-cell `cellAt F s` of kind `2` (`balObj_cell`).

For a zero-centred normalization `D` of the balanced piece (which fixes the VF
coordinates, the piece being doubly bounded), the prepared set
`Y = D(balObj) ∘ e` has the same cells, read on its labels `u = (tags, v)`
(`cell_prepared`). With the cell data of the Lemma 7.20 input read on the last
labels (`sOf`), it satisfies `BalancedShearStages.BalancedShearInput`
(`preparedInput`): it is proper invariant, doubly bounded and tagged, every
nonempty cell is balanced, the shift is genuine (a balanced positioning function
maps the first projection onto the second, which lies in one RV-disc), and the
graphs of the positioning functions and paradigms are definable over the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BalancedKinds
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.TwoCells DiamondIntegral.Section7.TwoCellInput
open DiamondIntegral.Section7.LabelPieces DiamondIntegral.Section7.Lemma722Cells
open DiamondIntegral.Section7.ProductKinds DiamondIntegral.Section7.BalancedShearStages

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable (A' : VFObject (M := M) (T : Set M) 2) (hω : ∀ p z : A'.carrier, p.val.2 = z.val.2 → A'.form p = A'.form z)
variable {e : Equiv.Perm (Fin 2)} (F : StandardContraction (G := G) A'.carrier e) (Dt : CellData F)

/-- The balanced piece of `A*`: the labels of kind `2`. -/
abbrev balObj : VFObject (M := M) (T : Set M) 2 :=
  pieceObject (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F) (complLabels (prodLabels Dt (2 + A'.labels)))

theorem balObj_doublyBounded : VFDoublyBounded (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier := by
  obtain ⟨δ, hδ⟩ := cellObject_doublyBounded h00 hc linear hκ hs hv hsmall hΓ A' hω F
  exact ⟨δ, fun p hp i => hδ p hp.1 i⟩

/-- **The cells of the balanced piece** are cells of kind `2` of the Lemma 7.20
contraction. -/
theorem balObj_cell (v : Fin ((2 + A'.labels) + F.arity) → RVInfinity M)
    (hv' : ∃ x : Fin 2 → VF M, (x, v) ∈ (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier) :
    ∃ s : F.rvTarget, s.val.2 = (fun j => v (Fin.natAdd _ j)) ∧ Dt.kind s.val.2 = 2 ∧
      cellOf (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier e v = cellAt F s := by
  obtain ⟨x, hxA, hvL⟩ := hv'
  have hex : ∃ x : Fin 2 → VF M, (x, v) ∈ (cellObject h00 hc linear hκ hs hv hsmall hΓ A' hω F).carrier.carrier :=
    ⟨x, hxA⟩
  refine ⟨pointOf h00 hc linear hκ hs hv hsmall hΓ A' hω F v hex, rfl, ?_, ?_⟩
  · by_contra hk
    exact hvL ((mem_prodLabels Dt v).mpr ⟨_, hk, rfl⟩)
  · rw [← cellOf_eq h00 hc linear hκ hs hv hsmall hΓ A' hω F v hex]
    ext q
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨x', hx'.1, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨x', ⟨hx', hvL⟩, rfl⟩

variable (D : ZeroCenteredData (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier)

/-- The prepared set of the balanced piece in the order `e`. -/
abbrev prepared : DefSet (rawMixedSpace (M := M) 2 (2 + ((2 + A'.labels) + F.arity))) (T : Set M) :=
  reindexedVFSet D.map.image e

/-- The RV point of the contraction, read on the labels of the prepared set. -/
def sOf (u : Fin (2 + ((2 + A'.labels) + F.arity)) → RVInfinity M) : Fin F.arity → RVInfinity M :=
  fun j => u (Fin.natAdd 2 (Fin.natAdd (2 + A'.labels) j))

omit [M ⊨ Axioms.ACVF] in
theorem perm_symm_vec (e : Equiv.Perm (Fin 2)) (x : Fin 2 → VF M) : ![x (e 0), x (e 1)] ∘ e.symm = x := by
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  match j with
  | 0 => rfl
  | 1 => rfl

omit [M ⊨ Axioms.ACVF] in
theorem vec_perm_symm (e : Equiv.Perm (Fin 2)) (a b : VF M) :
    (![a, b] ∘ e.symm) (e 0) = a ∧ (![a, b] ∘ e.symm) (e 1) = b := by
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  exact ⟨rfl, rfl⟩

/-- Membership in the prepared set. -/
theorem mem_prepared (a b : VF M) (u : Fin (2 + ((2 + A'.labels) + F.arity)) → RVInfinity M) :
    (![a, b], u) ∈ (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D).carrier ↔
      ∃ v, (![a, b] ∘ e.symm, v) ∈ (balObj h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt).carrier.carrier ∧
        u = Fin.append (fun _ : Fin 2 => branchTag (M := M) false) v := by
  rw [mem_reindexedVFSet]
  exact ProductCells.mem_image_doublyBounded D (balObj_doublyBounded h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt) _ u

/-- **The cells of the prepared set.** -/
theorem cell_prepared (u : Fin (2 + ((2 + A'.labels) + F.arity)) → RVInfinity M)
    (hne : (cell (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D) u).Nonempty) :
    ∃ s : F.rvTarget, s.val.2 = sOf A' F u ∧ Dt.kind s.val.2 = 2 ∧
      cell (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D) u = cellAt F s := by
  obtain ⟨⟨a₀, b₀⟩, h₀⟩ := hne
  obtain ⟨v₀, hv₀, rfl⟩ := (mem_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D a₀ b₀ u).mp h₀
  obtain ⟨s, hs2, hk, hcell⟩ := balObj_cell h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt v₀ ⟨_, hv₀⟩
  refine ⟨s, ?_, hk, ?_⟩
  · rw [hs2]
    funext j
    simp only [sOf, Fin.append_right]
  · rw [← hcell]
    have happ : ∀ v : Fin ((2 + A'.labels) + F.arity) → RVInfinity M,
        Fin.append (fun _ : Fin 2 => branchTag (M := M) false) v =
          Fin.append (fun _ : Fin 2 => branchTag (M := M) false) v₀ → v = v₀ := fun v h =>
      funext fun i => by simpa only [Fin.append_right] using congrFun h (Fin.natAdd 2 i)
    ext ⟨a, b⟩
    constructor
    · intro hab
      obtain ⟨v, hv, hvu⟩ := (mem_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D a b _).mp hab
      obtain rfl := happ v hvu.symm
      refine ⟨_, hv, ?_⟩
      obtain ⟨h0, h1⟩ := vec_perm_symm e a b
      rw [h0, h1]
    · rintro ⟨x, hx, he⟩
      have hab : (a, b) = (x (e 0), x (e 1)) := he
      refine (mem_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D a b _).mpr ⟨v₀, ?_, rfl⟩
      rw [Prod.mk.injEq] at hab
      rw [hab.1, hab.2, perm_symm_vec]
      exact hx

/-- The positioning function, paradigm and second paradigm on the prepared set. -/
abbrev εY (u : Fin (2 + ((2 + A'.labels) + F.arity)) → RVInfinity M) : VF M → VF M := Dt.ε (sOf A' F u)
abbrev tY (u : Fin (2 + ((2 + A'.labels) + F.arity)) → RVInfinity M) : RV M := Dt.t (sOf A' F u)
abbrev t₁Y (u : Fin (2 + ((2 + A'.labels) + F.arity)) → RVInfinity M) : RVInfinity M := Dt.t₁ (sOf A' F u)

/-- The index of the RV point inside the labels of the prepared set, after
`m` leading coordinates. -/
def sIdx (m : ℕ) (j : Fin F.arity) : Fin (m + (2 + ((2 + A'.labels) + F.arity))) :=
  Fin.natAdd m (Fin.natAdd 2 (Fin.natAdd (2 + A'.labels) j))

theorem focusGraph_prepared :
    (T : Set M).Definable LRV {z : Fin (2 + (2 + ((2 + A'.labels) + F.arity))) → M | ∃ u x,
      (∃ y, (![x, y], u) ∈ (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D).carrier) ∧
      z = Fin.append ![x.val, (εY A' F Dt u x).val] (rvValues u)} := by
  let Y := prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  let q := 2 + ((2 + A'.labels) + F.arity)
  let P := rawMixedSpace (M := M) 2 q
  have hY : (T : Set M).Definable LRV (P.preimage Y.carrier) := Y.definable
  let f₁ : Fin (1 + q) → Fin 2 ⊕ Fin q := Fin.append (fun _ => Sum.inl 0) Sum.inr
  let g₁ : Fin (1 + q) → Fin (2 + q) := Fin.append (fun _ => Fin.castAdd q 0) (Fin.natAdd 2)
  let g₂ : Fin (2 + F.arity) → Fin (2 + q) := Fin.append (Fin.castAdd q) (sIdx A' F 2)
  have h := ((hY.image_comp f₁).preimage_comp g₁).inter (Dt.focusGraph.preimage_comp g₂)
  convert h using 1
  ext z
  constructor
  · rintro ⟨u, x, ⟨y, hxy⟩, rfl⟩
    obtain ⟨s, hs2, -, hcell⟩ := cell_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D u
      ⟨(x, y), hxy⟩
    refine ⟨⟨mixedValues ((![x, y], u) : Mixed M 2 q), ⟨mixedValues_mem_domain _, ?_⟩, ?_⟩, ?_⟩
    · rw [decode_mixedValues]; exact hxy
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [f₁, g₁, Function.comp_apply, Fin.append_left]
        rfl
      · simp only [f₁, g₁, Function.comp_apply, Fin.append_right]
        rfl
    · have hx : x ∈ first (cellAt F s) := by
        rw [← hcell]
        exact ⟨(x, y), hxy, rfl⟩
      refine ⟨s, x, hx, ?_⟩
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [g₂, Function.comp_apply, Fin.append_left]
        fin_cases j
        · rfl
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
          rw [hs2]
          rfl
      · simp only [g₂, Function.comp_apply, Fin.append_right, sIdx]
        rw [hs2]
        rfl
  · rintro ⟨⟨c, ⟨hc, hcY⟩, hcz⟩, ⟨s, a, ha, hz⟩⟩
    let p := P.decode ⟨c, hc⟩
    have hpc : mixedValues p = c := mixedValues_decode ⟨c, hc⟩
    have hz0 : z (Fin.castAdd q 0) = (p.1 0).val := by
      have h1 := congrFun hcz (Fin.castAdd q 0)
      simp only [f₁, g₁, Function.comp_apply, Fin.append_left] at h1
      rw [← h1, ← hpc]
      rfl
    have hzu : ∀ j, z (Fin.natAdd 2 j) = (p.2 j).val := by
      intro j
      have h1 := congrFun hcz (Fin.natAdd 1 j)
      simp only [f₁, g₁, Function.comp_apply, Fin.append_right] at h1
      rw [← h1, ← hpc]
      rfl
    have ha0 : a = p.1 0 := by
      apply Subtype.ext
      have h1 := congrFun hz (Fin.castAdd F.arity 0)
      simp only [g₂, Function.comp_apply, Fin.append_left] at h1
      rw [← hz0, h1]
      rfl
    have hsu : s.val.2 = sOf A' F p.2 := by
      funext j
      apply Subtype.ext
      have h1 := congrFun hz (Fin.natAdd 2 j)
      simp only [g₂, Function.comp_apply, Fin.append_right, sIdx] at h1
      rw [hzu] at h1
      exact h1.symm
    refine ⟨p.2, p.1 0, ⟨p.1 1, by rw [vec_two]; exact hcY⟩, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Fin.append_left, Matrix.cons_val_zero]
        exact hz0
      · have h1 := congrFun hz (Fin.castAdd F.arity 1)
        simp only [g₂, Function.comp_apply, Fin.append_left, Fin.mk_one, Fin.isValue, Matrix.cons_val_one] at h1 ⊢
        rw [h1, ha0, hsu]
    · simp only [Fin.append_right]
      exact hzu j

theorem paradigmGraph_prepared :
    (T : Set M).Definable LRV {z : Fin (1 + (2 + ((2 + A'.labels) + F.arity))) → M | ∃ u x,
      (∃ y, (![x, y], u) ∈ (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D).carrier) ∧
      z = Fin.append ![(tY A' F Dt u).val.val] (rvValues u)} := by
  let Y := prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  let q := 2 + ((2 + A'.labels) + F.arity)
  let P := rawMixedSpace (M := M) 2 q
  have hY : (T : Set M).Definable LRV (P.preimage Y.carrier) := Y.definable
  let g₃ : Fin (1 + F.arity) → Fin (1 + q) := Fin.append (Fin.castAdd q) (sIdx A' F 1)
  have h := ((hY.image_comp (Sum.inr : Fin q → Fin 2 ⊕ Fin q)).preimage_comp (Fin.natAdd 1)).inter
    (Dt.paradigmGraph.preimage_comp g₃)
  convert h using 1
  ext z
  constructor
  · rintro ⟨u, x, ⟨y, hxy⟩, rfl⟩
    obtain ⟨s, hs2, -, -⟩ := cell_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D u ⟨(x, y), hxy⟩
    refine ⟨⟨mixedValues ((![x, y], u) : Mixed M 2 q), ⟨mixedValues_mem_domain _, ?_⟩, ?_⟩, ⟨s, ?_⟩⟩
    · rw [decode_mixedValues]; exact hxy
    · funext j
      simp only [Function.comp_apply, Fin.append_right]
      rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [g₃, Function.comp_apply, Fin.append_left]
        rw [Fin.fin_one_eq_zero j, hs2]
        rfl
      · simp only [g₃, Function.comp_apply, Fin.append_right, sIdx]
        rw [hs2]
        rfl
  · rintro ⟨⟨c, ⟨hc, hcY⟩, hcz⟩, ⟨s, hz⟩⟩
    let p := P.decode ⟨c, hc⟩
    have hpc : mixedValues p = c := mixedValues_decode ⟨c, hc⟩
    have hzu : ∀ j, z (Fin.natAdd 1 j) = (p.2 j).val := by
      intro j
      have h1 := congrFun hcz j
      simp only [Function.comp_apply] at h1
      rw [← h1, ← hpc]
      rfl
    have hsu : s.val.2 = sOf A' F p.2 := by
      funext j
      apply Subtype.ext
      have h1 := congrFun hz (Fin.natAdd 1 j)
      simp only [g₃, Function.comp_apply, Fin.append_right, sIdx] at h1
      rw [hzu] at h1
      exact h1.symm
    refine ⟨p.2, p.1 0, ⟨p.1 1, by rw [vec_two]; exact hcY⟩, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have h1 := congrFun hz (Fin.castAdd F.arity j)
      simp only [g₃, Function.comp_apply, Fin.append_left] at h1 ⊢
      rw [h1, hsu]
    · simp only [Fin.append_right]
      exact hzu j

theorem secondGraph_prepared :
    (T : Set M).Definable LRV {z : Fin (1 + (2 + ((2 + A'.labels) + F.arity))) → M | ∃ u x,
      (∃ y, (![x, y], u) ∈ (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D).carrier) ∧
      z = Fin.append ![(t₁Y A' F Dt u).val] (rvValues u)} := by
  let Y := prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  let q := 2 + ((2 + A'.labels) + F.arity)
  let P := rawMixedSpace (M := M) 2 q
  have hY : (T : Set M).Definable LRV (P.preimage Y.carrier) := Y.definable
  let g₃ : Fin (1 + F.arity) → Fin (1 + q) := Fin.append (Fin.castAdd q) (sIdx A' F 1)
  have h := ((hY.image_comp (Sum.inr : Fin q → Fin 2 ⊕ Fin q)).preimage_comp (Fin.natAdd 1)).inter
    (Dt.secondGraph.preimage_comp g₃)
  convert h using 1
  ext z
  constructor
  · rintro ⟨u, x, ⟨y, hxy⟩, rfl⟩
    obtain ⟨s, hs2, hk, -⟩ := cell_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D u ⟨(x, y), hxy⟩
    refine ⟨⟨mixedValues ((![x, y], u) : Mixed M 2 q), ⟨mixedValues_mem_domain _, ?_⟩, ?_⟩, ⟨s, hk, ?_⟩⟩
    · rw [decode_mixedValues]; exact hxy
    · funext j
      simp only [Function.comp_apply, Fin.append_right]
      rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [g₃, Function.comp_apply, Fin.append_left]
        rw [Fin.fin_one_eq_zero j, hs2]
        rfl
      · simp only [g₃, Function.comp_apply, Fin.append_right, sIdx]
        rw [hs2]
        rfl
  · rintro ⟨⟨c, ⟨hc, hcY⟩, hcz⟩, ⟨s, -, hz⟩⟩
    let p := P.decode ⟨c, hc⟩
    have hpc : mixedValues p = c := mixedValues_decode ⟨c, hc⟩
    have hzu : ∀ j, z (Fin.natAdd 1 j) = (p.2 j).val := by
      intro j
      have h1 := congrFun hcz j
      simp only [Function.comp_apply] at h1
      rw [← h1, ← hpc]
      rfl
    have hsu : s.val.2 = sOf A' F p.2 := by
      funext j
      apply Subtype.ext
      have h1 := congrFun hz (Fin.natAdd 1 j)
      simp only [g₃, Function.comp_apply, Fin.append_right, sIdx] at h1
      rw [hzu] at h1
      exact h1.symm
    refine ⟨p.2, p.1 0, ⟨p.1 1, by rw [vec_two]; exact hcY⟩, ?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have h1 := congrFun hz (Fin.castAdd F.arity j)
      simp only [g₃, Function.comp_apply, Fin.append_left] at h1 ⊢
      rw [h1, hsu]
    · simp only [Fin.append_right]
      exact hzu j

/-- **The balanced piece, prepared, is input of the balanced translation.** -/
theorem preparedInput :
    BalancedShearInput (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D) (εY A' F Dt) (tY A' F Dt)
      (t₁Y A' F Dt) where
  proper := reindexedVFSet_properInvariant _ e (D.image_properInvariant h00 hc hκ hs hv)
  doublyBounded := reindexedVFSet_doublyBounded _ e D.image_vfDoublyBounded
  tagged := by
    intro p hp p' hp' he
    have hc₀ : (p.1 0, p.1 1) ∈ cell (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D) p.2 :=
      (mem_cell_iff p.1).mpr hp
    have hc₁ : (p'.1 0, p'.1 1) ∈ cell (prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D) p.2 := by
      rw [he]; exact (mem_cell_iff p'.1).mpr hp'
    obtain ⟨s, -, -, hcell⟩ := cell_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D p.2 ⟨_, hc₀⟩
    rw [hcell] at hc₀ hc₁
    obtain ⟨⟨u₁, u₂, hpoly⟩, -⟩ := Dt.cells s
    funext i
    change rv M (p.1 i) = rv M (p'.1 i)
    fin_cases i
    · exact ((hpoly _ hc₀).1).trans ((hpoly _ hc₁).1).symm
    · exact ((hpoly _ hc₀).2).trans ((hpoly _ hc₁).2).symm
  focusGraph := focusGraph_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  paradigmGraph := paradigmGraph_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D
  balanced := by
    intro u hne
    obtain ⟨s, hs2, hk, hcell⟩ := cell_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D u hne
    rw [hcell]
    have hb := (Dt.cells s).2.2.2.2.2 hk
    rw [hs2] at hb
    exact hb
  genuine := by
    intro u p hp
    obtain ⟨s, hs2, hk, hcell⟩ := cell_prepared h00 hc linear hκ hs hv hsmall hΓ A' hω F Dt D u ⟨p, hp⟩
    rw [hcell] at hp
    obtain ⟨⟨u₁, u₂, hpoly⟩, -⟩ := Dt.cells s
    have hb := (Dt.cells s).2.2.2.2.2 hk
    have hfirst : p.1 ∈ first (cellAt F s) := ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hq2⟩ := hb.bijective.mapsTo hfirst
    change rv M (Dt.ε (sOf A' F u) p.1) = rv M p.2
    rw [← hs2, ← hq2]
    exact ((hpoly q hq).2).trans ((hpoly p hp).2).symm

end DiamondIntegral.Section7.BalancedKinds
