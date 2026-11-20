import «section 7».SliceContractions

/-! Covariance of the form on the first-stage set (for Proposition 7.24).

Let `G₀` be a normalized contraction of an object `A` of `μVF^◇[n + 2]`, with
first stage `H` on the prepared set `Y`. The first-stage set `firstSet G₀` carries
the induced form `firstForm G₀`: the prepared form read through the contraction of
`H`. It is not an object of `μVF^◇[n + 1]` (its RV fibres are finite only modulo
the leading label), but its form is covariant (`firstForm_covariant`):

* a point `(z, t)` of the first-stage set lifts to the prepared point
  `y = H.lift⁻¹ (z, x, t)` for any `x` with `rv(x) = t_lead`. `y` has VF coordinates
  `(z, y_last)` (the lift fixes the other coordinates) and labels `t ∘ oldLabels`
  (the old labels are retained);
* for `z'` close to `z`, the point `y' = (z', y_last)` with the same labels is again
  prepared (invariance of `Y`), has the same prepared form (covariance of the
  prepared form, `SliceContractions.prepared_covariant`), and its lift has labels
  `t` (invariance of the graph fibres of `H.lift`), so `y'` lies over `(z', t)`.

The three radii are named over the labels `t`, since the source labels are among
them. The label slices of the first-stage set are the objects of the fibres in
the proof of `(∗)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FirstStageObjects
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.ContractionChoice
open DiamondIntegral.Section7.SliceContractions

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### Radii -/

section Radii

/-- The componentwise larger of two radii (one of the two, so it stays named). -/
def maxRadii {k : ℕ} (a b : Fin k → Gamma M) : Fin k → Gamma M := fun j => if a j ≤ b j then b j else a j

theorem maxRadii_named {S : Set M} {m k : ℕ} {t : Fin m → RVInfinity M} {a b : Fin k → Gamma M}
    (ha : NamedRadii S t a) (hb : NamedRadii S t b) : NamedRadii S t (maxRadii a b) := fun j => by
  unfold maxRadii
  split_ifs
  · exact hb j
  · exact ha j

theorem le_maxRadii_left {k : ℕ} (a b : Fin k → Gamma M) (j : Fin k) : (a j).val ≤ (maxRadii a b j).val := by
  unfold maxRadii
  split_ifs with h
  · exact h
  · exact le_rfl

theorem le_maxRadii_right {k : ℕ} (a b : Fin k → Gamma M) (j : Fin k) : (b j).val ≤ (maxRadii a b j).val := by
  unfold maxRadii
  split_ifs with h
  · exact le_rfl
  · exact (le_of_lt (lt_of_not_ge h))

theorem congruent_mono {k : ℕ} {a b : Fin k → Gamma M} (h : ∀ j, (a j).val ≤ (b j).val) {x y : Fin k → VF M}
    (hxy : Congruent b x y) : Congruent a x y := fun j => lt_of_le_of_lt (h j) (hxy j)

theorem congruent_snoc {n : ℕ} {α : Fin (n + 1) → Gamma M} {β : Fin n → Gamma M}
    (h : ∀ j, (α j.castSucc).val ≤ (β j).val) {z z' : Fin n → VF M} (hzz : Congruent β z z') (w : VF M) :
    Congruent α (Fin.snoc z w) (Fin.snoc z' w) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, sub_self]
    exact gamma_lt_value_zero (α (Fin.last n))
  · simp only [Fin.snoc_castSucc]
    exact lt_of_le_of_lt (h j) (hzz j)

end Radii

/-! ### Graph fibres -/

omit [M ⊨ Axioms.ACVF] in
theorem graphFibre_iff {S : Set M} {n m r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) m s) S} (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a : Fin n → VF M) (b : Fin m → VF M) :
    graphFibre f u v a b ↔ ∃ h : ((a, u) : Mixed M n r) ∈ A.carrier, (f ⟨(a, u), h⟩).val = (b, v) := by
  constructor
  · rintro ⟨p, hp, hfp⟩
    have hpu : p = ⟨(a, u), hp ▸ p.property⟩ := Subtype.ext hp
    refine ⟨hp ▸ p.property, ?_⟩
    rw [← hpu]
    exact hfp
  · rintro ⟨h, he⟩
    exact ⟨⟨(a, u), h⟩, rfl, he⟩

/-! ### Covariance of the first-stage form -/

section Covariance
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1)} {e : Equiv.Perm (Fin (n + 1 + 1))}
variable (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)

include h00 hc hκ hs hv in
/-- **The first-stage form is covariant**, with radii named over the labels. -/
theorem firstForm_covariant (t : Fin (stage G₀).arity → RVInfinity M) :
    ∃ β : Fin (n + 1) → Gamma M, NamedRadii (T : Set M) t β ∧
      ∀ (z z' : Fin (n + 1) → VF M) (hz : ((z, t) : Mixed M _ _) ∈ (firstSet G₀).carrier)
        (hz' : ((z', t) : Mixed M _ _) ∈ (firstSet G₀).carrier),
        Congruent β z z' → gammaMapValue (firstForm G₀) ⟨_, hz⟩ = gammaMapValue (firstForm G₀) ⟨_, hz'⟩ := by
  let H := stage G₀
  let v : Fin ((n + 1 + 1) + A.labels) → RVInfinity M := t ∘ H.oldLabels
  obtain ⟨αY, hαY, hInvY⟩ := (Corollary715Fibres.prepProper hc h00 hκ hs hv G₀).radii v
  obtain ⟨αP, hαP, hcovP⟩ := prepared_covariant h00 G₀ v
  obtain ⟨αF, -, hαF, -, hInvF, -, -⟩ := H.home.covariant.radii v t
  have hsubv : (T : Set M) ∪ Set.range (rvValues v) ⊆ (T : Set M) ∪ Set.range (rvValues t) := by
    rintro x (hx | ⟨i, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨H.oldLabels i, rfl⟩
  have hsubF : graphFibreBase (T : Set M) v t ⊆ (T : Set M) ∪ Set.range (rvValues t) := by
    rintro x ((hx | hx) | hx)
    · exact Or.inl hx
    · exact hsubv (Or.inr hx)
    · exact Or.inr hx
  let aY : Fin (n + 1) → Gamma M := fun j => αY j.castSucc
  let aP : Fin (n + 1) → Gamma M := fun j => αP j.castSucc
  let aF : Fin (n + 1) → Gamma M := fun j => αF j.castSucc
  have hnY : NamedRadii (T : Set M) t aY := fun j => (hαY j.castSucc).mono hsubv
  have hnP : NamedRadii (T : Set M) t aP := fun j => (hαP j.castSucc).mono hsubv
  have hnF : NamedRadii (T : Set M) t aF := fun j => (hαF j.castSucc).mono hsubF
  let β := maxRadii aY (maxRadii aP aF)
  have hβY : ∀ j, (αY j.castSucc).val ≤ (β j).val := fun j => le_maxRadii_left aY _ j
  have hβP : ∀ j, (αP j.castSucc).val ≤ (β j).val := fun j =>
    (le_maxRadii_left aP aF j).trans (le_maxRadii_right aY _ j)
  have hβF : ∀ j, (αF j.castSucc).val ≤ (β j).val := fun j =>
    (le_maxRadii_right aP aF j).trans (le_maxRadii_right aY _ j)
  refine ⟨β, maxRadii_named hnY (maxRadii_named hnP hnF), fun z z' hz hz' hzz => ?_⟩
  -- a prepared point over `(z, t)`
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun _ : Fin 1 => t H.leading)
  have htg : ((Fin.snoc z (x 0), t) : Mixed M (n + 1 + 1) H.arity) ∈ H.target.carrier := by
    refine (H.recover_target _).mpr ⟨?_, ?_⟩
    · simpa only [Fin.init_snoc] using hz
    · exact (congrArg (rv M) (Fin.snoc_last (α := fun _ => VF M) _ _)).trans (congrFun hx 0)
  obtain ⟨y, hy⟩ := H.home.bijective.surjective ⟨_, htg⟩
  have hyval : (H.lift y).val = ((Fin.snoc z (x 0), t) : Mixed M _ _) := congrArg Subtype.val hy
  have hy1 : ∀ j : Fin (n + 1), y.val.1 j.castSucc = z j := fun j => by
    rw [← H.relative y j, hyval]
    exact Fin.snoc_castSucc (α := fun _ => VF M) _ _ j
  have hy2 : y.val.2 = v := funext fun i => by
    rw [← H.retained y i, hyval]
    rfl
  let w : VF M := y.val.1 (Fin.last (n + 1))
  have hyeq : y.val = ((Fin.snoc z w, v) : Mixed M _ _) := by
    refine Prod.ext ?_ hy2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (Fin.snoc_last (α := fun _ => VF M) _ _).symm
    · exact (hy1 j).trans (Fin.snoc_castSucc (α := fun _ => VF M) _ _ j).symm
  have hyY : ((Fin.snoc z w, v) : Mixed M _ _) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier := by
    rw [← hyeq]
    exact y.property
  have hcong (α : Fin (n + 1 + 1) → Gamma M) (hα : ∀ j, (α j.castSucc).val ≤ (β j).val) :
      Congruent α (Fin.snoc z w) (Fin.snoc z' w) := congruent_snoc hα hzz w
  have hyY' : ((Fin.snoc z' w, v) : Mixed M _ _) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier :=
    (hInvY _ _ (hcong αY hβY)).mp hyY
  -- the prepared forms agree
  have hP := hcovP _ _ hyY hyY' (hcong αP hβP)
  -- the companion point lies over `(z', t)`
  have hsrc : Fin.snoc z w ∈ graphFibreSource H.lift v t := by
    refine ⟨Fin.snoc z (x 0), (graphFibre_iff H.lift v t _ _).mpr ⟨hyY, ?_⟩⟩
    have : (⟨((Fin.snoc z w, v) : Mixed M _ _), hyY⟩ : reindexedVFSet G₀.normalization.map.image e) = y := Subtype.ext hyeq.symm
    rw [this, hyval]
  obtain ⟨x', hx'⟩ := (hInvF _ _ (hcong αF hβF)).mp hsrc
  obtain ⟨hyY'', hlift'⟩ := (graphFibre_iff H.lift v t _ _).mp hx'
  let y' : reindexedVFSet G₀.normalization.map.image e := ⟨_, hyY'⟩
  have hc' : (H.contraction y').val = ((z', t) : Mixed M _ _) := by
    rw [StandardContractionStage.contraction_value]
    change (Fin.init (H.lift ⟨_, hyY''⟩).val.1, (H.lift ⟨_, hyY''⟩).val.2) = _
    rw [hlift']
    refine Prod.ext ?_ rfl
    funext j
    change x' j.castSucc = z' j
    have hrel := H.relative ⟨_, hyY''⟩ j
    rw [hlift'] at hrel
    rw [show x' j.castSucc = (x', t).1 j.castSucc from rfl, hrel]
    exact Fin.snoc_castSucc (α := fun _ => VF M) _ _ j
  have hc0 : (H.contraction y).val = ((z, t) : Mixed M _ _) := by
    rw [StandardContractionStage.contraction_value, hyval]
    exact Prod.ext (Fin.init_snoc (α := fun _ => VF M) _ _) rfl
  have e1 : gammaMapValue (firstForm G₀) ⟨_, hz⟩ = gammaMapValue G₀.preparedForm y := by
    unfold gammaMapValue
    rw [show (⟨((z, t) : Mixed M _ _), hz⟩ : firstSet G₀) = H.contraction y from Subtype.ext hc0.symm]
    exact restForm_contraction G₀.preparedContraction.data y
  have e2 : gammaMapValue (firstForm G₀) ⟨_, hz'⟩ = gammaMapValue G₀.preparedForm y' := by
    unfold gammaMapValue
    rw [show (⟨((z', t) : Mixed M _ _), hz'⟩ : firstSet G₀) = H.contraction y' from Subtype.ext hc'.symm]
    exact restForm_contraction G₀.preparedContraction.data y'
  rw [e1, e2]
  rw [show y = ⟨_, hyY⟩ from Subtype.ext hyeq]
  exact hP

end Covariance

end DiamondIntegral.Section7.FirstStageObjects
