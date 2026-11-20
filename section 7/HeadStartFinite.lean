import «section 7».HeadStartK

/-! Finite RV fibres modulo head-start labels (for Lemma 7.23 with `n > 2`).

The first-stage set of a standard contraction does not have finite RV fibres
over VF points: the leading label varies with the contracted coordinate. It has
finite fibres modulo the leading label (`ContractionChoice.firstStage_finite`).
For a second stage, finiteness is needed modulo the labels carried from the first
stage together with the new leading label (`restLabels`).

* `finite_mod_of_bijective`: a definable bijection that carries labels `π` of the
  source to labels `ρ` of the target transports finite fibres modulo `π` to
  finite fibres modulo `ρ`. Proof: restrict to the label slices `u ∘ π = t` over
  the base enlarged by the coordinates of `t`, and apply Section 6
  `finite_rv_fibers_of_bijective` (Lemma 4.13: RV fibre dimension is preserved).
* `restLabels_finite`: if a set has finite fibres modulo `π`, the first-stage set
  of any normalized contraction of it has finite fibres modulo `restLabels F π`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.HeadStartFinite
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.ContractionChoice

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The label slice `{p | p.2 ∘ π = t}` is definable over the coordinates of `t`. -/
theorem labelSlice_definable {S : Set M} {n r k : ℕ} (π : Fin k → Fin r) (t : Fin k → RVInfinity M) :
    (rawMixedSpace (M := M) n r).Definable (S ∪ Set.range (rvValues t)) {p | ∀ i, p.2 (π i) = t i} := by
  have hR : (S ∪ Set.range (rvValues t)).Definable LRV
      (⋂ i, {z : Fin n ⊕ Fin r → M | z (.inr (π i)) = (t i).val}) :=
    Set.definable_iInter_of_finite fun i =>
      (Set.DefinableFun.proj LRV).ofPred_eq (LRV.definableFun_const _ (Or.inr ⟨i, rfl⟩))
  have h := mixedValues_preimage_definable (M := M) (n := n) (r := r) _ hR
  convert h using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hp i
    change (p.2 (π i)).val = (t i).val
    rw [hp i]
  · intro hp i
    have h' : (p.2 (π i)).val = (t i).val := hp i
    exact Subtype.ext h'

/-- The restriction of a set to a label slice, over the enlarged base. -/
def labelSlice {S : Set M} {n r k : ℕ} (Y : DefSet (rawMixedSpace (M := M) n r) S) (π : Fin k → Fin r)
    (t : Fin k → RVInfinity M) : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range (rvValues t)) :=
  ⟨{p | p ∈ Y.carrier ∧ ∀ i, p.2 (π i) = t i},
    Space.Definable.inter (rawMixedSpace (M := M) n r)
      (Space.Definable.mono (rawMixedSpace (M := M) n r) Y.definable Set.subset_union_left)
      (labelSlice_definable π t)⟩

theorem mem_labelSlice {S : Set M} {n r k : ℕ} (Y : DefSet (rawMixedSpace (M := M) n r) S) (π : Fin k → Fin r)
    (t : Fin k → RVInfinity M) (p : Mixed M n r) :
    p ∈ (labelSlice Y π t).carrier ↔ p ∈ Y.carrier ∧ ∀ i, p.2 (π i) = t i := Iff.rfl

/-- **Finite fibres modulo labels, along a bijection.** -/
theorem finite_mod_of_bijective (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n m r s k : ℕ} {Y : DefSet (rawMixedSpace (M := M) n r) S} {Z : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map Y Z) (hf : Function.Bijective f) (π : Fin k → Fin r) (ρ : Fin k → Fin s)
    (hret : ∀ p : Y, ∀ i, (f p).val.2 (ρ i) = p.val.2 (π i))
    (hY : ∀ (a : Fin n → VF M) (t : Fin k → RVInfinity M), {u | (a, u) ∈ Y.carrier ∧ u ∘ π = t}.Finite) :
    ∀ (b : Fin m → VF M) (t : Fin k → RVInfinity M), {v | (b, v) ∈ Z.carrier ∧ v ∘ ρ = t}.Finite := by
  intro b t
  let S' := S ∪ Set.range (rvValues t)
  have hsmall' : Cardinal.mk S' < κ :=
    (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hsmall
      ((Set.finite_range _).lt_aleph0.trans_le hκ.le))
  let Yt := labelSlice Y π t
  let Zt := labelSlice Z ρ t
  have hYt : ∀ p : Yt, p.val ∈ Y.carrier ∧ ∀ i, p.val.2 (π i) = t i := fun p =>
    (mem_labelSlice Y π t p.val).mp p.property
  have hZt : ∀ z : Zt, z.val ∈ Z.carrier ∧ ∀ i, z.val.2 (ρ i) = t i := fun z =>
    (mem_labelSlice Z ρ t z.val).mp z.property
  have hmem : ∀ p : Yt, (f ⟨p.val, (hYt p).1⟩).val ∈ Zt.carrier := fun p =>
    (mem_labelSlice Z ρ t _).mpr ⟨(f ⟨p.val, (hYt p).1⟩).property, fun i => (hret _ i).trans ((hYt p).2 i)⟩
  have hsub : Yt.carrier ⊆ Y.carrier := fun q hq => ((mem_labelSlice Y π t q).mp hq).1
  let ft : Map Yt Zt := ((extendMapBase (Set.subset_union_left : S ⊆ S') f).comp
    (Map.inclusion hsub)).corestrict hmem
  have hft : Function.Bijective ft := by
    refine ⟨fun x y he => ?_, fun z => ?_⟩
    · have h1 : (f ⟨x.val, (hYt x).1⟩).val = (f ⟨y.val, (hYt y).1⟩).val := by
        have := congrArg Subtype.val he
        exact this
      have h2 := hf.1 (Subtype.ext h1)
      apply Subtype.ext
      have := congrArg Subtype.val h2
      exact this
    · obtain ⟨p, hp⟩ := hf.2 ⟨z.val, (hZt z).1⟩
      have hpt : ∀ i, p.val.2 (π i) = t i := fun i => by
        rw [← hret p i, hp]
        exact (hZt z).2 i
      refine ⟨⟨p.val, (mem_labelSlice Y π t _).mpr ⟨p.property, hpt⟩⟩, Subtype.ext ?_⟩
      have := congrArg Subtype.val hp
      exact this
  have hYfin : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ Yt.carrier}.Finite := by
    intro a
    refine (hY a t).subset ?_
    intro u hu
    obtain ⟨hu1, ht⟩ := (mem_labelSlice Y π t _).mp hu
    exact ⟨hu1, funext ht⟩
  refine (finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall' ft hft hYfin b).subset ?_
  rintro v ⟨hv, hvt⟩
  exact (mem_labelSlice Z ρ t _).mpr ⟨hv, fun i => congrFun hvt i⟩

section Rest
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ)
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1))}

include hc h00 hκ hs hsmall in
/-- **Finite fibres of the first-stage set modulo the rest labels.** -/
theorem restLabels_finite (F : NormalizedMeasuredContraction (G := G) A ω e) {k : ℕ} (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∀ (b : Fin n → VF M) (t : Fin (k + 1) → RVInfinity M),
      {u | (b, u) ∈ (headStage F.preparedContraction.data.program).contracted.carrier ∧
        u ∘ restLabels F π = t}.Finite := by
  let H := headStage F.preparedContraction.data.program
  let D := F.normalization
  let prep : Map A (reindexedVFSet D.map.image e) := (vfRelabeling D.map.image e).comp D.bijection
  have hprep : Function.Bijective prep := (vfRelabeling_bijective _ e).comp (D.bijective h00)
  have hret₁ : ∀ p : A, ∀ i, (prep p).val.2 (Fin.natAdd (n + 1) (π i)) = p.val.2 (π i) := by
    intro p i
    change Fin.append (fun j => branchTag (M := M) (D.core p.val j)) p.val.2 (Fin.natAdd (n + 1) (π i)) = _
    rw [Fin.append_right]
  have hP := finite_mod_of_bijective hc h00 hκ hs hsmall prep hprep π (fun i => Fin.natAdd (n + 1) (π i)) hret₁ hFin
  have hT := finite_mod_of_bijective hc h00 hκ hs hsmall H.lift H.home.bijective (fun i => Fin.natAdd (n + 1) (π i))
    (fun i => H.oldLabels (Fin.natAdd (n + 1) (π i))) (fun p i => H.retained p _) hP
  intro b t
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun _ : Fin 1 => t (Fin.last k))
  refine (hT (Fin.snoc b (x 0)) (fun i => t i.castSucc)).subset ?_
  rintro u ⟨hu, ht⟩
  have hlead : u H.leading = t (Fin.last k) := by
    have := congrFun ht (Fin.last k)
    simpa only [Function.comp_apply, restLabels, Fin.snoc_last] using this
  have hold : ∀ i, u (H.oldLabels (Fin.natAdd (n + 1) (π i))) = t i.castSucc := by
    intro i
    have := congrFun ht i.castSucc
    simpa only [Function.comp_apply, restLabels, Fin.snoc_castSucc] using this
  refine ⟨?_, funext hold⟩
  apply (H.recover_target (Fin.snoc b (x 0), u)).mpr
  refine ⟨by simpa only [Fin.init_snoc] using hu, ?_⟩
  change rv M (Fin.snoc (α := fun _ => VF M) b (x 0) (Fin.last n)) = u H.leading
  rw [Fin.snoc_last, hlead]
  exact congrFun hx 0

end Rest

end DiamondIntegral.Section7.HeadStartFinite
