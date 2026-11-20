import «section 7».OrderIndependence

/-! The tautological contraction of a lift (for Proposition 7.24).

The paper: "Since `μL U` is an RV-pullback, its tautological contraction, which
recovers `U`, is a standard contraction with respect to any order."

Let `U` be a doubly bounded measured RV object of `μRV[n + 1]` with labels
`w ∈ RV^r` and values `val(w) ∈ RV^{n+1}`, and let
`L = rvLift U = {(x, w) | w ∈ U, rv(x) = val(w)}` be its lift.

* **Stages.** The first stage is the regularization `(x, w) ↦ (x, rv(x) ++ w)`
  (`regStage`). On `L` its new labels `rv(x) = val(w)` depend only on the old
  labels, so it is a label map: a proper covariant homeomorphism with unit
  derivative everywhere (`ProgramContractions.labelMap_home`, `labelMap_unit`).
  On the regularized set every VF coordinate is an RV-pullback along a label,
  `rv(x_i) = label (castAdd r i)` (`described_reg`), so every later stage is an
  identity stage (`idStageG`, `idProgram`). The RV target is the set of the
  regularized labels `regTarget`, the volume labels are `castAdd r`
  (`liftProgram_volumeIndex`) and the old labels `natAdd (n + 1)`
  (`liftProgram_oldLabels`). The RV form is the form of `U` read on the old
  labels (`liftRVForm`, by descent along the surjective program map).
* **The class.** The head-start-`0` object of this contraction is isomorphic to
  `U` through `u ↦ u ∘ natAdd (n + 1)` (`cls_liftMOC`), so the normalized
  contraction `tautLift` of `(L, ω)` in the identity order
  (`OrderedProgramContractions.ofContractionOrd`; `L` has no zero coordinate)
  has the class of `U` (`clsOf_tautLift`, `exists_taut_contraction`): equality,
  not only `μIsp^db`.
* **Any order.** With the independence of the contraction and its order
  (`OrderIndependence.star`), every standard contraction of `L` in any order has
  a class `μIsp^db`-related to the class of `U` (`ispRel_lift`), and for a chart
  `a` and the lift of its Section 6 object (the object of `liftCls_cls`), to the
  class of `a` (`ispRel_chart`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.TautologicalLifts
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ProgramContractions DiamondIntegral.Section7.OrderedProgramContractions
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section6.DiamondStandardContraction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Selecting RV coordinates -/

section Select
variable {S : Set M} {q r : ℕ}

/-- The definable map `u ↦ u ∘ ι` on RV tuples. -/
def rvSelectMap (A : DefSet (rawRVSpace (M := M) q) S) (ι : Fin r → Fin q) :
    Map A (DefSet.univ (rawRVSpace (M := M) r) S) := by
  let F (z : Fin q → M) : Fin r → M := z ∘ ι
  have hcode (c : (rawRVSpace (M := M) q).domain) :
      rvValues (((rawRVSpace (M := M) q).decode c) ∘ ι) = F c.val := by
    funext i
    exact congrFun (SpecialTransformations.Section4.rvValues_decode c) (ι i)
  refine Map.ofCodes A (fun t => t ∘ ι) F (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨((rawRVSpace (M := M) q).decode c) ∘ ι, hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (SpecialTransformations.Section4.rvValues_decode _).trans (hcode c).symm

omit [M ⊨ Axioms.ACVF] in
theorem rvSelectMap_val (A : DefSet (rawRVSpace (M := M) q) S) (ι : Fin r → Fin q) (u : A) :
    (rvSelectMap A ι u).val = u.val ∘ ι := rfl

end Select

/-! ### Sets described by an RV target and volume labels -/

section Described
variable {S : Set M} {q : ℕ}

/-- `Z` is the set of points over `W` whose VF coordinates have the residues
read at the labels `ν`: the form of `OrderedStandardContractionLift.recover`. -/
def Described (W : DefSet (rawMixedSpace (M := M) 0 q) S) {m : ℕ} (ν : Fin m → Fin q)
    (Z : DefSet (rawMixedSpace (M := M) m q) S) : Prop :=
  ∀ p : Mixed M m q, p ∈ Z.carrier ↔ (Fin.elim0, p.2) ∈ W.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (ν i)

variable {W : DefSet (rawMixedSpace (M := M) 0 q) S}

/-- Dropping the last VF coordinate of a described set. -/
theorem described_drop {m : ℕ} {ν : Fin (m + 1) → Fin q} {Z : DefSet (rawMixedSpace (M := M) (m + 1) q) S}
    (hZ : Described W ν Z) : Described W (fun i => ν i.castSucc) (vfDropLast Z).image := by
  intro p
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hW, hrv⟩ := (hZ z.val).mp z.property
    have h1 : Fin.init z.val.1 = p.1 := congrArg Prod.fst hz
    have h2 : z.val.2 = p.2 := congrArg Prod.snd hz
    refine ⟨h2 ▸ hW, fun i => ?_⟩
    rw [← h1, ← h2]
    exact hrv i.castSucc
  · rintro ⟨hW, hrv⟩
    obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun _ : Fin 1 => p.2 (ν (Fin.last m)))
    have hmem : ((Fin.snoc p.1 (x 0), p.2) : Mixed M (m + 1) q) ∈ Z.carrier := by
      refine (hZ _).mpr ⟨hW, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact congrFun hx 0
      · simp only [Fin.snoc_castSucc]
        exact hrv j
    refine ⟨⟨_, hmem⟩, Prod.ext ?_ rfl⟩
    exact Fin.init_snoc (α := fun _ => VF M) (x 0) p.1

/-- A described set is the RV-disc bundle over its drop, along the label of its
last coordinate. -/
theorem described_bundle {m : ℕ} {ν : Fin (m + 1) → Fin q} {Z : DefSet (rawMixedSpace (M := M) (m + 1) q) S}
    (hZ : Described W ν Z) :
    Z.carrier = (rvCoordinateBundle (vfDropLast Z).image (ν (Fin.last m))).carrier := by
  ext p
  change p ∈ Z.carrier ↔ (Fin.init p.1, p.2) ∈ (vfDropLast Z).image.carrier ∧
    rv M (p.1 (Fin.last m)) = p.2 (ν (Fin.last m))
  rw [hZ p, described_drop hZ]
  constructor
  · rintro ⟨hW, hrv⟩
    exact ⟨⟨hW, fun i => hrv i.castSucc⟩, hrv (Fin.last m)⟩
  · rintro ⟨⟨hW, hrv⟩, hl⟩
    refine ⟨hW, fun i => ?_⟩
    refine Fin.lastCases hl (fun j => ?_) i
    exact hrv j

theorem described_zero {ν : Fin 0 → Fin q} {Z : DefSet (rawMixedSpace (M := M) 0 q) S}
    (hZ : Described W ν Z) : Z.carrier = W.carrier := by
  ext p
  rw [hZ p]
  have he : ((Fin.elim0, p.2) : Mixed M 0 q) = p := Prod.ext (Subsingleton.elim _ _) rfl
  rw [he]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩

theorem drop_doublyBounded {m r : ℕ} {Z : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
    (hD : VFDoublyBounded Z.carrier) : VFDoublyBounded (vfDropLast Z).image.carrier := by
  obtain ⟨δ, hδ⟩ := hD
  refine ⟨δ, ?_⟩
  rintro _ ⟨p, rfl⟩ i
  exact hδ p.val p.property i.castSucc

end Described

/-! ### Identity programs of described sets -/

section IdProgram
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {q : ℕ}

/-- **The identity stage** of a proper, VF-doubly bounded RV-disc bundle. -/
def idStageG {m : ℕ} (Z : DefSet (rawMixedSpace (M := M) (m + 1) q) S) (hP : ProperInvariant S Z.carrier)
    (hD : VFDoublyBounded Z.carrier) (ℓ : Fin q)
    (hB : Z.carrier = (rvCoordinateBundle (vfDropLast Z).image ℓ).carrier) :
    StandardContractionStage (G := G) Z where
  arity := q
  target := Z
  lift := Map.id Z
  home := identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ hP
  proper := hP
  doublyBounded := hD
  relative := fun _ _ => rfl
  oldLabels := id
  oldLabels_injective := Function.injective_id
  retained := fun _ _ => rfl
  leading := ℓ
  bundle := hB
  exceptional := DefSet.empty _ S
  exceptional_subset := fun _ hp => hp.elim
  exceptional_dim := DiamondIntegral.Section6.DiamondLift.vfDim_empty_lt (Fin.last m)
  unitDerivative := fun p _ => identity_unit_derivative hP p

variable (W : DefSet (rawMixedSpace (M := M) 0 q) S)

/-- **The identity program** of a described set: one identity stage per VF
coordinate, ending on the RV target `W`. -/
def idProgram : (m : ℕ) → (ν : Fin m → Fin q) → (Z : DefSet (rawMixedSpace (M := M) m q) S) →
    Described W ν Z → ProperInvariant S Z.carrier → VFDoublyBounded Z.carrier →
    OrderedStandardContractionProgram (G := G) S Z W
  | 0, _, _, hZ, _, _ => programOn (OrderedStandardContractionProgram.zero W) (defSet_eq_of_carrier_eq (described_zero hZ))
  | m + 1, ν, Z, hZ, hP, hD =>
    .step (idStageG h00 hc linear hκ hs hv hsmall hΓ Z hP hD (ν (Fin.last m)) (described_bundle hZ))
      (idProgram m (fun i => ν i.castSucc) (vfDropLast Z).image (described_drop hZ)
        (vfDropLast_image_properInvariant hP) (drop_doublyBounded hD))

theorem idProgram_oldLabels : ∀ (m : ℕ) (ν : Fin m → Fin q) (Z : DefSet (rawMixedSpace (M := M) m q) S)
    (hZ : Described W ν Z) (hP : ProperInvariant S Z.carrier) (hD : VFDoublyBounded Z.carrier),
    (idProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ W m ν Z hZ hP hD).oldLabels = id
  | 0, _, _, hZ, _, _ => by
    change (programOn _ _).oldLabels = id
    rw [programOn_oldLabels]
    rfl
  | m + 1, ν, Z, hZ, hP, hD => by
    change (idProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ W m (fun i => ν i.castSucc) (vfDropLast Z).image
      (described_drop hZ) (vfDropLast_image_properInvariant hP) (drop_doublyBounded hD)).oldLabels ∘ id = id
    rw [idProgram_oldLabels m]
    rfl

theorem idProgram_volumeIndex : ∀ (m : ℕ) (ν : Fin m → Fin q) (Z : DefSet (rawMixedSpace (M := M) m q) S)
    (hZ : Described W ν Z) (hP : ProperInvariant S Z.carrier) (hD : VFDoublyBounded Z.carrier),
    (idProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ W m ν Z hZ hP hD).volumeIndex = ν
  | 0, _, _, _, _, _ => funext fun i => i.elim0
  | m + 1, ν, Z, hZ, hP, hD => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change (OrderedStandardContractionProgram.step _ _).volumeIndex (Fin.last m) = _
      rw [OrderedStandardContractionProgram.volumeIndex_step_last]
      exact congrFun (idProgram_oldLabels (G := G) h00 hc linear hκ hs hv hsmall hΓ W m (fun i => ν i.castSucc)
        (vfDropLast Z).image (described_drop hZ) (vfDropLast_image_properInvariant hP) (drop_doublyBounded hD))
        (ν (Fin.last m))
    · change (OrderedStandardContractionProgram.step _ _).volumeIndex j.castSucc = _
      rw [OrderedStandardContractionProgram.volumeIndex_step_castSucc]
      exact congrFun (idProgram_volumeIndex m (fun i => ν i.castSucc)
        (vfDropLast Z).image (described_drop hZ) (vfDropLast_image_properInvariant hP) (drop_doublyBounded hD)) j

end IdProgram

/-! ### The regularization stage and the program -/

section Reg
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {n r : ℕ} (Z : DefSet (rawMixedSpace (M := M) (n + 1) r) S)

/-- The RV target: the regularized labels `rv(x) ++ w` of the points of `Z`. -/
def regTarget : DefSet (rawMixedSpace (M := M) 0 ((n + 1) + r)) S := (rvProjection (regularization Z)).image

theorem mem_regTarget (u : Fin ((n + 1) + r) → RVInfinity M) :
    ((Fin.elim0, u) : Mixed M 0 ((n + 1) + r)) ∈ (regTarget Z).carrier ↔
      ∃ p ∈ Z.carrier, Fin.append (tupleRV M p.1) p.2 = u := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.val, p.property, congrArg Prod.snd hp⟩
  · rintro ⟨p, hp, hu⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    change ((Fin.elim0, Fin.append (tupleRV M p.1) p.2) : Mixed M 0 ((n + 1) + r)) = (Fin.elim0, u)
    rw [hu]

variable {Z} in
/-- On the regularized set of an RV-pullback, every VF coordinate is an
RV-pullback along its regularization label. -/
theorem described_reg (hRP : ∀ p ∈ Z.carrier, ∀ x : Fin (n + 1) → VF M, tupleRV M x = tupleRV M p.1 →
      ((x, p.2) : Mixed M (n + 1) r) ∈ Z.carrier) :
    Described (regTarget Z) (Fin.castAdd r) (regularizeMap Z).image := by
  intro q
  rw [regularization_carrier]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(mem_regTarget Z _).mpr ⟨p, hp, rfl⟩, fun i => ?_⟩
    change rv M (p.1 i) = Fin.append (tupleRV M p.1) p.2 (Fin.castAdd r i)
    rw [Fin.append_left]
    rfl
  · rintro ⟨hW, hrv⟩
    obtain ⟨p, hp, hu⟩ := (mem_regTarget Z _).mp hW
    have ht : tupleRV M q.1 = tupleRV M p.1 := funext fun i => by
      have h1 := hrv i
      rw [← hu, Fin.append_left] at h1
      exact h1
    refine ⟨(q.1, p.2), hRP p hp q.1 ht, ?_⟩
    change ((q.1, Fin.append (tupleRV M q.1) p.2) : Mixed M (n + 1) ((n + 1) + r)) = q
    rw [ht, hu]

variable (hP : ProperInvariant S Z.carrier) (hD : VFDoublyBounded Z.carrier)
variable (hT : ∀ p ∈ Z.carrier, ∀ p' ∈ Z.carrier, p.2 = p'.2 → tupleRV M p.1 = tupleRV M p'.1)
variable (hRP : ∀ p ∈ Z.carrier, ∀ x : Fin (n + 1) → VF M, tupleRV M x = tupleRV M p.1 →
  ((x, p.2) : Mixed M (n + 1) r) ∈ Z.carrier)

include hT in
/-- When the labels of `Z` determine the residues of its VF coordinates, the
labels of the regularization depend only on the labels. -/
theorem reg_labels (p p' : Z) (h : p.val.2 = p'.val.2) :
    (regularization Z p).val.2 = (regularization Z p').val.2 := by
  change Fin.append (tupleRV M p.val.1) p.val.2 = Fin.append (tupleRV M p'.val.1) p'.val.2
  rw [hT _ p.property _ p'.property h, h]

include hD in
theorem reg_vfDoublyBounded : VFDoublyBounded (regularizeMap Z).image.carrier := by
  obtain ⟨γ, hγ⟩ := hD
  refine ⟨γ, ?_⟩
  rw [regularization_carrier]
  rintro _ ⟨p, hp, rfl⟩ i
  exact hγ p hp i

/-- **The regularization stage** `(x, w) ↦ (x, rv(x) ++ w)`, a label map. -/
def regStage : StandardContractionStage (G := G) Z where
  arity := (n + 1) + r
  target := (regularizeMap Z).image
  lift := regularization Z
  home := labelMap_home h00 hc linear hκ hs hv hsmall hΓ _ hP
    (regularization_properInvariant h00 hc hκ hs hv Z hP hD) (regularization_bijective Z) (fun _ => rfl)
    (reg_labels Z hT)
  proper := regularization_properInvariant h00 hc hκ hs hv Z hP hD
  doublyBounded := reg_vfDoublyBounded Z hD
  relative := fun _ _ => rfl
  oldLabels := Fin.natAdd (n + 1)
  oldLabels_injective := Fin.natAdd_injective r (n + 1)
  retained := fun p i => by simp only [regularization_apply, regularize, Fin.append_right]
  leading := Fin.castAdd r (Fin.last n)
  bundle := described_bundle (described_reg hRP)
  exceptional := DefSet.empty _ S
  exceptional_subset := fun _ hp => hp.elim
  exceptional_dim := DiamondIntegral.Section6.DiamondLift.vfDim_empty_lt (Fin.last n)
  unitDerivative := fun p _ => labelMap_unit (G := G) hv _ hP (fun _ => rfl) (reg_labels Z hT) p

/-- **The program**: the regularization stage, then identity stages. -/
def liftProgram : OrderedStandardContractionProgram (G := G) S Z (regTarget Z) :=
  .step (regStage h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP)
    (idProgram h00 hc linear hκ hs hv hsmall hΓ (regTarget Z) n (fun i => Fin.castAdd r i.castSucc)
      (vfDropLast (regularizeMap Z).image).image (described_drop (described_reg hRP))
      (vfDropLast_image_properInvariant (regularization_properInvariant h00 hc hκ hs hv Z hP hD))
      (drop_doublyBounded (reg_vfDoublyBounded Z hD)))

theorem liftProgram_oldLabels :
    (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).oldLabels = Fin.natAdd (n + 1) := by
  funext i
  exact congrFun (idProgram_oldLabels (G := G) h00 hc linear hκ hs hv hsmall hΓ (regTarget Z) n
    (fun i => Fin.castAdd r i.castSucc) (vfDropLast (regularizeMap Z).image).image
    (described_drop (described_reg hRP))
    (vfDropLast_image_properInvariant (regularization_properInvariant h00 hc hκ hs hv Z hP hD))
    (drop_doublyBounded (reg_vfDoublyBounded Z hD))) (Fin.natAdd (n + 1) i)

theorem liftProgram_volumeIndex :
    (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).volumeIndex = Fin.castAdd r := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (OrderedStandardContractionProgram.step _ _).volumeIndex (Fin.last n) = _
    rw [OrderedStandardContractionProgram.volumeIndex_step_last]
    exact congrFun (idProgram_oldLabels (G := G) h00 hc linear hκ hs hv hsmall hΓ (regTarget Z) n
      (fun i => Fin.castAdd r i.castSucc) (vfDropLast (regularizeMap Z).image).image
      (described_drop (described_reg hRP))
      (vfDropLast_image_properInvariant (regularization_properInvariant h00 hc hκ hs hv Z hP hD))
      (drop_doublyBounded (reg_vfDoublyBounded Z hD))) (Fin.castAdd r (Fin.last n))
  · change (OrderedStandardContractionProgram.step _ _).volumeIndex j.castSucc = _
    rw [OrderedStandardContractionProgram.volumeIndex_step_castSucc]
    exact congrFun (idProgram_volumeIndex (G := G) h00 hc linear hκ hs hv hsmall hΓ (regTarget Z) n
      (fun i => Fin.castAdd r i.castSucc) (vfDropLast (regularizeMap Z).image).image
      (described_drop (described_reg hRP))
      (vfDropLast_image_properInvariant (regularization_properInvariant h00 hc hκ hs hv Z hP hD))
      (drop_doublyBounded (reg_vfDoublyBounded Z hD))) j

/-- The program map keeps the labels of `Z` (at the old labels `natAdd (n + 1)`). -/
theorem liftProgram_toMap_labels (p : Z) (j : Fin r) :
    ((liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).toMap p).val.2 (Fin.natAdd (n + 1) j) =
      p.val.2 j := by
  have h := (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).retained p j
  rwa [liftProgram_oldLabels] at h

theorem liftProgram_labels (a b : Z)
    (h : (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).toMap a =
      (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).toMap b) :
    a.val.2 = b.val.2 := by
  funext j
  rw [← liftProgram_toMap_labels h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP a j, h,
    liftProgram_toMap_labels]

variable (ωZ : Map Z (DefSet.univ (rawGammaPresentation (M := M)) S))
variable (hωZ : ∀ p p' : Z, p.val.2 = p'.val.2 → ωZ p = ωZ p')

/-- The RV form: `ωZ` descended along the surjective program map. -/
def liftRVForm : Map (regTarget Z) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  definableSurjectiveDescent (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).toMap
    (liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).surjective ωZ
    (fun a b h => hωZ a b (liftProgram_labels h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP a b h))

theorem liftRVForm_toMap (p : Z) :
    liftRVForm (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP ωZ hωZ
      ((liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP).toMap p) = ωZ p :=
  definableSurjectiveDescent_apply _ _ _ _ p

/-- **The measured contraction** of `(Z, ωZ)`. -/
def liftMOC : MeasuredOrderedContraction (G := G) Z ωZ where
  data :=
    { arity := (n + 1) + r
      rvTarget := regTarget Z
      program := liftProgram (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP
      rvForm := liftRVForm (G := G) h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP ωZ hωZ
      factor := fun p => congrArg Subtype.val (liftRVForm_toMap h00 hc linear hκ hs hv hsmall hΓ Z hP hD hT hRP ωZ hωZ p) }
  lift := Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _ hP)

end Reg

/-! ### The lift of a measured RV object -/

section Lift
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} (U : MeasuredRVObject (M := M) (T : Set M) (n + 1))

/-- The lift, prepared in the identity order. -/
abbrev liftSet : DefSet (rawMixedSpace (M := M) (n + 1) U.object.arity) (T : Set M) :=
  reindexedVFSet (rvLift U.object) 1

theorem mem_liftSet (p : Mixed M (n + 1) U.object.arity) :
    p ∈ (liftSet U).carrier ↔ p ∈ (rvLift U.object).carrier := by
  rw [mem_reindexedVFSet]
  exact Iff.rfl

/-- The labels of the lift determine the residues of its VF coordinates. -/
theorem rvLift_tagged : ∀ p ∈ (rvLift U.object).carrier, ∀ p' ∈ (rvLift U.object).carrier, p.2 = p'.2 →
    tupleRV M p.1 = tupleRV M p'.1 := by
  rintro p ⟨u, hu, hpu⟩ p' ⟨u', hu', hpu'⟩ h
  have huu : u = u' := Subtype.ext (hu.trans (h.trans hu'.symm))
  subst huu
  exact hpu.symm.trans hpu'

/-- The lift is an RV-pullback. -/
theorem rvLift_pullback : ∀ p ∈ (rvLift U.object).carrier, ∀ x : Fin (n + 1) → VF M, tupleRV M x = tupleRV M p.1 →
    ((x, p.2) : Mixed M (n + 1) U.object.arity) ∈ (rvLift U.object).carrier := by
  rintro p ⟨u, hu, hpu⟩ x hx
  exact ⟨u, hu, hpu.trans hx.symm⟩

theorem liftSet_tagged : ∀ p ∈ (liftSet U).carrier, ∀ p' ∈ (liftSet U).carrier, p.2 = p'.2 →
    tupleRV M p.1 = tupleRV M p'.1 := fun p hp p' hp' =>
  rvLift_tagged U p ((mem_liftSet U p).mp hp) p' ((mem_liftSet U p').mp hp')

theorem liftSet_pullback : ∀ p ∈ (liftSet U).carrier, ∀ x : Fin (n + 1) → VF M, tupleRV M x = tupleRV M p.1 →
    ((x, p.2) : Mixed M (n + 1) U.object.arity) ∈ (liftSet U).carrier := fun p hp x hx =>
  (mem_liftSet U _).mpr (rvLift_pullback U p ((mem_liftSet U p).mp hp) x hx)

theorem liftSet_hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin 0 → RVInfinity M),
    {u : Fin U.object.arity → RVInfinity M | (a, u) ∈ (liftSet U).carrier ∧ u ∘ Fin.elim0 = t}.Finite :=
  fun a _ => (lift_fibre_finite U a).subset (fun _ hu => (mem_liftSet U _).mp hu.1)

/-- The form of the lift, on the prepared copy. -/
def liftFormE : Map (liftSet U) (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  (liftForm U).comp ((vfRelabeling (rvLift U.object) 1).inverse (vfRelabeling_bijective (rvLift U.object) 1))

theorem liftFormE_relabel (p : rvLift U.object) :
    (liftFormE U (vfRelabeling (rvLift U.object) 1 p)).val = (liftForm U p).val := by
  change (liftForm U ((vfRelabeling (rvLift U.object) 1).inverse (vfRelabeling_bijective (rvLift U.object) 1)
    (vfRelabeling (rvLift U.object) 1 p))).val = _
  rw [Map.inverse_apply]

theorem liftFormE_val (p : liftSet U) (w : U.object.domain) (hw : w.val = p.val.2) :
    (liftFormE U p).val = (U.form w).val := by
  obtain ⟨p₀, rfl⟩ := (vfRelabeling_bijective (rvLift U.object) 1).2 p
  rw [liftFormE_relabel]
  have he : liftLabelMap U.object p₀ = w := Subtype.ext hw.symm
  change (U.form (liftLabelMap U.object p₀)).val = _
  rw [he]

theorem liftFormE_labels (p p' : liftSet U) (h : p.val.2 = p'.val.2) : liftFormE U p = liftFormE U p' := by
  obtain ⟨u, hu, -⟩ := (mem_liftSet U p.val).mp p.property
  apply Subtype.ext
  rw [liftFormE_val U p u hu, liftFormE_val U p' u (hu.trans h)]

/-- The RV target of the lift: the labels `val(w) ++ w`, `w ∈ U`. -/
theorem mem_liftTarget (u : Fin ((n + 1) + U.object.arity) → RVInfinity M) :
    ((Fin.elim0, u) : Mixed M 0 ((n + 1) + U.object.arity)) ∈ (regTarget (liftSet U)).carrier ↔
      ∃ w : U.object.domain, Fin.append (U.object.value w) w.val = u := by
  rw [mem_regTarget]
  constructor
  · rintro ⟨p, hp, hu⟩
    obtain ⟨w, hw, hval⟩ := (mem_liftSet U p).mp hp
    exact ⟨w, (congrArg₂ Fin.append hval hw).trans hu⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨x, hx⟩ := SpecialTransformations.Section4.tupleRV_surjective (U.object.value w)
    exact ⟨(x, w.val), (mem_liftSet U _).mpr ⟨w, rfl, hx.symm⟩, congrArg (fun t => Fin.append t w.val) hx⟩

variable (hU : U.doublyBounded) (hP : ProperInvariant (T : Set M) (rvLift U.object).carrier)

include hP in
theorem liftSet_proper : ProperInvariant (T : Set M) (liftSet U).carrier :=
  reindexedVFSet_properInvariant _ 1 hP

include hU in
theorem liftSet_doublyBounded : VFDoublyBounded (liftSet U).carrier :=
  reindexedVFSet_doublyBounded _ 1 (measuredRVLift_vfDoublyBounded U hU)

/-- **The measured contraction of the prepared lift**: regularization, then
identity stages. -/
def liftC : MeasuredOrderedContraction (G := G) (liftSet U) (liftFormE U) :=
  liftMOC h00 hc lin hκ hs hv hsmall hΓ (liftSet U) (liftSet_proper U hP) (liftSet_doublyBounded U hU)
    (liftSet_tagged U) (liftSet_pullback U) (liftFormE U) (liftFormE_labels U)

/-- **The tautological contraction of the lift**, a normalized contraction of
`(μL U, ω)` in the identity order. -/
def tautLift (D : ZeroCenteredData (rvLift U.object)) :
    NormalizedMeasuredContraction (G := G) (rvLift U.object) (liftForm U) 1 :=
  ofContractionOrd h00 hc lin hκ hs hv hsmall hΓ D
    (fun _ hp i => (measuredRVLift_vfDoublyBounded U hU).nonzero hp i) 1
    (liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP) (liftFormE_relabel U)

theorem liftC_volumeIndex :
    (liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).data.program.volumeIndex = Fin.castAdd U.object.arity :=
  liftProgram_volumeIndex (G := G) h00 hc lin hκ hs hv hsmall hΓ (liftSet U) (liftSet_proper U hP)
    (liftSet_doublyBounded U hU) (liftSet_tagged U) (liftSet_pullback U)

theorem liftC_recover (p : Mixed M (n + 1) ((n + 1) + U.object.arity)) :
    p ∈ (liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).lift.target.carrier ↔
      (Fin.elim0, p.2) ∈ (regTarget (liftSet U)).carrier ∧
        ∀ i, rv M (p.1 i) = p.2 (Fin.castAdd U.object.arity i) := by
  rw [(liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).lift.recover p,
    liftC_volumeIndex h00 hc hκ hs hv hsmall hΓ U hU hP]
  rfl

/-- The RV form of the contraction is the form of `U` at the old labels. -/
theorem liftC_rvForm (z : regTarget (liftSet U)) (w : U.object.domain)
    (hw : ∀ j, w.val j = z.val.2 (Fin.natAdd (n + 1) j)) :
    ((liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).data.rvForm z).val = (U.form w).val := by
  obtain ⟨y, rfl⟩ := (liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).data.program.surjective z
  refine ((liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).data.factor y).trans (liftFormE_val U y w ?_)
  funext j
  rw [hw j]
  exact liftProgram_toMap_labels (G := G) h00 hc lin hκ hs hv hsmall hΓ (liftSet U) (liftSet_proper U hP)
    (liftSet_doublyBounded U hU) (liftSet_tagged U) (liftSet_pullback U) y j

/-- **The class of the tautological contraction**: its head-start-`0` object is
isomorphic to `U` through `u ↦ u ∘ natAdd (n + 1)`. -/
theorem cls_liftC
    (hFinE : ∀ (a : Fin (n + 1) → VF M) (t : Fin 0 → RVInfinity M),
      {u : Fin U.object.arity → RVInfinity M | (a, u) ∈ (liftSet U).carrier ∧ u ∘ Fin.elim0 = t}.Finite) :
    cls (objOf hc T ((liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP).headStartObject hc h00 hκ.le hs hsmall 0
        Fin.elim0 hFinE)
        (headStartObject_doublyBounded h00 hc hκ hs hsmall (liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP) 0
          Fin.elim0 hFinE)) =
      cls (objOf hc T U hU) := by
  set C := liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP with hC
  set H := C.headStartObject hc h00 hκ.le hs hsmall 0 Fin.elim0 hFinE with hH
  have hX := liftC_recover (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP
  have hT := C.lift.target_tagged
  let l : Fin 0 → Fin ((n + 1) + U.object.arity) := C.data.program.oldLabels ∘ Fin.elim0
  have hdom : ∀ u, u ∈ H.object.domain.carrier ↔ ∃ w : U.object.domain, Fin.append (U.object.value w) w.val = u :=
    fun u => (mem_domain_labels hX l hT u).trans (mem_liftTarget U u)
  have hsel : ∀ u : H.object.domain,
      (rvSelectMap H.object.domain (Fin.natAdd (n + 1)) u).val ∈ U.object.domain.carrier := by
    intro u
    obtain ⟨w, hw⟩ := (hdom u.val).mp u.property
    have he : u.val ∘ Fin.natAdd (n + 1) = w.val := by
      rw [← hw]
      funext j
      exact Fin.append_right _ _ j
    rw [rvSelectMap_val, he]
    exact w.property
  let F : Map H.object.domain U.object.domain := (rvSelectMap H.object.domain (Fin.natAdd (n + 1))).corestrict hsel
  have hFw : ∀ (u : H.object.domain) (w : U.object.domain), Fin.append (U.object.value w) w.val = u.val → F u = w := by
    intro u w hw
    apply Subtype.ext
    change u.val ∘ Fin.natAdd (n + 1) = w.val
    rw [← hw]
    funext j
    exact Fin.append_right _ _ j
  have hF : Function.Bijective F := by
    constructor
    · intro u u' he
      obtain ⟨w, hw⟩ := (hdom u.val).mp u.property
      obtain ⟨w', hw'⟩ := (hdom u'.val).mp u'.property
      have hww : w = w' := (hFw u w hw).symm.trans (he.trans (hFw u' w' hw'))
      subst hww
      exact Subtype.ext (hw.symm.trans hw')
    · intro w
      exact ⟨⟨_, (hdom _).mpr ⟨w, rfl⟩⟩, hFw _ w rfl⟩
  refine cls_eq_of_volume hc (show (n + 1) + 0 = n + 1 from rfl) _ hU F hF (fun u => ?_) (fun u => ?_)
  · obtain ⟨w, hw⟩ := (hdom u.val).mp u.property
    rw [volumeGamma_eq, volumeGamma_eq, hFw u w hw]
    refine Finset.prod_congr rfl (fun i _ => congrArg gam ?_)
    change (preparedHeadStartRVObject C.lift.target 0 l hT).value u i = _
    rw [value_labels hX l hT u]
    change u.val (Fin.append (Fin.castAdd U.object.arity) l (Fin.castAdd 0 i)) = _
    rw [Fin.append_left, ← hw, Fin.append_left]
  · obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
    obtain ⟨w, hw⟩ := (hdom _).mp (pureRVTagQuotient _ p).property
    rw [hFw _ w hw]
    change (headStartRVForm C.lift.target 0 l C.form C.form_same_tags (pureRVTagQuotient _ p)).val = (U.form w).val
    rw [headStartRVForm_at]
    have hz : ((Fin.elim0, p.val.2) : Mixed M 0 ((n + 1) + U.object.arity)) ∈ (regTarget (liftSet U)).carrier :=
      ((mem_bundle_labels hX l p.val).mp p.property).1
    refine (rvForm_read C.data.rvForm (C.data.liftedRVMap C.lift) (fun _ => rfl) _ ⟨_, hz⟩ ?_).trans ?_
    · rw [headStartBaseProjection_value]
    · refine liftC_rvForm (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP ⟨_, hz⟩ w (fun j => ?_)
      change w.val j = (pureRVTagQuotient _ p).val (Fin.natAdd (n + 1) j)
      rw [← hw, Fin.append_right]

include hU hP in
/-- **The class of `tautLift`** is the class of `U`. -/
theorem clsOf_tautLift (D : ZeroCenteredData (rvLift U.object)) :
    clsOf h00 hc hκ hs hv hsmall hΓ (liftObject U hP) (tautLift (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP D) =
      cls (objOf hc T U hU) :=
  (cls_ofContractionOrd h00 hc lin hκ hs hv hsmall hΓ D
    (fun _ hp i => (measuredRVLift_vfDoublyBounded U hU).nonzero hp i) 1
    (liftC (G := G) h00 hc hκ hs hv hsmall hΓ U hU hP) (liftFormE_relabel U) 0 Fin.elim0
    (object_hFin (liftObject U hP) Fin.elim0) (liftSet_hFin U)).trans
    (cls_liftC h00 hc hκ hs hv hsmall hΓ U hU hP (liftSet_hFin U))

end Lift

/-! ### The main results -/

section Main
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include V hV hVT hTV hnt in
/-- **(1) The tautological contraction of a lift.** The lift `μL U` of a doubly
bounded measured RV object has a standard contraction (in the identity order)
whose class is exactly the class of `U`. -/
theorem exists_taut_contraction {n : ℕ} (U : MeasuredRVObject (M := M) (T : Set M) (n + 1))
    (hU : U.doublyBounded) (hP : ProperInvariant (T : Set M) (rvLift U.object).carrier) :
    ∃ F : NormalizedMeasuredContraction (G := G) (liftObject U hP).carrier (liftObject U hP).form 1,
      clsOf h00 hc hκ hs hv hsmall hΓ (liftObject U hP) F = cls (objOf hc T U hU) := by
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (rvLift U.object) hP
  exact ⟨tautLift h00 hc hκ hs hv hsmall hΓ U hU hP D, clsOf_tautLift h00 hc hκ hs hv hsmall hΓ U hU hP D⟩

include V hV hVT hTV hnt in
/-- **(2) Any contraction of a lift.** Every standard contraction of `μL U`, in
any order, has a class `μIsp^db`-related to the class of `U`. -/
theorem ispRel_lift {n : ℕ} (U : MeasuredRVObject (M := M) (T : Set M) (n + 1)) (hU : U.doublyBounded)
    (hP : ProperInvariant (T : Set M) (rvLift U.object).carrier) {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) (liftObject U hP).carrier (liftObject U hP).form e) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ (liftObject U hP) F) (cls (objOf hc T U hU)) := by
  obtain ⟨F₀, hF₀⟩ := exists_taut_contraction (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ U hU hP
  have h := OrderIndependence.star (G := G) h00 hc hκ hs hv n T V hV hVT hTV hnt hsmall hΓ (liftObject U hP) F F₀
  rwa [hF₀] at h

/-- The class of the Section 6 object of a chart is the class of the chart. -/
theorem cls_objOf_dbObj {k : ℕ} (a : Obj (BT T) k) :
    cls (objOf hc T (dbObj hc h00 hκ hs T hsmall hΓ a).1 (dbObj hc h00 hκ hs T hsmall hΓ a).2) = cls a := by
  rw [← StrictCharts.cls_strictObj h00 a]
  exact (IsoOfMeasured.cls_eq_iff_measured hc).mpr ⟨measuredIso_chartOf hc (dbObj hc h00 hκ hs T hsmall hΓ a).1⟩

include V hV hVT hTV hnt in
/-- **(3) Chart objects.** For a chart `a` of `μRV^db[n + 1]`, every standard
contraction of the lift of its Section 6 object (the object of
`LiftClasses.liftCls_cls`), in any order, has a class `μIsp^db`-related to the
class of `a`. -/
theorem ispRel_chart {n : ℕ} (a : Obj (BT T) (n + 1))
    (hP : ProperInvariant (T : Set M) (rvLift (dbObj hc h00 hκ hs T hsmall hΓ a).1.object).carrier)
    {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1 hP).carrier
      (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1 hP).form e) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1 hP) F) (cls a) := by
  have h := ispRel_lift (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ (dbObj hc h00 hκ hs T hsmall hΓ a).1
    (dbObj hc h00 hκ hs T hsmall hΓ a).2 hP F
  rwa [cls_objOf_dbObj] at h

end Main

end DiamondIntegral.Section7.TautologicalLifts
