import «section 6».StandardContractionStages
import «section 6».VFRelabelingHomeomorphisms
import «section 6».DiamondGroupoid
import «section 6».InvariantOfCovariance
import «section 6».ProperComposition
import Section4.CoordinateMaps

/-! Reindexing a standard contraction stage by a permutation fixing the last
VF coordinate.

Let `H` be a standard contraction stage of `Y ⊆ VF^{N+1} × RVʳ`; it changes only
the last VF coordinate. Let `s` be a permutation of `Fin (N + 1)` with
`s (last) = last`. Write `R_Y = vfRelabeling Y s : Y → Y^s`, `(x, u) ↦ (x ∘ s, u)`,
for the relabelling onto the reindexed set `Y^s = reindexedVFSet Y s`.

* `s` restricts to a permutation `σ = inducedPerm s hfix` of `Fin N` with
  `castSucc (σ i) = s (castSucc i)` (`inducedPerm_castSucc`). Dropping the last
  coordinate commutes with reindexing: `init (x ∘ s) = init x ∘ σ` (`init_comp`), so
  the contracted set of `T^s` is the `σ`-reindexing of the contracted set of `T`
  (`reindexed_contracted_carrier`), and `T^s` is the RV-disc bundle over its
  contracted set whenever `T` is (`reindexed_bundle`).
* The conjugate `R_target ∘ H.lift ∘ R_Y⁻¹` (`reindexLift`) is a standard
  contraction stage of `Y^s` (`reindexStage`): its target is `target^s`, it has the
  arity, old labels and leading label of `H`, and its exceptional set is
  `exceptional^s`. It is a proper covariant homeomorphism by Lemma 6.9; it fixes the
  first `N` coordinates because `s` permutes them; the exceptional set has small VF
  dimension because it is a definable image of that of `H` (Corollary 4.5 through
  `vfDim_image_le`); and its derivative off the exceptional set is
  `P_s ∘ L ∘ P_{s⁻¹}` for permutation matrices `P`, of determinant `det L = 1`
  (`det_conj`).
* The contracted set of the reindexed stage is the `σ`-reindexing of that of `H`
  (`reindexStage_contracted`), and the reindexed contraction at `R_Y q₀` is the
  contraction of `H` at `q₀` read through `σ` (`reindexStage_contraction_value`);
  similarly for the lift (`reindexStage_lift_value`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.StageReindexing
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondGroupoid

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {N r : ℕ}

/-! ### The induced permutation of the first `N` coordinates -/

section Perm
variable (s : Equiv.Perm (Fin (N + 1))) (hfix : s (Fin.last N) = Fin.last N)

omit [M ⊨ Axioms.ACVF] in
include hfix in
theorem symm_last : s.symm (Fin.last N) = Fin.last N :=
  s.symm_apply_eq.mpr hfix.symm

omit [M ⊨ Axioms.ACVF] in
include hfix in
theorem perm_castSucc_ne_last (i : Fin N) : s i.castSucc ≠ Fin.last N :=
  fun h => Fin.castSucc_ne_last i (s.injective (h.trans hfix.symm))

include hfix in
/-- The permutation of `Fin N` induced by a permutation of `Fin (N + 1)` fixing
`last`. -/
def inducedPerm : Equiv.Perm (Fin N) where
  toFun i := (s i.castSucc).castPred (perm_castSucc_ne_last s hfix i)
  invFun i := (s.symm i.castSucc).castPred (perm_castSucc_ne_last s.symm (symm_last s hfix) i)
  left_inv i := Fin.castSucc_injective _ (by
    simp only [Fin.castSucc_castPred, Equiv.symm_apply_apply])
  right_inv i := Fin.castSucc_injective _ (by
    simp only [Fin.castSucc_castPred, Equiv.apply_symm_apply])

theorem inducedPerm_castSucc (i : Fin N) : (inducedPerm s hfix i).castSucc = s i.castSucc :=
  Fin.castSucc_castPred _ (perm_castSucc_ne_last s hfix i)

theorem inducedPerm_symm_castSucc (i : Fin N) :
    ((inducedPerm s hfix).symm i).castSucc = s.symm i.castSucc :=
  Fin.castSucc_castPred _ (perm_castSucc_ne_last s.symm (symm_last s hfix) i)

/-- Dropping the last coordinate commutes with reindexing by `s`. -/
theorem init_comp {β : Type} (f : Fin (N + 1) → β) :
    Fin.init (f ∘ s) = Fin.init f ∘ inducedPerm s hfix := by
  funext i
  change f (s i.castSucc) = f (inducedPerm s hfix i).castSucc
  rw [inducedPerm_castSucc]

theorem init_comp_symm {β : Type} (f : Fin (N + 1) → β) :
    Fin.init (f ∘ s.symm) = Fin.init f ∘ (inducedPerm s hfix).symm := by
  funext i
  change f (s.symm i.castSucc) = f ((inducedPerm s hfix).symm i).castSucc
  rw [inducedPerm_symm_castSucc]

/-! ### Contracted sets and bundles of reindexed sets -/

/-- The contracted set of a reindexed set is the reindexed contracted set. -/
theorem mem_reindexed_contracted {a : ℕ} (T : DefSet (rawMixedSpace (M := M) (N + 1) a) S)
    (q : Mixed M N a) :
    q ∈ (vfDropLast (reindexedVFSet T s)).image.carrier ↔
      q ∈ (reindexedVFSet (vfDropLast T).image (inducedPerm s hfix)).carrier := by
  rw [mem_reindexedVFSet]
  constructor
  · rintro ⟨x, hx⟩
    have hxq : ((Fin.init x.val.1, x.val.2) : Mixed M N a) = q := hx
    have hxT := (mem_reindexedVFSet T s x.val).mp x.property
    refine ⟨⟨_, hxT⟩, ?_⟩
    change ((Fin.init (x.val.1 ∘ s.symm), x.val.2) : Mixed M N a) =
      reindexVFPoint (inducedPerm s hfix).symm q
    rw [← hxq, init_comp_symm s hfix]
    rfl
  · rintro ⟨y, hy⟩
    have hyq : ((Fin.init y.val.1, y.val.2) : Mixed M N a) = reindexVFPoint (inducedPerm s hfix).symm q := hy
    have hmem : reindexVFPoint s y.val ∈ (reindexedVFSet T s).carrier := by
      apply (mem_reindexedVFSet T s _).mpr
      rw [reindexVFPoint_inverse]
      exact y.property
    refine ⟨⟨_, hmem⟩, ?_⟩
    change ((Fin.init (y.val.1 ∘ s), y.val.2) : Mixed M N a) = q
    rw [init_comp s hfix]
    have h1 : Fin.init y.val.1 = q.1 ∘ (inducedPerm s hfix).symm := congrArg Prod.fst hyq
    have h2 : y.val.2 = q.2 := congrArg Prod.snd hyq
    refine Prod.ext ?_ h2
    change Fin.init y.val.1 ∘ inducedPerm s hfix = q.1
    rw [h1]
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem reindexed_contracted_carrier {a : ℕ} (T : DefSet (rawMixedSpace (M := M) (N + 1) a) S) :
    (vfDropLast (reindexedVFSet T s)).image.carrier =
      (reindexedVFSet (vfDropLast T).image (inducedPerm s hfix)).carrier :=
  Set.ext (mem_reindexed_contracted s hfix T)

include hfix in
/-- A reindexed RV-disc bundle over the last coordinate is the RV-disc bundle
over its contracted set. -/
theorem reindexed_bundle {a : ℕ} (T : DefSet (rawMixedSpace (M := M) (N + 1) a) S) (k : Fin a)
    (hT : T.carrier = (rvCoordinateBundle (vfDropLast T).image k).carrier) :
    (reindexedVFSet T s).carrier =
      (rvCoordinateBundle (vfDropLast (reindexedVFSet T s)).image k).carrier := by
  ext x
  have hx : x ∈ (reindexedVFSet T s).carrier ↔ reindexVFPoint s.symm x ∈ T.carrier :=
    mem_reindexedVFSet T s x
  rw [hT] at hx
  refine hx.trans ?_
  change ((Fin.init (x.1 ∘ s.symm), x.2) : Mixed M N a) ∈ (vfDropLast T).image.carrier ∧
      rv M ((x.1 ∘ s.symm) (Fin.last N)) = x.2 k ↔
    ((Fin.init x.1, x.2) : Mixed M N a) ∈ (vfDropLast (reindexedVFSet T s)).image.carrier ∧
      rv M (x.1 (Fin.last N)) = x.2 k
  rw [mem_reindexed_contracted s hfix T, mem_reindexedVFSet, init_comp_symm s hfix, Function.comp_apply,
    symm_last s hfix]
  rfl

end Perm

/-! ### Determinants of conjugates by permutation matrices -/

theorem det_conj {n : ℕ} (s : Equiv.Perm (Fin n)) (L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M))
    (hL : (LinearMap.toMatrix' L).det = 1) :
    (LinearMap.toMatrix' ((vfReindexLinear s).comp (L.comp (vfReindexLinear s.symm)))).det = 1 := by
  have hsc := congrArg (fun D => (LinearMap.toMatrix' D).det) (vfReindexLinear_symm_comp (M := M) s)
  simp only [LinearMap.toMatrix'_comp, Matrix.det_mul, LinearMap.toMatrix'_id, Matrix.det_one] at hsc
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, Matrix.det_mul, Matrix.det_mul, hL]
  linear_combination hsc

/-! ### The inverse relabelling -/

section Inverse
variable {n : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (s : Equiv.Perm (Fin n))

theorem relabel_inverse_value (q : reindexedVFSet A s) :
    ((vfRelabeling A s).inverse (vfRelabeling_bijective A s) q).val = (q.val.1 ∘ s.symm, q.val.2) := by
  have h := congrArg Subtype.val (Map.apply_inverse (vfRelabeling A s) (vfRelabeling_bijective A s) q)
  rw [vfRelabeling_value] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext ?_ h2
  rw [← h1]
  funext i
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

include hv in
/-- The inverse relabelling is affine near every point, with derivative the
inverse permutation. -/
theorem relabel_inverse_derivative (hA : ProperInvariant S A.carrier) (q : reindexedVFSet A s) :
    HasMixedVFDerivativeAt ((vfRelabeling A s).inverse (vfRelabeling_bijective A s)) q
      (vfReindexLinear s.symm) := by
  have hB := reindexedVFSet_properInvariant A s hA
  obtain ⟨ρ, hρ⟩ := exists_vfBall_subset_nhds hv q.val.1
    ((hB.clopen_fibres hv q.val.2).isOpen.mem_nhds q.property)
  refine ⟨fun x => vfReindexLinear s.symm x + 0, ⟨ρ, fun x hx => ⟨hρ hx, ?_⟩⟩,
    hasVFDerivativeAt_affine (vfReindexLinear s.symm) 0 q.val.1⟩
  rw [relabel_inverse_value, relabel_inverse_value]
  change (x ∘ s.symm, q.val.2) = (vfReindexLinear s.symm x + 0, q.val.2)
  rw [add_zero, vfReindexLinear_apply]

end Inverse

/-! ### The reindexed stage -/

section Stage
variable {Y : DefSet (rawMixedSpace (M := M) (N + 1) r) S}
variable (H : StandardContractionStage (G := G) Y) (s : Equiv.Perm (Fin (N + 1)))
variable (hfix : s (Fin.last N) = Fin.last N)

/-- The conjugate lift `R_target ∘ H.lift ∘ R_Y⁻¹`. -/
def reindexLift : Map (reindexedVFSet Y s) (reindexedVFSet H.target s) :=
  (vfRelabeling H.target s).comp (H.lift.comp ((vfRelabeling Y s).inverse (vfRelabeling_bijective Y s)))

theorem reindexLift_relabel (p : Y) :
    reindexLift H s (vfRelabeling Y s p) = vfRelabeling H.target s (H.lift p) := by
  change vfRelabeling H.target s (H.lift ((vfRelabeling Y s).inverse (vfRelabeling_bijective Y s)
    (vfRelabeling Y s p))) = _
  rw [Map.inverse_apply]

theorem reindexLift_relabel_value (p : Y) :
    (reindexLift H s (vfRelabeling Y s p)).val = ((H.lift p).val.1 ∘ s, (H.lift p).val.2) := by
  rw [reindexLift_relabel]
  rfl

include h00 hc linear hκ hs hv hsmall hΓ in
theorem reindexLift_home : ProperCovariantHomeomorphism (G := G) (reindexLift H s) := by
  have hY : ProperInvariant S Y.carrier :=
    H.home.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  exact lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
      (homeo_inverse (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ Y s hY)) H.home)
    (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ H.target s H.proper)

include hfix in
theorem reindexLift_relative (p : reindexedVFSet Y s) (i : Fin N) :
    (reindexLift H s p).val.1 i.castSucc = p.val.1 i.castSucc := by
  obtain ⟨q, rfl⟩ := (vfRelabeling_bijective Y s).surjective p
  rw [reindexLift_relabel_value]
  change (H.lift q).val.1 (s i.castSucc) = q.val.1 (s i.castSucc)
  rw [← inducedPerm_castSucc s hfix i]
  exact H.relative q (inducedPerm s hfix i)

theorem reindexLift_retained (p : reindexedVFSet Y s) (i : Fin r) :
    (reindexLift H s p).val.2 (H.oldLabels i) = p.val.2 i := by
  obtain ⟨q, rfl⟩ := (vfRelabeling_bijective Y s).surjective p
  rw [reindexLift_relabel_value]
  exact H.retained q i

theorem reindexed_exceptional_subset :
    (reindexedVFSet H.exceptional s).carrier ⊆ (reindexedVFSet Y s).carrier := fun q hq =>
  (mem_reindexedVFSet Y s q).mpr (H.exceptional_subset ((mem_reindexedVFSet H.exceptional s q).mp hq))

include hc hs hsmall in
theorem reindexed_exceptional_dim :
    vfDim (rawRVSpace (M := M) 1) (reindexedVFSet H.exceptional s) < N + 1 :=
  lt_of_le_of_lt (vfDim_image_le hc hs hsmall (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1)
    (reindexVFMap H.exceptional s)) H.exceptional_dim

include h00 hc linear hκ hs hv hsmall hΓ in
theorem reindexLift_unit (p : reindexedVFSet Y s) (hp : p.val ∉ (reindexedVFSet H.exceptional s).carrier) :
    HasMixedUnitDerivativeAt (reindexLift H s) p := by
  have hY : ProperInvariant S Y.carrier :=
    H.home.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  let q := (vfRelabeling Y s).inverse (vfRelabeling_bijective Y s) p
  have hq : q.val ∉ H.exceptional.carrier := by
    intro hqE
    apply hp
    apply (mem_reindexedVFSet H.exceptional s p.val).mpr
    have he : reindexVFPoint s.symm p.val = q.val := (relabel_inverse_value Y s p).symm
    rw [he]
    exact hqE
  obtain ⟨L, hL, hdet⟩ := H.unitDerivative q hq
  have h1 := relabel_inverse_derivative hv Y s hY p
  have h2 := mixedDerivative_comp _ _ p h1 hL
  have h3 := mixedDerivative_comp _ _ p h2 (vfRelabeling_derivative hv H.target s H.proper (H.lift q))
  exact ⟨_, h3, det_conj s L hdet⟩

include h00 hc linear hκ hs hv hsmall hΓ in
/-- **The reindexed stage.** For a permutation `s` of the VF coordinates fixing the
last one, the conjugate of a standard contraction stage of `Y` by the relabellings
is a standard contraction stage of the reindexed set `Y^s`. -/
def reindexStage : StandardContractionStage (G := G) (reindexedVFSet Y s) where
  arity := H.arity
  target := reindexedVFSet H.target s
  lift := reindexLift H s
  home := reindexLift_home h00 hc linear hκ hs hv hsmall hΓ H s
  proper := reindexedVFSet_properInvariant H.target s H.proper
  doublyBounded := reindexedVFSet_doublyBounded H.target s H.doublyBounded
  relative := reindexLift_relative H s hfix
  oldLabels := H.oldLabels
  oldLabels_injective := H.oldLabels_injective
  retained := reindexLift_retained H s
  leading := H.leading
  bundle := reindexed_bundle s hfix H.target H.leading H.bundle
  exceptional := reindexedVFSet H.exceptional s
  exceptional_subset := reindexed_exceptional_subset H s
  exceptional_dim := reindexed_exceptional_dim hc hs hsmall H s
  unitDerivative := reindexLift_unit h00 hc linear hκ hs hv hsmall hΓ H s

theorem reindexStage_arity :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).arity = H.arity := rfl

theorem reindexStage_oldLabels :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).oldLabels = H.oldLabels := rfl

theorem reindexStage_leading :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).leading = H.leading := rfl

theorem reindexStage_target :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).target = reindexedVFSet H.target s := rfl

theorem reindexStage_lift :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).lift = reindexLift H s := rfl

theorem reindexStage_exceptional :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).exceptional = reindexedVFSet H.exceptional s := rfl

/-- The contracted set of the reindexed stage is the reindexing of the contracted
set of `H` by the induced permutation. -/
theorem reindexStage_contracted :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).contracted.carrier =
      (reindexedVFSet H.contracted (inducedPerm s hfix)).carrier :=
  reindexed_contracted_carrier s hfix H.target

theorem reindexStage_contracted_eq :
    (reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).contracted =
      reindexedVFSet H.contracted (inducedPerm s hfix) :=
  DefSet.eq_of_carrier_eq (reindexStage_contracted h00 hc linear hκ hs hv hsmall hΓ H s hfix)

/-- The reindexed lift at a relabelled point. -/
theorem reindexStage_lift_value (q₀ : Y) :
    ((reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).lift (vfRelabeling Y s q₀)).val =
      ((H.lift q₀).val.1 ∘ s, (H.lift q₀).val.2) :=
  reindexLift_relabel_value H s q₀

/-- The reindexed contraction at a relabelled point is the contraction of `H`,
read through the induced permutation. -/
theorem reindexStage_contraction_value (q₀ : Y) :
    ((reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).contraction (vfRelabeling Y s q₀)).val =
      ((H.contraction q₀).val.1 ∘ inducedPerm s hfix, (H.contraction q₀).val.2) := by
  rw [StandardContractionStage.contraction_value, StandardContractionStage.contraction_value]
  refine Prod.ext ?_ ?_
  · change Fin.init ((reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).lift (vfRelabeling Y s q₀)).val.1 =
      Fin.init (H.lift q₀).val.1 ∘ inducedPerm s hfix
    rw [reindexStage_lift_value, ← init_comp s hfix]
  · change ((reindexStage h00 hc linear hκ hs hv hsmall hΓ H s hfix).lift (vfRelabeling Y s q₀)).val.2 =
      (H.lift q₀).val.2
    rw [reindexStage_lift_value]

end Stage

end DiamondIntegral.Section7.StageReindexing
