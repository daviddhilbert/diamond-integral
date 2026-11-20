import «section 7».FirstStage
import «section 6».InitialPreparation
import «section 6».ZeroCenteredBoundedTrace
import «section 6».ZeroCenteredHomeomorphism
import «section 6».ZeroCenteredGeometry
import «section 6».FiniteRVFiberTransport
import «section 6».FixedVFStagePrecomposition
import «section 6».InvarianceTopology

/-! Choosing standard contractions for Corollary 7.15.

* `exists_common_center`: two proper invariant sets admit zero-centred
  normalizations with the same centre. One takes a centre above both uniform
  invariance radii.
* `exists_contraction_with`: a measured standard contraction exists with any
  prescribed normalization, in any coordinate order. This is Section 6's
  `measured_contraction_any_order` with the normalization given.
* First-stage sets: the first-stage set of a contraction of a set with finite RV
  fibres has finite fibres over the leading label (`firstStage_finite`); the
  leading label never vanishes (`firstStage_nonzero`); the induced form has open
  level sets (`restForm_levels`).
* `graftRest`: a normalized contraction `H` of the first-stage set, in the
  identity order, can be put after the first stage. The normalization of a
  doubly bounded set fixes every VF coordinate (Section 6's
  `point_field_of_doublyBounded`). So `H`'s program pulls back to the
  first-stage set itself (`precomposeFixedVF`), and the head-start-`0` class of
  the grafted contraction is the head-start-`1` class of `H`
  (`cls_graftRest`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ContractionChoice
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-! ### A common centre -/

section Center
variable (V S : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include h00 hc linear hκ hs hv hsmall hΓ hV hVS hSV hnt in
/-- Two proper invariant sets have zero-centred normalizations with a common
centre. -/
theorem exists_common_center {n r' r'' : ℕ}
    (A' : DefSet (rawMixedSpace (M := M) n r') S) (A'' : DefSet (rawMixedSpace (M := M) n r'') S)
    (hA' : ProperInvariant S A'.carrier) (hA'' : ProperInvariant S A''.carrier) :
    ∃ (D' : ZeroCenteredData A') (D'' : ZeroCenteredData A''), D'.center = D''.center := by
  obtain ⟨δ', hδ', hδ0', hInv'⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA'
  obtain ⟨δ'', hδ'', hδ0'', hInv''⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA''
  obtain ⟨c', hc0', hcdef', hcδ'⟩ :=
    exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ' hδ0' hδ'
  obtain ⟨c'', hc0'', hcdef'', hcδ''⟩ :=
    exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ'' hδ0'' hδ''
  by_cases hle : vfValue c'' ≤ vfValue c'
  · exact ⟨⟨hA', c', hc0', hcdef', fun u => (hInv' u).larger_radius (fun _ => hcδ'.le)⟩,
      ⟨hA'', c', hc0', hcdef', fun u => (hInv'' u).larger_radius (fun _ => (hcδ''.trans_le hle).le)⟩, rfl⟩
  · have hlt : vfValue c' < vfValue c'' := lt_of_not_ge hle
    exact ⟨⟨hA', c'', hc0'', hcdef'', fun u => (hInv' u).larger_radius (fun _ => (hcδ'.trans hlt).le)⟩,
      ⟨hA'', c'', hc0'', hcdef'', fun u => (hInv'' u).larger_radius (fun _ => hcδ''.le)⟩, rfl⟩

include h00 hc linear hκ hs hv hsmall hΓ hV hVS hSV hnt in
/-- A measured standard contraction with a prescribed normalization, in any
coordinate order. -/
theorem exists_contraction_with {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) (n + 1) r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin (n + 1) → VF M | (a, u) ∈ A.carrier ∧ gammaFormExtension ω (a, u) = γ})
    (e : Equiv.Perm (Fin (n + 1))) (D : ZeroCenteredData A) :
    ∃ F : NormalizedMeasuredContraction (G := G) A ω e, F.normalization = D := by
  let d := D.bijection
  have hd : SpecialCovariantChain (G := G) A D.map.image d := .zeroCentered A D
  let η := ω.comp (d.inverse (D.bijective h00))
  have hTransportD (p : A) : (η (d p)).val = (ω p).val := by
    change (ω (d.inverse (D.bijective h00) (d p))).val = _
    rw [Map.inverse_apply]
  have hLevelsD := hd.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels η hTransportD
  let E := vfRelabeling D.map.image e
  let θ := η.comp (E.inverse (vfRelabeling_bijective D.map.image e))
  have hLevelsE := vfRelabeling_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ D.map.image e
    (D.image_properInvariant h00 hc hκ hs hv) η hLevelsD
  obtain ⟨F⟩ := measured_ordered_contraction_all_dimensions (G := G) h00 hc linear hκ hs hv V hsmall hΓ hV hVS
    hSV hnt (reindexedVFSet D.map.image e)
    (reindexedVFSet_properInvariant D.map.image e (D.image_properInvariant h00 hc hκ hs hv))
    (reindexedVFSet_doublyBounded D.map.image e D.image_vfDoublyBounded) θ hLevelsE
  refine ⟨⟨D, θ, fun p => ?_, F⟩, rfl⟩
  change (η (E.inverse (vfRelabeling_bijective D.map.image e) (E (d p)))).val = (ω p).val
  rw [Map.inverse_apply]
  exact hTransportD p

end Center

/-! ### First-stage sets -/

section FirstStageSets
variable {S : Set M} {n r : ℕ} {Y : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
variable {θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S)}

include hc h00 hκ hs in
/-- Finite fibres over the leading label on the first-stage set, from finite
RV fibres of the source. -/
theorem firstStage_finite (hsmall : Cardinal.mk S < κ) (D : MeasuredOrderedProgram (G := G) Y θ)
    (hY : ∀ a : Fin (n + 1) → VF M, {u : Fin r → RVInfinity M | (a, u) ∈ Y.carrier}.Finite)
    (b : Fin n → VF M) (t : Fin 1 → RVInfinity M) :
    {u | (b, u) ∈ (headStage D.program).contracted.carrier ∧ u ∘ ![(headStage D.program).leading] = t}.Finite := by
  have hT := finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall (headStage D.program).lift
    (headStage D.program).home.bijective hY
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) t
  refine (hT (Fin.snoc b (x 0))).subset ?_
  rintro u ⟨hu, ht⟩
  apply ((headStage D.program).recover_target (Fin.snoc b (x 0), u)).mpr
  refine ⟨by simpa only [Fin.init_snoc] using hu, ?_⟩
  change rv M (Fin.snoc (α := fun _ => VF M) b (x 0) (Fin.last n)) = u (headStage D.program).leading
  rw [Fin.snoc_last]
  have h1 := congrFun hx 0
  have h2 := congrFun ht 0
  simp only [Function.comp_apply, Matrix.cons_val_zero] at h2
  exact h1.trans h2.symm

/-- The leading label of the first-stage set never vanishes. -/
theorem firstStage_nonzero (D : MeasuredOrderedProgram (G := G) Y θ) :
    ∀ p ∈ (headStage D.program).contracted.carrier, ∀ i : Fin 1,
      (p.2 (![(headStage D.program).leading] i)).val ≠ iRVZero := by
  rintro _ ⟨q, rfl⟩ i
  have hq := ((headStage D.program).recover_target q.val).mp q.property
  intro he
  have hrv : rv M (q.val.1 (Fin.last n)) = q.val.2 (headStage D.program).leading := by
    simpa only [Fin.init_snoc] using hq.2
  have h0 : (rv M (q.val.1 (Fin.last n))).val = iRVZero := by
    rw [hrv]
    simpa only [Matrix.cons_val_fin_one, vfDropLast_apply] using he
  exact (headStage D.program).doublyBounded.nonzero q.property (Fin.last n)
    ((rv_eq_zero_iff _).mp (Subtype.ext h0))

theorem isOpenMap_init : IsOpenMap (fun a : Fin (n + 1) → VF M => Fin.init a) := by
  refine IsOpenMap.of_sections fun x => ⟨fun b => Fin.snoc (α := fun _ => VF M) b (x (Fin.last n)), ?_, ?_, ?_⟩
  · exact (continuous_id.finSnoc continuous_const).continuousAt
  · exact Fin.snoc_init_self x
  · intro b
    exact Fin.init_snoc _ _

include hv in
/-- The form induced on the first-stage set has open level sets. -/
theorem restForm_levels (D : MeasuredOrderedProgram (G := G) Y θ)
    (hLevels : ∀ u γ, IsOpen {a : Fin (n + 1) → VF M | (a, u) ∈ Y.carrier ∧ gammaFormExtension θ (a, u) = γ}) :
    ∀ u₁ γ, IsOpen {a : Fin n → VF M | (a, u₁) ∈ (headStage D.program).contracted.carrier ∧
      gammaFormExtension (restForm D) (a, u₁) = γ} := by
  intro u₁ γ
  let H := headStage D.program
  let u : Fin r → RVInfinity M := fun i => u₁ (H.oldLabels i)
  obtain ⟨α, β, -, -, hα, -⟩ := H.home.covariant.radii u u₁
  have hR : IsOpen (graphFibreSource H.lift u u₁) := hα.isOpen hv
  have hS : IsOpen ({a : Fin (n + 1) → VF M | (a, u) ∈ Y.carrier ∧ gammaFormExtension θ (a, u) = γ} ∩
      graphFibreSource H.lift u u₁) :=
    (hLevels u γ).inter hR
  convert isOpenMap_init _ hS using 1
  ext a'
  constructor
  · rintro ⟨hA, hγ⟩
    obtain ⟨q, hq⟩ := hA
    obtain ⟨p, hp⟩ := H.home.bijective.surjective q
    have hq' : (vfDropLast H.target q).val = (a', u₁) := hq
    have hq1 : Fin.init q.val.1 = a' := congrArg Prod.fst hq'
    have hq2 : q.val.2 = u₁ := congrArg Prod.snd hq'
    have hpa : Fin.init p.val.1 = a' := by
      rw [← hq1, ← hp]
      funext j
      exact (H.relative p j).symm
    have hpu : p.val.2 = u := by
      funext i
      rw [← H.retained p i, hp, hq2]
    have hcp : H.contraction p = ⟨(a', u₁), ⟨q, hq⟩⟩ := by
      apply Subtype.ext
      change (vfDropLast H.target (H.lift p)).val = (a', u₁)
      rw [hp]
      exact hq'
    refine ⟨p.val.1, ⟨⟨?_, ?_⟩, ⟨(H.lift p).val.1, p, Prod.ext rfl hpu, Prod.ext rfl ?_⟩⟩, hpa⟩
    · rw [← hpu]
      exact p.property
    · have key : gammaFormExtension θ (p.val.1, u) = gammaFormExtension θ p.val := by
        congr 1
        exact Prod.ext rfl hpu.symm
      calc gammaFormExtension θ (p.val.1, u) = (θ p).val := key.trans (gammaFormExtension_at θ p)
        _ = (restForm D ⟨(a', u₁), ⟨q, hq⟩⟩).val := by rw [← hcp]; exact (restForm_contraction D p).symm
        _ = gammaFormExtension (restForm D) (a', u₁) := (gammaFormExtension_at (restForm D) ⟨_, ⟨q, hq⟩⟩).symm
        _ = γ := hγ
    · change (H.lift p).val.2 = u₁
      rw [hp]
      exact hq2
  · rintro ⟨a, ⟨⟨haY, hγ⟩, ⟨b, p, hp1, hp2⟩⟩, rfl⟩
    have hpa : p.val.1 = a := congrArg Prod.fst hp1
    have hb : Fin.init (H.lift p).val.1 = Fin.init a := by
      funext j
      rw [← hpa]
      exact H.relative p j
    have hl2 : (H.lift p).val.2 = u₁ := congrArg Prod.snd hp2
    have hmem : (Fin.init a, u₁) ∈ H.contracted.carrier := by
      refine ⟨H.lift p, ?_⟩
      show (vfDropLast H.target (H.lift p)).val = (Fin.init a, u₁)
      rw [vfDropLast_apply, hb, hl2]
    have hcp : H.contraction p = ⟨(Fin.init a, u₁), hmem⟩ := by
      apply Subtype.ext
      rw [StandardContractionStage.contraction_value, hb, hl2]
    refine ⟨hmem, ?_⟩
    calc gammaFormExtension (restForm D) (Fin.init a, u₁) = (restForm D ⟨(Fin.init a, u₁), hmem⟩).val :=
          gammaFormExtension_at (restForm D) ⟨_, hmem⟩
      _ = (θ p).val := by rw [← hcp]; exact restForm_contraction D p
      _ = gammaFormExtension θ (a, u) := by rw [← hp1]; exact (gammaFormExtension_at θ p).symm
      _ = γ := hγ

end FirstStageSets

/-! ### Programs pulled back along a VF-fixing map -/

section Precompose
variable {S : Set M} {n r s q : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S} {B : DefSet (rawMixedSpace (M := M) (n + 1) s) S}
variable {U : DefSet (rawMixedSpace (M := M) 0 q) S}

theorem precomposeFixedVF_volumeIndex (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (T : OrderedStandardContractionProgram (G := G) S B U) (g : Map A B) (hG : ProperCovariantHomeomorphism g)
    (hVF : ∀ p : A, (g p).val.1 = p.val.1) (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A, ∀ i, (g p).val.2 (π i) = p.val.2 i)
    (hUnit : ∀ p : A, HasMixedUnitDerivativeAt g p) :
    (T.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ g hG hVF π hπ hRetain hUnit).volumeIndex =
      T.volumeIndex := by
  match T with
  | .step R tail => rfl

theorem precomposeFixedVF_oldLabels (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    (T : OrderedStandardContractionProgram (G := G) S B U) (g : Map A B) (hG : ProperCovariantHomeomorphism g)
    (hVF : ∀ p : A, (g p).val.1 = p.val.1) (π : Fin r → Fin s) (hπ : Function.Injective π)
    (hRetain : ∀ p : A, ∀ i, (g p).val.2 (π i) = p.val.2 i)
    (hUnit : ∀ p : A, HasMixedUnitDerivativeAt g p) (i : Fin r) :
    (T.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ g hG hVF π hπ hRetain hUnit).oldLabels i =
      T.oldLabels (π i) := by
  match T with
  | .step R tail => rfl

end Precompose

/-! ### Grafting a contraction of the first-stage set -/

section Graft
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1 + 1))}

/-- The first stage of a normalized contraction. -/
abbrev stage (F : NormalizedMeasuredContraction (G := G) A ω e) := headStage F.preparedContraction.data.program

/-- The first-stage set of a normalized contraction. -/
abbrev firstSet (F : NormalizedMeasuredContraction (G := G) A ω e) := (stage F).contracted

/-- The form induced on the first-stage set. -/
abbrev firstForm (F : NormalizedMeasuredContraction (G := G) A ω e) := restForm F.preparedContraction.data

include hv in
theorem relabel_one_unit {m s : ℕ} (X : DefSet (rawMixedSpace (M := M) m s) (T : Set M))
    (hX : ProperInvariant (T : Set M) X.carrier) (p : X) :
    HasMixedUnitDerivativeAt (vfRelabeling X 1) p := by
  refine ⟨vfReindexLinear 1, vfRelabeling_derivative hv X 1 hX p, ?_⟩
  have h : (vfReindexLinear (M := M) (1 : Equiv.Perm (Fin m))) = LinearMap.id := by
    refine LinearMap.ext fun x => funext fun i => ?_
    rw [vfReindexLinear_apply]
    rfl
  rw [h, LinearMap.toMatrix'_id, Matrix.det_one]

variable (F : NormalizedMeasuredContraction (G := G) A ω e)
variable (H : NormalizedMeasuredContraction (G := G) (firstSet F) (firstForm F) 1)

/-- The normalization of the first-stage set followed by the identity
relabeling. -/
def pad : Map (firstSet F) (reindexedVFSet H.normalization.map.image 1) :=
  (vfRelabeling H.normalization.map.image 1).comp H.normalization.bijection

theorem pad_vf (p : firstSet F) : (pad F H p).val.1 = p.val.1 := by
  change (H.normalization.point p.val).1 ∘ ⇑(1 : Equiv.Perm (Fin (n + 1))) = p.val.1
  rw [H.normalization.point_field_of_doublyBounded (stage F).contracted_doublyBounded p.property]
  rfl

theorem pad_retain (p : firstSet F) (i : Fin (stage F).arity) :
    (pad F H p).val.2 (Fin.natAdd (n + 1) i) = p.val.2 i := by
  change (H.normalization.point p.val).2 (Fin.natAdd (n + 1) i) = p.val.2 i
  change Fin.append (fun j => branchTag (M := M) (H.normalization.core p.val j)) p.val.2 (Fin.natAdd (n + 1) i) = _
  rw [Fin.append_right]

theorem natAdd_injective' : Function.Injective (Fin.natAdd (n + 1) : Fin (stage F).arity → Fin (n + 1 + (stage F).arity)) :=
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)

include h00 hc linear hκ hs hv hsmall hΓ in
theorem pad_home : ProperCovariantHomeomorphism (pad F H) :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (H.normalization.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ)
    (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ _ 1
      (H.normalization.image_properInvariant h00 hc hκ hs hv))

include h00 hc hκ hs hv in
theorem pad_unit (p : firstSet F) : HasMixedUnitDerivativeAt (pad F H) p :=
  (relabel_one_unit hv _ (H.normalization.image_properInvariant h00 hc hκ hs hv) _).comp
    (H.normalization.unit_derivative hv p)

/-- `H`'s program, pulled back to the first-stage set. -/
def pulledProgram :=
  H.preparedContraction.data.program.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ (pad F H)
    (pad_home h00 hc linear hκ hs hv hsmall hΓ F H) (pad_vf F H) (Fin.natAdd (n + 1)) (natAdd_injective' F)
    (pad_retain F H) (pad_unit h00 hc hκ hs hv F H)

/-- The measured program: the first stage of `F`, then `H`'s program. -/
def graftData : MeasuredOrderedProgram (G := G) (reindexedVFSet F.normalization.map.image e) F.preparedForm where
  arity := H.preparedContraction.data.arity
  rvTarget := H.preparedContraction.data.rvTarget
  program := .step (stage F) (pulledProgram h00 hc linear hκ hs hv hsmall hΓ F H)
  rvForm := H.preparedContraction.data.rvForm
  factor p := by
    change (H.preparedContraction.data.rvForm
      ((pulledProgram h00 hc linear hκ hs hv hsmall hΓ F H).toMap ((stage F).contraction p))).val = _
    rw [pulledProgram, OrderedStandardContractionProgram.precomposeFixedVF_toMap]
    change (H.preparedContraction.data.rvForm
      (H.preparedContraction.data.program.toMap (pad F H ((stage F).contraction p)))).val = _
    rw [H.preparedContraction.data.factor]
    exact (H.transport ((stage F).contraction p)).trans (restForm_contraction F.preparedContraction.data p)

/-- **Grafting.** The normalized contraction of `A` with `F`'s normalization and
first stage, followed by `H`'s program on the first-stage set. -/
def graftRest : NormalizedMeasuredContraction (G := G) A ω e where
  normalization := F.normalization
  preparedForm := F.preparedForm
  transport := F.transport
  preparedContraction := ⟨graftData h00 hc linear hκ hs hv hsmall hΓ F H,
    Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
      (reindexedVFSet_properInvariant _ e (F.normalization.image_properInvariant h00 hc hκ hs hv)))⟩

theorem graftRest_restProgram :
    restProgram (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data.program =
      pulledProgram h00 hc linear hκ hs hv hsmall hΓ F H := rfl

/-- **The grafted class.** The head-start-`0` class of the grafted contraction is
the head-start-`1` class of `H`, with the leading label of the first stage. -/
theorem cls_graftRest
    (hFin : ∀ a : Fin (n + 1 + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite)
    (hFinH : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 1 → RVInfinity M,
      {u | (a, u) ∈ (firstSet F).carrier ∧ u ∘ ![(stage F).leading] = t}.Finite) :
    cls (objOf hc T ((graftRest h00 hc linear hκ hs hv hsmall hΓ F H).headStartMeasuredObject h00 hc linear hκ hs hv
        hsmall hΓ 0 Fin.elim0 hFin) ((graftRest h00 hc linear hκ hs hv hsmall hΓ F H).headStartObject_doublyBounded 0
          Fin.elim0)) =
      cls (objOf hc T (H.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 1 ![(stage F).leading] hFinH)
        (H.headStartObject_doublyBounded 1 ![(stage F).leading])) := by
  rw [cls_headStart_rest h00 hc linear hκ hs hv hsmall hΓ]
  have h : cls (objOf hc T (restObject h00 hc linear hκ hs hv hsmall hΓ
        (graftRest h00 hc linear hκ hs hv hsmall hΓ F H) 0 Fin.elim0 hFin)
        (restObject_doublyBounded h00 hc linear hκ hs hv hsmall hΓ _ 0 Fin.elim0 hFin)) =
      cls (objOf hc T (H.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 1 ![(stage F).leading] hFinH)
        (H.headStartObject_doublyBounded 1 ![(stage F).leading])) :=
    cls_labelObject_eq hc (show (n + 1) + (0 + 1) = (n + 1) + 1 from rfl)
      (restLift h00 hc linear hκ hs hv hsmall hΓ
        (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data).recover
      H.preparedContraction.lift.originalTarget_recover _ _ (by
        intro f
        refine Finset.prod_congr rfl (fun i _ => congrArg f ?_)
        induction i using Fin.addCases with
        | left i =>
          rw [Fin.append_left, Fin.append_left]
          exact congrFun (precomposeFixedVF_volumeIndex h00 hc linear hκ hs hv hsmall hΓ
            H.preparedContraction.data.program _ _ _ _ _ _ _) i
        | right j =>
          rw [Fin.append_right, Fin.append_right, Fin.fin_one_eq_zero j]
          change (restProgram (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data.program).oldLabels
              (restLabels (graftRest h00 hc linear hκ hs hv hsmall hΓ F H) Fin.elim0 0) =
            H.preparedContraction.data.program.oldLabels (Fin.natAdd (n + 1) (stage F).leading)
          exact precomposeFixedVF_oldLabels h00 hc linear hκ hs hv hsmall hΓ
            H.preparedContraction.data.program _ _ _ _ _ _ _ _)
      H.preparedContraction.data.rvForm _ _ _ _ _ _
      (restContraction h00 hc linear hκ hs hv hsmall hΓ
        (graftRest h00 hc linear hκ hs hv hsmall hΓ F H).preparedContraction.data).form _ H.form _
      (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
      (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _
  exact h

end Graft

end DiamondIntegral.Section7.ContractionChoice
