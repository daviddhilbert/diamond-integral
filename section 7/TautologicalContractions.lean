import «section 7».OrderedProgramContractions
import «section 6».IdentityStage
import «section 6».DiamondLift

/-! Tautological contractions of RV-disc bundles (for Proposition 7.24).

Let `U ⊆ RV^q` be a proper invariant set and `ℓ` one of its labels. The RV-disc
bundle `B = rvCoordinateBundle U ℓ = {(x, w) : w ∈ U, rv(x) = w_ℓ} ⊆ VF × RV^q`
is an `RV`-pullback in its VF coordinate. Its *tautological contraction* has one
stage, the identity of `B`, with leading label `ℓ`: it contracts `x` to `w_ℓ` and
recovers `U` (`idStage`, `tautMOC`). As a normalized contraction of `(B, ρ ∘ pr)`
in the order `1` (`taut`, via `OrderedProgramContractions.ofContractionOrd`; the
bundle has no zero coordinate), its head-start class with labels `π` is the class
of every label object over `U` with the same labels `ℓ, π` up to order and the
form `ρ` (`cls_taut`).

In the proof of Proposition 7.24 (the independence `(∗)` of the contraction and
its order), the outputs of the contractions of the fibres over the first
contracted coordinate are glued into such bundles, and Lemma 7.14 with one VF
coordinate compares their tautological contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.TautologicalContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ProgramContractions DiamondIntegral.Section7.OrderedProgramContractions

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### The bundle -/

section Bundle
variable {S : Set M} {q : ℕ} (U : DefSet (rawMixedSpace (M := M) 0 q) S) (ℓ : Fin q)

theorem mem_bundle (p : Mixed M 1 q) :
    p ∈ (rvCoordinateBundle U ℓ).carrier ↔ ((Fin.elim0, p.2) : Mixed M 0 q) ∈ U.carrier ∧ rv M (p.1 0) = p.2 ℓ := by
  have he : (Fin.init p.1 : Fin 0 → VF M) = Fin.elim0 := Subsingleton.elim _ _
  change (Fin.init p.1, p.2) ∈ U.carrier ∧ rv M (p.1 (Fin.last 0)) = p.2 ℓ ↔ _
  rw [he]
  rfl

/-- A set with the carrier of the bundle has the RV target `U`. -/
theorem image_carrier_of_eq {Z : DefSet (rawMixedSpace (M := M) 1 q) S}
    (hZ : Z.carrier = (rvCoordinateBundle U ℓ).carrier) : (vfDropLast Z).image.carrier = U.carrier := by
  ext ⟨z, w⟩
  have hz : z = Fin.elim0 := funext fun i => i.elim0
  subst hz
  constructor
  · rintro ⟨p, hp⟩
    have h2 : p.val.2 = w := congrArg Prod.snd hp
    have hpz : p.val ∈ (rvCoordinateBundle U ℓ).carrier := hZ ▸ p.property
    have hm := (mem_bundle U ℓ p.val).mp hpz
    rw [h2] at hm
    exact hm.1
  · intro hw
    obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun _ : Fin 1 => w ℓ)
    have hm : ((x, w) : Mixed M 1 q) ∈ (rvCoordinateBundle U ℓ).carrier :=
      (mem_bundle U ℓ (x, w)).mpr ⟨hw, congrFun hx 0⟩
    have hmZ : ((x, w) : Mixed M 1 q) ∈ Z.carrier := by rw [hZ]; exact hm
    refine ⟨⟨_, hmZ⟩, ?_⟩
    change ((Fin.init x, w) : Mixed M 0 q) = (Fin.elim0, w)
    exact Prod.ext (Subsingleton.elim _ _) rfl

theorem bundle_doublyBounded (hU : ProperInvariant S U.carrier) : VFDoublyBounded (rvCoordinateBundle U ℓ).carrier := by
  obtain ⟨γ, hγ⟩ := hU.rvBounded
  refine ⟨γ, fun p hp i => ?_⟩
  have hm := (mem_bundle U ℓ p).mp hp
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  change (γ⁻¹).val ≤ Values.vrv (rv M (p.1 0)) ∧ Values.vrv (rv M (p.1 0)) ≤ γ.val
  rw [hm.2]
  exact hγ _ hm.1 ℓ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable (hU : ProperInvariant S U.carrier)

include h00 hc hκ hs hv hU in
theorem bundle_proper {Z : DefSet (rawMixedSpace (M := M) 1 q) S} (hZ : Z.carrier = (rvCoordinateBundle U ℓ).carrier) :
    ProperInvariant S Z.carrier := by
  rw [hZ]
  exact rvCoordinateBundle_properInvariant h00 hc hκ hs hv U ℓ hU

/-- **The identity stage** of a set with the carrier of the bundle, with leading
label `ℓ`. -/
def idStage (Z : DefSet (rawMixedSpace (M := M) 1 q) S) (hZ : Z.carrier = (rvCoordinateBundle U ℓ).carrier) :
    StandardContractionStage (G := G) Z where
  arity := q
  target := Z
  lift := Map.id Z
  home := identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ (bundle_proper U ℓ h00 hc hκ hs hv hU hZ)
  proper := bundle_proper U ℓ h00 hc hκ hs hv hU hZ
  doublyBounded := by rw [hZ]; exact bundle_doublyBounded U ℓ hU
  relative := fun _ i => i.elim0
  oldLabels := id
  oldLabels_injective := Function.injective_id
  retained := fun _ _ => rfl
  leading := ℓ
  bundle := by
    ext p
    change p ∈ Z.carrier ↔ (Fin.init p.1, p.2) ∈ (vfDropLast Z).image.carrier ∧ rv M (p.1 (Fin.last 0)) = p.2 ℓ
    rw [image_carrier_of_eq U ℓ hZ, hZ]
    rfl
  exceptional := DefSet.empty _ S
  exceptional_subset := fun _ hp => hp.elim
  exceptional_dim := DiamondIntegral.Section6.DiamondLift.vfDim_empty_lt 0
  unitDerivative := fun p _ => identity_unit_derivative (bundle_proper U ℓ h00 hc hκ hs hv hU hZ) p

theorem idStage_contracted (Z : DefSet (rawMixedSpace (M := M) 1 q) S) (hZ : Z.carrier = (rvCoordinateBundle U ℓ).carrier) :
    (idStage U ℓ h00 hc linear hκ hs hv hsmall hΓ hU Z hZ).contracted.carrier = U.carrier :=
  image_carrier_of_eq U ℓ hZ

end Bundle

/-! ### The tautological contraction -/

section Taut
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {q : ℕ} (U : DefSet (rawMixedSpace (M := M) 0 q) (T : Set M)) (ℓ : Fin q)
variable (hU : ProperInvariant (T : Set M) U.carrier)
variable (ρ : Map U (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))

/-- The projection of the bundle to `U`. -/
def bundleProj : Map (rvCoordinateBundle U ℓ) U :=
  (Map.inclusion (fun _ h => (image_carrier_of_eq U ℓ rfl ▸ h : _))).comp
    (vfDropLast (rvCoordinateBundle U ℓ)).toImage

theorem bundleProj_val (p : rvCoordinateBundle U ℓ) : (bundleProj U ℓ p).val = (Fin.init p.val.1, p.val.2) := rfl

/-- The form `ρ` read on the bundle. -/
def bundleForm : Map (rvCoordinateBundle U ℓ) (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  ρ.comp (bundleProj U ℓ)

theorem reindex_one_carrier : (reindexedVFSet (rvCoordinateBundle U ℓ) 1).carrier = (rvCoordinateBundle U ℓ).carrier := by
  ext w
  rw [mem_reindexedVFSet]
  exact Iff.rfl

/-- The identity stage on the prepared copy of the bundle. -/
abbrev tautStage : StandardContractionStage (G := G) (reindexedVFSet (rvCoordinateBundle U ℓ) 1) :=
  idStage U ℓ h00 hc linear hκ hs hv hsmall hΓ hU _ (reindex_one_carrier U ℓ)

/-- The one-stage program. -/
abbrev tautProgram : OrderedStandardContractionProgram (G := G) (T : Set M)
    (reindexedVFSet (rvCoordinateBundle U ℓ) 1) (tautStage h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).contracted :=
  .step (tautStage h00 hc linear hκ hs hv hsmall hΓ U ℓ hU) (.zero _)

/-- The RV form on the output: `ρ`. -/
def tautRVForm : Map (tautStage h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).contracted
    (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  ρ.comp (Map.inclusion (fun _ h => (idStage_contracted U ℓ h00 hc linear hκ hs hv hsmall hΓ hU _
    (reindex_one_carrier U ℓ) ▸ h : _)))

/-- **The tautological measured contraction.** -/
def tautMOC : MeasuredOrderedContraction (G := G) (reindexedVFSet (rvCoordinateBundle U ℓ) 1)
    ((tautRVForm h00 hc linear hκ hs hv hsmall hΓ U ℓ hU ρ).comp
      (tautProgram h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).toMap) where
  data :=
    { arity := q
      rvTarget := (tautStage h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).contracted
      program := tautProgram h00 hc linear hκ hs hv hsmall hΓ U ℓ hU
      rvForm := tautRVForm h00 hc linear hκ hs hv hsmall hΓ U ℓ hU ρ
      factor := fun _ => rfl }
  lift := Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
    (reindexedVFSet_properInvariant _ 1 (rvCoordinateBundle_properInvariant h00 hc hκ hs hv U ℓ hU)))

/-- **The tautological contraction** of the bundle, as a normalized contraction in
the order `1`. -/
def taut (D : ZeroCenteredData (rvCoordinateBundle U ℓ)) :
    NormalizedMeasuredContraction (G := G) (rvCoordinateBundle U ℓ) (bundleForm U ℓ ρ) 1 :=
  ofContractionOrd h00 hc linear hκ hs hv hsmall hΓ D (fun _ hp i => (bundle_doublyBounded U ℓ hU).nonzero hp i) 1
    (tautMOC h00 hc linear hκ hs hv hsmall hΓ U ℓ hU ρ) (fun _ => rfl)

theorem tautProgram_volumeIndex :
    (tautProgram h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).volumeIndex = ![ℓ] := by
  funext i
  rw [Fin.fin_one_eq_zero i]
  change (OrderedStandardContractionProgram.step _ _).volumeIndex (Fin.last 0) = _
  rw [OrderedStandardContractionProgram.volumeIndex_step_last]
  rfl

theorem tautProgram_oldLabels : (tautProgram h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).oldLabels = id := rfl

/-- **The class of the tautological contraction.** Its head-start class with
labels `π` is the class of every label object over `U` whose labels are `ℓ, π`
up to order, with the form `ρ`. -/
theorem cls_taut (D : ZeroCenteredData (rvCoordinateBundle U ℓ)) {k : ℕ} (π : Fin k → Fin q)
    (hFin : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin q → RVInfinity M | (a, u) ∈ (rvCoordinateBundle U ℓ).carrier ∧ u ∘ π = t}.Finite)
    {a kX : ℕ} {X : DefSet (rawMixedSpace (M := M) a q) (T : Set M)} {ν : Fin a → Fin q} (h : a + kX = 1 + k)
    (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (ν i))
    (lX : Fin kX → Fin q)
    (hprod : ∀ f : Fin q → Gamma M, ∏ i, f (Fin.append ν lX i) = ∏ i, f (Fin.append ![ℓ] π i))
    (hTX : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1) (hfinX hnzX)
    (ηX : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (hηX)
    (hρX : ∀ (p : X) (z : U), z.val.2 = p.val.2 → (ηX p).val = (ρ z).val)
    (hdX : (labelObject X kX lX hTX hfinX hnzX ηX hηX).doublyBounded) :
    cls (objOf hc T (labelObject X kX lX hTX hfinX hnzX ηX hηX) hdX) =
      castCls h.symm (cls (objOf hc T ((taut h00 hc linear hκ hs hv hsmall hΓ U ℓ hU ρ D).headStartMeasuredObject h00 hc
        linear hκ hs hv hsmall hΓ k π hFin)
        ((taut h00 hc linear hκ hs hv hsmall hΓ U ℓ hU ρ D).headStartObject_doublyBounded k π))) := by
  let C := tautMOC h00 hc linear hκ hs hv hsmall hΓ U ℓ hU ρ
  have hFinE : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin q → RVInfinity M | (a, u) ∈ (reindexedVFSet (rvCoordinateBundle U ℓ) 1).carrier ∧ u ∘ π = t}.Finite := by
    intro a t
    refine (hFin a t).subset ?_
    rintro u ⟨hu, hut⟩
    rw [reindex_one_carrier] at hu
    exact ⟨hu, hut⟩
  have e := cls_ofContractionOrd (ω := bundleForm U ℓ ρ) h00 hc linear hκ hs hv hsmall hΓ D
    (fun _ hp i => (bundle_doublyBounded U ℓ hU).nonzero hp i) 1 C (fun _ => rfl) k π hFin hFinE
  have hY : ∀ p : Mixed M 1 q, p ∈ C.lift.target.carrier ↔
      (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (C.data.program.volumeIndex i) := by
    intro p
    rw [C.lift.recover p]
    change (Fin.elim0, p.2) ∈ (tautStage h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).contracted.carrier ∧ _ ↔ _
    rw [idStage_contracted]
  have hprod' : ∀ f : Fin q → Gamma M,
      ∏ i, f (Fin.append ν lX i) = ∏ i, f (Fin.append C.data.program.volumeIndex (C.data.program.oldLabels ∘ π) i) := by
    intro f
    rw [hprod f]
    change ∏ i, f (Fin.append ![ℓ] π i) = ∏ i, f (Fin.append (tautProgram h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).volumeIndex
      ((tautProgram h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).oldLabels ∘ π) i)
    rw [tautProgram_volumeIndex, tautProgram_oldLabels]
    rfl
  refine Eq.trans ?_ (congrArg (castCls h.symm) e.symm)
  exact cls_labelObject_eq hc h hX hY lX (C.data.program.oldLabels ∘ π) hprod' ρ hTX _ hfinX _ hnzX _ ηX hηX C.form
    C.form_same_tags hρX (fun p z hz => by
      have he : ((Fin.elim0, p.val.2) : Mixed M 0 q) = z.val := Prod.ext (funext fun i => i.elim0) hz.symm
      have hmem : ((Fin.elim0, p.val.2) : Mixed M 0 q) ∈ C.data.rvTarget.carrier := by
        change _ ∈ (tautStage h00 hc linear hκ hs hv hsmall hΓ U ℓ hU).contracted.carrier
        rw [idStage_contracted, he]
        exact z.property
      refine (rvForm_read _ _ (fun _ => rfl) p ⟨_, hmem⟩ rfl).trans ?_
      exact congrArg (fun y => (ρ y).val) (Subtype.ext he))
    hdX _

end Taut

end DiamondIntegral.Section7.TautologicalContractions
