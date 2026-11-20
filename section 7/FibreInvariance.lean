import «section 7».ContractionChoice
import «section 7».BaseExtension
import «section 7».GoodPoints
import «section 6».RVGraftingHomeomorphism
import «section 6».UniformMixedRadius
import «section 6».AttainableRadii
import «section 6».ContractedApertures

/-! Good points near a given point, and invariance of first-stage fibres
(for Corollary 7.15).

* `exists_good_point`: for a nonzero polynomial `P` over the VF parameter field
  of `S`, a named radius `δ` and a VF point `a`, there is `y` with entries in the
  definable closure of `S` and values above `δ` such that `P(a + y) ≠ 0`. The
  entries are powers of one named element above `δ` (the grid of the
  Combinatorial Nullstellensatz, `GoodPoints.exists_grid_nonzero_subfield`).
* `transfer_adjoin`: if every coordinate of `b` is in the definable closure of
  `S⟨a⟩`, then definability over `S⟨b⟩` implies definability over `S⟨a⟩`. So
  Section 7's classes and `μIsp^db` pass from `S⟨b⟩` to `S⟨a⟩`
  (`BaseExtension.Transfer`).
* `firstSet_uniform`: there is a named radius `δ` such that the first-stage set
  of a measured program and its induced form are unchanged when the remaining
  VF coordinates move by less than `δ`. One applies Section 6's uniform invariance
  radius to the graft of the rest-lift map, which records the RV labels that
  determine the form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.FibreInvariance
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.ContractionChoice
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.BaseExtension
open DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-! ### Good points -/

section GoodPoint
variable (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)

theorem vfValue_pow (c : VF M) (k : ℕ) : vfValue (c ^ k) = vfValue c ^ k := by
  change Values.vfValueHom (c ^ k) = Values.vfValueHom c ^ k
  exact map_pow _ _ _

theorem one_lt_vfValue {δ : Gamma M} (hδ1 : (1 : Gamma M) ≤ δ) {c : VF M} (hc : δ.val < vfValue c) :
    (1 : Values.GammaTop (M := M)) < vfValue c :=
  lt_of_le_of_lt (show (1 : Gamma M).val ≤ δ.val from hδ1) hc

theorem pow_injective_of_one_lt {c : VF M} (hc0 : c ≠ 0) (h1 : (1 : Values.GammaTop (M := M)) < vfValue c) :
    Function.Injective (fun k : ℕ => c ^ (k + 1)) := by
  have key : ∀ j k : ℕ, j < k → c ^ (j + 1) ≠ c ^ (k + 1) := by
    intro j k hjk he
    have hsplit : c ^ (k + 1) = c ^ (j + 1) * c ^ (k - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at he
    have hone : c ^ (k - j) = 1 := by
      have h0 : c ^ (j + 1) ≠ 0 := pow_ne_zero _ hc0
      have := mul_left_cancel₀ h0 (he.symm.trans (mul_one _).symm)
      exact this
    have hv1 : vfValue c ^ (k - j) = 1 := by
      rw [← vfValue_pow, hone]
      change Values.vfValueHom 1 = 1
      exact map_one _
    have hle : vfValue c ≤ vfValue c ^ (k - j) := le_self_pow h1.le (by omega)
    rw [hv1] at hle
    exact absurd h1 (not_lt.mpr hle)
  intro j k he
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key j k h he
  · exact key k j h he.symm

include h00 hc hv hV hVS hSV hnt in
/-- **A good point near `a`.** -/
theorem exists_good_point {m : ℕ} (δ : Gamma M)
    (hδdef : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) (hδ1 : (1 : Gamma M) ≤ δ)
    (P : MvPolynomial (Fin m) (vfParameterField S)) (hP : P ≠ 0) (a : Fin m → VF M) :
    ∃ y : Fin m → VF M, (∀ j, y j ∈ vfDefinableClosureField S) ∧ (∀ j, δ.val < vfValue (y j)) ∧
      P.eval₂ (vfParameterField S).subtype (a + y) ≠ 0 := by
  obtain ⟨c, hc0, hcdef, hcδ⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ1 hδdef
  have h1 := one_lt_vfValue hδ1 hcδ
  let C : Finset (VF M) := (Finset.range (P.totalDegree + 1)).image (fun k => c ^ (k + 1))
  have hcard : C.card = P.totalDegree + 1 := by
    rw [Finset.card_image_of_injective _ (pow_injective_of_one_lt hc0 h1), Finset.card_range]
  obtain ⟨y, hyC, hy⟩ := GoodPoints.exists_grid_nonzero_subfield (vfParameterField S) P hP a C (by omega)
  have hcmem : c ∈ vfDefinableClosureField S := by
    obtain ⟨σ, hσ⟩ := (mem_definableClosure_iff_raw hc S c.val).mpr hcdef
    exact (definableClosureAt_iff_raw hc S .vf c.val).mpr ⟨hσ.raw_definable, c.property⟩
  refine ⟨y, fun j => ?_, fun j => ?_, hy⟩
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hyC j)
    rw [← hk]
    exact pow_mem hcmem _
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hyC j)
    rw [← hk, vfValue_pow]
    exact hcδ.trans_le (le_self_pow h1.le (by omega))

end GoodPoint

/-! ### Passing from `S⟨b⟩` to `S⟨a⟩` -/

section Transfer
variable {T : LRV.Substructure M} {m : ℕ}

include hc in
theorem adjoin_subset_dcl (a b : Fin m → VF M) (hb : ∀ j, b j ∈ vfDefinableClosureField (adjoin T a : Set M)) :
    (adjoin T b : Set M) ⊆ definableClosure (adjoin T a : Set M) := by
  have hle : adjoin T b ≤ definableClosureSubstructure hc (adjoin T a : Set M) := by
    refine (Substructure.closure_le (L := LRV)).mpr ?_
    rintro x (hx | ⟨j, rfl⟩)
    · exact subset_definableClosure _ (subset_adjoin a hx)
    · exact ⟨.vf, hb j⟩
  exact hle

include hc in
/-- Definability over `S⟨b⟩` implies definability over `S⟨a⟩` when every
coordinate of `b` is in the definable closure of `S⟨a⟩`. -/
theorem transfer_adjoin (a b : Fin m → VF M) (hb : ∀ j, b j ∈ vfDefinableClosureField (adjoin T a : Set M)) :
    Transfer (BT (adjoin T b)) (BT (adjoin T a)) := by
  refine Transfer.ofDcl (B := BT (adjoin T b)) (C := BT (adjoin T a)) (fun x hx => ?_) (fun γ hγ => (Set.mem_empty_iff_false γ).mp hγ |>.elim)
  obtain ⟨σ, hσ⟩ := adjoin_subset_dcl hc a b hb hx
  exact ⟨σ, real_definableAtBase (BT (adjoin T a)) σ {x} hσ⟩

theorem coordinate_mem_dcl (a : Fin m → VF M) (j : Fin m) :
    a j ∈ vfDefinableClosureField (adjoin T a : Set M) :=
  definableClosureAt_of_mem (coordinate_mem_adjoin a j) (a j).property

theorem dcl_mono_adjoin {S : Set M} (hS : S ⊆ (T : Set M)) (a : Fin m → VF M) {x : VF M}
    (hx : x ∈ vfDefinableClosureField S) : x ∈ vfDefinableClosureField (adjoin T a : Set M) :=
  hx.mono (hS.trans (subset_adjoin a))

end Transfer

/-! ### Uniform invariance of first-stage sets and their forms -/

section Uniform
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {n r : ℕ} {Y : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
variable {θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S)}

include h00 hc linear hκ hs hv hsmall hΓ in
/-- **Uniform invariance.** A named radius `δ` such that moving the VF point of
the first-stage set by less than `δ` preserves membership, and the induced form
`restForm D`. -/
theorem firstSet_uniform (D : MeasuredOrderedProgram (G := G) Y θ) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ (1 : Gamma M) ≤ δ ∧
      ∀ (a b : Fin n → VF M), Congruent (fun _ => δ) a b → ∀ u,
        ∀ ha : (a, u) ∈ (headStage D.program).contracted.carrier,
          ∃ hb : (b, u) ∈ (headStage D.program).contracted.carrier,
            restForm D ⟨(b, u), hb⟩ = restForm D ⟨(a, u), ha⟩ := by
  let H := headStage D.program
  let V₁ := restLift h00 hc linear hκ hs hv hsmall hΓ D
  let τ := rvProjection V₁.map
  have hτ : ProperCovariant τ := ProperCovariant.rvProjection V₁.map V₁.home.covariant
  have hGr := graft_properInvariant h00 hc hκ hs hv τ H.contracted_proper hτ
  obtain ⟨δ, hδdef, hδ1, hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hGr
  refine ⟨δ, hδdef, hδ1, fun a b hab u ha => ?_⟩
  let p : H.contracted := ⟨(a, u), ha⟩
  have hmem : (a, Fin.append u (τ p).val.2) ∈ (graftMap hc τ).image.carrier := ⟨p, rfl⟩
  have hmem' : (b, Fin.append u (τ p).val.2) ∈ (graftMap hc τ).image.carrier :=
    (hInv (Fin.append u (τ p).val.2) a b hab).mp hmem
  obtain ⟨p', hp'⟩ := hmem'
  have hp'v : (graft hc τ p').val = (b, Fin.append u (τ p).val.2) := hp'
  rw [graft_apply] at hp'v
  have h1 : p'.val.1 = b := congrArg Prod.fst hp'v
  have h2 : p'.val.2 = u := funext fun i => by
    simpa only [Fin.append_left] using congrFun (congrArg Prod.snd hp'v) (Fin.castAdd _ i)
  have h3 : (τ p').val.2 = (τ p).val.2 := funext fun i => by
    simpa only [Fin.append_right] using congrFun (congrArg Prod.snd hp'v) (Fin.natAdd _ i)
  have hb : (b, u) ∈ H.contracted.carrier := by
    rw [← h1, ← h2]
    exact p'.property
  refine ⟨hb, ?_⟩
  have hpp : p' = ⟨(b, u), hb⟩ := Subtype.ext (Prod.ext h1 h2)
  have hmap : (restProgram D.program).toMap ⟨(b, u), hb⟩ = (restProgram D.program).toMap p := by
    apply Subtype.ext
    refine Prod.ext (funext fun i => i.elim0) ?_
    show ((restData D).program.toMap ⟨(b, u), hb⟩).val.2 = ((restData D).program.toMap p).val.2
    rw [← V₁.labels, ← V₁.labels, ← hpp]
    change (τ p').val.2 = (τ p).val.2
    exact h3
  change D.rvForm ((restProgram D.program).toMap ⟨(b, u), hb⟩) = D.rvForm ((restProgram D.program).toMap p)
  rw [hmap]

end Uniform

end DiamondIntegral.Section7.FibreInvariance
