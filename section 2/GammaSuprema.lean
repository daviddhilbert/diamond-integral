import «section 2».Boundedness
import Section3.GammaThresholdGeometry
import Section3.GammaFiniteOrder

/-!
# Definable completeness of the actual value group

The value group is not assumed Dedekind complete. A nonempty definable
subset with an upper bound has a finite supremum because its cuts are
determined by finitely many actual Gamma thresholds. The dual argument
gives infima. These are the extrema used in the author's induction in 2.41.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_definable_exists_isGLB (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (A : Set (Gamma M))
    (hA : GammaParameters.GammaDefinableOverBase B A)
    (hne : A.Nonempty) (hbounded : BddBelow A) :
    ∃ c : Gamma M, IsGLB A c := by
  obtain ⟨E, hE⟩ := GammaParameters.gamma_definable_finite_thresholds h00 B A hA
  obtain ⟨c, hc, _⟩ := FiniteThresholds.exists_infimum E A hE hne hbounded
  exact ⟨c, hc⟩

theorem gamma_definable_exists_isLUB (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (A : Set (Gamma M))
    (hA : GammaParameters.GammaDefinableOverBase B A)
    (hne : A.Nonempty) (hbounded : BddAbove A) :
    ∃ c : Gamma M, IsLUB A c := by
  obtain ⟨E, hE⟩ := GammaParameters.gamma_definable_finite_thresholds h00 B A hA
  have hd : @FiniteThresholds.Determines (OrderDual (Gamma M)) inferInstance E A := by
    intro x y hxy
    exact hE x y (fun c hc => ⟨(hxy c hc).2, (hxy c hc).1⟩)
  obtain ⟨c, hc, _⟩ := FiniteThresholds.exists_infimum
    (α := OrderDual (Gamma M)) E A hd hne hbounded
  exact ⟨c, hc⟩

theorem gamma_definable_exists_unique_isLUB (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (A : Set (Gamma M))
    (hA : GammaParameters.GammaDefinableOverBase B A)
    (hne : A.Nonempty) (hbounded : BddAbove A) :
    ∃! c : Gamma M, IsLUB A c := by
  obtain ⟨c, hc⟩ := gamma_definable_exists_isLUB h00 B A hA hne hbounded
  exact ⟨c, hc, fun _ hd => hd.unique hc⟩

private def upperCodes (U : Set M) : Set M :=
  {t | GammaParameters.NonzeroRV t ∧ ∀ u ∈ U, iLe u t}

omit hM in
/-- The reversed comparison is the same well-sorted atomic construction
as `GammaParameters.not_le_pair_definable`, with its two inputs exchanged. -/
private theorem reversed_not_le_definable (S : Set M) :
    DefinableOver S (fun _ : Fin 2 => .rv)
      {z | (∀ i, iRV (z i)) ∧ ¬ iLe (z 1) (z 0)} := by
  let p : Parameters S := ⟨0, Fin.elim0, (fun _ => .vf),
    (fun i => i.elim0), (fun i => i.elim0)⟩
  let ts : Fin 2 → LRV.Term (Fin 0 ⊕ Fin 2) := ![.var (.inr 1), .var (.inr 0)]
  let φ : LRV.BoundedFormula (Fin 0) 2 := (BoundedFormula.rel Rel.rvLe ts).not
  have hw : WellSorted p.sorts (fun _ : Fin 2 => .rv) φ := by
    apply wellSorted_not
    apply WellSorted.rel
    intro i
    fin_cases i <;> rfl
  refine ⟨p, φ, hw, ?_⟩
  ext z
  have he : (fun i => (ts i).realize (Sum.elim (Fin.elim0 : Fin 0 → M) z)) =
      (![z 1, z 0] : Fin 2 → M) := by
    funext i
    fin_cases i <;> rfl
  change ((∀ i, iRV (z i)) ∧ ¬ iLe (z 1) (z 0)) ↔
    (∀ i, iRV (z i)) ∧ ¬ Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => (ts i).realize (Sum.elim (Fin.elim0 : Fin 0 → M) z))
  rw [he]
  rfl

private theorem upperCodes_definable (B : ParameterBase M) (U : Set M)
    (hU : GammaParameters.DefinableAtBase B .rv U) :
    GammaParameters.DefinableAtBase B .rv (upperCodes U) := by
  let bad : Set M := {t | iRV t ∧ ∃ u ∈ U, ¬ iLe u t}
  have hbad : GammaParameters.DefinableAtBase B .rv bad := by
    have hU2 := hU.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (1 : Fin 2))
    have hR := GammaParameters.real_definableOverBase B _ _
      (reversed_not_le_definable B.real)
    have hp := (hU2.inter hR).image_real (fun _ : Fin 1 => (0 : Fin 2))
    change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
      {z | z 0 ∈ bad}
    convert hp using 1
    all_goals try rfl
    ext z
    change (iRV (z 0) ∧ ∃ u ∈ U, ¬ iLe u (z 0)) ↔ ∃ w,
      ((w 1 ∈ U ∧ w ∈ GammaParameters.sortedUniverse (fun _ : Fin 2 => .rv)) ∧
        ((∀ i, iRV (w i)) ∧ ¬ iLe (w 1) (w 0))) ∧
      w ∘ (fun _ : Fin 1 => (0 : Fin 2)) = z
    constructor
    · rintro ⟨hz, u, hu, hn⟩
      have hs : ∀ i, iRV ((![z 0, u] : Fin 2 → M) i) := by
        intro i
        fin_cases i
        · exact hz
        · exact hU.proper u hu
      refine ⟨![z 0, u], ⟨⟨hu, hs⟩, ⟨hs, hn⟩⟩, ?_⟩
      funext i
      fin_cases i
      rfl
    · rintro ⟨w, ⟨⟨hu, hs⟩, _, hn⟩, he⟩
      have hz : w 0 = z 0 := congrFun he 0
      rw [← hz]
      exact ⟨hs 0, w 1, hu, hn⟩
  have hN : DefinableAt B.real .rv {t | GammaParameters.NonzeroRV t} :=
    (definableAt_iff_normalized_raw B.real .rv _).mpr
      ⟨GammaParameters.nonzero_codes_normalized_definable B.real, fun _ hx => hx.1⟩
  have h := (GammaParameters.real_definableAtBase B .rv _ hN).inter hbad.compl
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ upperCodes U}
  convert h using 1
  ext z
  change (GammaParameters.NonzeroRV (z 0) ∧ ∀ u ∈ U, iLe u (z 0)) ↔
    GammaParameters.NonzeroRV (z 0) ∧ ((∀ i : Fin 1, iRV (z i)) ∧ z 0 ∉ bad)
  constructor
  · rintro ⟨hz, hle⟩
    refine ⟨hz, ?_, ?_⟩
    · intro i
      fin_cases i
      exact hz.1
    · rintro ⟨_, u, hu, hn⟩
      exact hn (hle u hu)
  · rintro ⟨hz, _, hn⟩
    refine ⟨hz, fun u hu => ?_⟩
    by_contra hnot
    exact hn ⟨hz.1, u, hu, hnot⟩

private theorem upperCodes_mem_iff (A : Set (Gamma M)) (t : M)
    (ht : GammaParameters.NonzeroRV t) :
    t ∈ upperCodes (Values.gammaPullback A) ↔
      GammaParameters.codeValue t ∈ upperBounds A := by
  constructor
  · rintro ⟨_, h⟩ a ha
    obtain ⟨u, hu, heu⟩ := GammaParameters.EndpointLogic.codeValue_surjective a
    have huA : u ∈ Values.gammaPullback A :=
      (GammaParameters.gammaPullback_mem_codeValue_iff A u hu).mpr (heu.symm ▸ ha)
    have hle := (GammaParameters.original_le_codeValue_iff u t hu ht).mp (h u huA)
    rwa [heu] at hle
  · intro h
    refine ⟨ht, fun u huA => ?_⟩
    have hu : GammaParameters.NonzeroRV u := ⟨huA.1, huA.2.1⟩
    apply (GammaParameters.original_le_codeValue_iff u t hu ht).mpr
    exact h ((GammaParameters.gammaPullback_mem_codeValue_iff A u hu).mp huA)

/-- The finite supremum is definable over the original real/Gamma base.
The construction uses all nonzero RV codes, never a chosen representative. -/
theorem gamma_isLUB_definable (B : ParameterBase M) (A : Set (Gamma M))
    (hA : GammaParameters.GammaDefinableOverBase B A) (c : Gamma M)
    (hc : IsLUB A c) : GammaParameters.GammaDefinableClosureAtBase B c := by
  have hd := GammaParameters.leastCodes_definable_base B
    (upperCodes (Values.gammaPullback A)) (upperCodes_definable B _ hA)
  have he : GammaParameters.leastCodes (upperCodes (Values.gammaPullback A)) =
      Values.gammaPullback {c} := by
    ext t
    constructor
    · rintro ⟨ht, hleast⟩
      have htNZ : GammaParameters.NonzeroRV t := ht.1
      have hct := hc.2 ((upperCodes_mem_iff A t htNZ).mp ht)
      obtain ⟨u, hu, heu⟩ := GammaParameters.EndpointLogic.codeValue_surjective c
      have huU : u ∈ upperCodes (Values.gammaPullback A) :=
        (upperCodes_mem_iff A u hu).mpr (heu.symm ▸ hc.1)
      have htc := (GammaParameters.original_le_codeValue_iff t u htNZ hu).mp (hleast u huU)
      rw [heu] at htc
      exact (GammaParameters.gammaPullback_mem_codeValue_iff {c} t htNZ).mpr
        (le_antisymm htc hct)
    · intro ht
      have htNZ : GammaParameters.NonzeroRV t := ⟨ht.1, ht.2.1⟩
      have het : GammaParameters.codeValue t = c :=
        (GammaParameters.gammaPullback_mem_codeValue_iff {c} t htNZ).mp ht
      refine ⟨(upperCodes_mem_iff A t htNZ).mpr (het.symm ▸ hc.1), ?_⟩
      intro u huU
      have hu : GammaParameters.NonzeroRV u := huU.1
      apply (GammaParameters.original_le_codeValue_iff t u htNZ hu).mpr
      rw [het]
      exact hc.2 ((upperCodes_mem_iff A u hu).mp huU)
  rwa [he] at hd

theorem gamma_definable_supremum (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (A : Set (Gamma M))
    (hA : GammaParameters.GammaDefinableOverBase B A)
    (hne : A.Nonempty) (hbounded : BddAbove A) :
    ∃ c : Gamma M, IsLUB A c ∧ GammaParameters.GammaDefinableClosureAtBase B c := by
  obtain ⟨c, hc⟩ := gamma_definable_exists_isLUB h00 B A hA hne hbounded
  exact ⟨c, hc, gamma_isLUB_definable B A hA c hc⟩

end DiamondIntegral.Section2
