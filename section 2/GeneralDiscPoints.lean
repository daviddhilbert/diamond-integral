import «section 2».Bases
import «section 2».Discs
import Section3.GeneratedBaseLifting
import Section3.GeneralBallCenters

/-! The generation bridge for Lemma 2.20. Passing temporarily to definable
closure does not change the original parameter base of the conclusion.
The saturation bound for this temporary closure is explicit. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem VFGeneratedFieldBase.definableOver_gamma_names_iff
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M))
    {n : ℕ} (sn : Fin n → SortTag) (U : Set (Fin n → M)) :
    GammaParameters.DefinableOverBase ⟨(S : Set M), G⟩ sn U ↔
      GammaParameters.DefinableOverBase ⟨vfFieldNames F.field, G⟩ sn U := by
  constructor
  · intro hU
    apply hU.eliminate_definable_params
    · intro c hc
      obtain ⟨σ, hσ⟩ := F.definable_over_fieldNames c hc
      exact ⟨σ, GammaParameters.real_definableAtBase _ σ {c} hσ⟩
    · intro γ hγ
      exact GammaParameters.gamma_name_definable _ γ hγ
  · intro hU
    exact hU.mono F.fieldNames_subset (Set.Subset.refl _)

/-- The temporary dcl depends only on the original VF field names and
the original Gamma names, rather than an assumed dcl-generation premise. -/
theorem VFGeneratedFieldBase.gamma_closure_eq
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M)) :
    GammaParameters.closureBase ⟨(S : Set M), G⟩ =
      GammaParameters.closureBase ⟨vfFieldNames F.field, G⟩ := by
  have hr : (GammaParameters.closureBase ⟨(S : Set M), G⟩).real =
      (GammaParameters.closureBase ⟨vfFieldNames F.field, G⟩).real := by
    ext c
    exact exists_congr (fun σ => F.definableOver_gamma_names_iff G
      (fun _ : Fin 1 => σ) {z | z 0 ∈ ({c} : Set M)})
  have hg : (GammaParameters.closureBase ⟨(S : Set M), G⟩).gamma =
      (GammaParameters.closureBase ⟨vfFieldNames F.field, G⟩).gamma := by
    ext γ
    exact F.definableOver_gamma_names_iff G (fun _ : Fin 1 => .rv)
      {z | z 0 ∈ Values.gammaPullback {γ}}
  cases hS : GammaParameters.closureBase ⟨(S : Set M), G⟩
  cases hF : GammaParameters.closureBase ⟨vfFieldNames F.field, G⟩
  simp_all

theorem VFGeneratedFieldBase.gamma_closure_generated
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M)) :
    DclVFGammaGenerated M (GammaParameters.closureBase ⟨(S : Set M), G⟩) := by
  rw [F.gamma_closure_eq G]
  apply GammaParameters.vfGammaGenerated_closure
  rintro a ⟨x, _, rfl⟩
  exact x.property

/-- Algebraicity of an actual disc name is finite-family definability in
both complete invariant code charts. -/
def DiscAlgebraic (B : ParameterBase M) (D : DC (M := M)) : Prop :=
  ∃ A : Set (DC (M := M)), A.Finite ∧ D ∈ A ∧ BallImaginaries.FamilyDefinableBase B A

def DiscDefinable (B : ParameterBase M) (D : DC (M := M)) : Prop :=
  BallImaginaries.FamilyDefinableBase B {D}

private theorem open_center_image_definable (B : ParameterBase M)
    (A : Set (OpenBallCodes.OpenBall M)) (c : A → M)
    (hc : GammaParameters.DefinableOverBase B (fun _ => .vf)
      (OpenBallCodes.quotientCenterGraph A c)) :
    GammaParameters.DefinableAtBase B .vf (Set.range c) := by
  have hd := hc.image_real (fun _ : Fin 1 => Fin.last 2)
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf)
    {z | z 0 ∈ Set.range c}
  convert hd using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨D, hD⟩
    obtain ⟨q, hq⟩ := Quotient.exists_rep D.val
    let w : Fin 3 → M := Fin.snoc q.val (c D)
    refine ⟨w, ⟨q, ?_, D, hq, rfl⟩, ?_⟩
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i
      exact hD
  · rintro ⟨w, ⟨q, hq, D, hD, hcD⟩, he⟩
    exact ⟨D, hcD.trans (congrFun he 0)⟩

private theorem singleton_center_point (B : ParameterBase M) (D : DC (M := M))
    (f : ({D} : Set (DC (M := M))) → M)
    (hmem : ∀ d, f d ∈ BallImaginaries.underlying d.val)
    (hf : BallImaginaries.CenterDefinableBase B {D} f) :
    ∃ x : VF M, GammaParameters.DefinableClosureAtBase B .vf x.val ∧
      x.val ∈ BallImaginaries.underlying D := by
  let d : ({D} : Set (DC (M := M))) := ⟨D, Set.mem_singleton D⟩
  have hpoint : GammaParameters.DefinableClosureAtBase B .vf (f d) := by
    rcases BallImaginaries.family_cases {D} d with ⟨C, hC⟩ | ⟨O, hO⟩
    · let c : BallImaginaries.closedFamily {D} → M :=
        fun e => f ⟨BallImaginaries.ofClosed e.val, e.property⟩
      obtain ⟨himage, _⟩ := BallImaginaries.closed_center_image_definable B
        (BallImaginaries.closedFamily {D})
        (BallImaginaries.closedFamily_finite {D} (Set.finite_singleton D)) c hf.1
      have he : Set.range c = {f d} := by
        apply Set.Subset.antisymm
        · rintro y ⟨e, rfl⟩
          exact congrArg f (Subtype.ext (Set.mem_singleton_iff.mp e.property))
        · rintro y rfl
          exact ⟨C, congrArg f (Subtype.ext hC)⟩
      change GammaParameters.DefinableAtBase B .vf {f d}
      rwa [he] at himage
    · let c : BallImaginaries.openFamily {D} → M :=
        fun e => f ⟨BallImaginaries.ofOpen e.val, e.property⟩
      have himage := open_center_image_definable B (BallImaginaries.openFamily {D}) c hf.2
      have he : Set.range c = {f d} := by
        apply Set.Subset.antisymm
        · rintro y ⟨e, rfl⟩
          exact congrArg f (Subtype.ext (Set.mem_singleton_iff.mp e.property))
        · rintro y rfl
          exact ⟨O, congrArg f (Subtype.ext hO)⟩
      change GammaParameters.DefinableAtBase B .vf {f d}
      rwa [he] at himage
  exact ⟨⟨f d, hpoint.proper (f d) rfl⟩, hpoint, hmem d⟩

/-- Algebraic case of Lemma 2.20 over the original VF-generated real
substructure together with arbitrary genuine Gamma names. The temporary
dcl-generation premise is proved, not assumed. Its size bound is retained
explicitly; the conclusion descends back to the original base. -/
theorem lemma_2_20_algebraic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M))
    (hsmall : Cardinal.mk (GammaParameters.closureBase ⟨(S : Set M), G⟩).real < κ)
    (D : DC (M := M)) (hD : DiscAlgebraic ⟨(S : Set M), G⟩ D) :
    ∃ x : VF M, GammaParameters.AlgebraicAtBase ⟨(S : Set M), G⟩ .vf x.val ∧
      x.val ∈ BallImaginaries.underlying D := by
  obtain ⟨A, hfin, hDA, hdef⟩ := hD
  let B : ParameterBase M := ⟨(S : Set M), G⟩
  have hdef' : BallImaginaries.FamilyDefinableBase (GammaParameters.closureBase B) A :=
    ⟨(GammaParameters.DefinableOverBase.closureBase_iff B _ _).mpr hdef.1,
      (GammaParameters.DefinableOverBase.closureBase_iff B _ _).mpr hdef.2⟩
  obtain ⟨x, hx, hmem⟩ := BallImaginaries.finite_family_algebraic_points hκ hs h00
    (GammaParameters.closureBase B) hsmall (F.gamma_closure_generated G) A hfin hdef' ⟨D, hDA⟩
  exact ⟨x, (GammaParameters.AlgebraicAtBase.closureBase_iff B .vf x.val).mp hx, hmem⟩

/-- Definable case of Lemma 2.20. Both code charts of the centre function
descend from the temporary dcl to the original real/Gamma ground base. -/
theorem lemma_2_20_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : LRV.Substructure M} (F : VFGeneratedFieldBase S) (G : Set (Gamma M))
    (hsmall : Cardinal.mk (GammaParameters.closureBase ⟨(S : Set M), G⟩).real < κ)
    (D : DC (M := M)) (hD : DiscDefinable ⟨(S : Set M), G⟩ D) :
    ∃ x : VF M, GammaParameters.DefinableClosureAtBase ⟨(S : Set M), G⟩ .vf x.val ∧
      x.val ∈ BallImaginaries.underlying D := by
  let B : ParameterBase M := ⟨(S : Set M), G⟩
  have hD' : BallImaginaries.FamilyDefinableBase (GammaParameters.closureBase B) {D} :=
    ⟨(GammaParameters.DefinableOverBase.closureBase_iff B _ _).mpr hD.1,
      (GammaParameters.DefinableOverBase.closureBase_iff B _ _).mpr hD.2⟩
  obtain ⟨f, hmem, hf⟩ := BallImaginaries.lemma_3_13 hκ hs h00
    (GammaParameters.closureBase B) hsmall (F.gamma_closure_generated G) {D}
    (Set.finite_singleton D) hD'
  exact singleton_center_point B D f hmem
    ⟨(GammaParameters.DefinableOverBase.closureBase_iff B _ _).mp hf.1,
      (GammaParameters.DefinableOverBase.closureBase_iff B _ _).mp hf.2⟩

end DiamondIntegral.Section2
