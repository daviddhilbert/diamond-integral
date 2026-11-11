import «section 2».Discs
import Section3.GammaClosedBallCenters
import Section3.GammaBallDefinablePoint

/-! Lemma 2.19 and Corollary 2.21. Algebraic and definable disc points
remain separate assertions over the original ground parameter base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev ClosedDC (M : Type) [LRV.Structure M] := ClosedBallCodes.ClosedBall M

/-- Imaginary definability uses the entire invariant preimage of the disc
name, rather than a chosen centre or radius representative. -/
def ClosedDiscDefinable (B : ParameterBase M) (D : ClosedDC M) : Prop :=
  GammaParameters.DefinableOverBase B (fun _ => .vf) (ClosedBallCodes.pullback {D})

def ClosedDiscAlgebraic (B : ParameterBase M) (D : ClosedDC M) : Prop :=
  ∃ A : Set (ClosedDC M), A.Finite ∧ D ∈ A ∧
    GammaParameters.DefinableOverBase B (fun _ => .vf) (ClosedBallCodes.pullback A)

omit hM in
/-- The closed-disc chart is the existing chart in the manuscript's DC sort. -/
theorem closedDC_underlying (D : ClosedDC M) :
    BallImaginaries.underlying (BallImaginaries.ofClosed D) = ClosedBallCodes.underlying D := rfl

/-- The algebraic case of Lemma 2.19 (`effectiveness`). An algebraic disc
belongs to a finite ground-definable family; its chosen point is algebraic
over that same ground base, with no assertion of individual definability. -/
theorem lemma_2_19_algebraic (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (D : ClosedDC M) (hD : ClosedDiscAlgebraic B D) :
    ∃ x : VF M, GammaParameters.AlgebraicAtBase B .vf x.val ∧
      x.val ∈ ClosedBallCodes.underlying D := by
  obtain ⟨A, hfin, hDA, hdef⟩ := hD
  obtain ⟨c, hmem, hgraph⟩ := GammaParameters.lemma_3_10_gamma_base h00 B A hfin hdef
  obtain ⟨himage, himageFin⟩ := BallImaginaries.closed_center_image_definable B A hfin c hgraph
  let d : A := ⟨D, hDA⟩
  let x : VF M := ⟨c d, himage.proper (c d) (Set.mem_range_self d)⟩
  exact ⟨x, ⟨Set.range c, himage, himageFin, Set.mem_range_self d⟩, hmem d⟩

/-- The definable case of Lemma 2.19: a ground-definable closed disc has
a point definable over that same base. No additional disc name is retained. -/
theorem lemma_2_19_definable (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (D : ClosedDC M) (hD : ClosedDiscDefinable B D) :
    ∃ x : VF M, GammaParameters.DefinableClosureAtBase B .vf x.val ∧
      x.val ∈ ClosedBallCodes.underlying D := by
  obtain ⟨c, hmem, hgraph⟩ := GammaParameters.lemma_3_10_gamma_base h00 B {D}
    (Set.finite_singleton D) hD
  obtain ⟨himage, _⟩ := BallImaginaries.closed_center_image_definable B {D}
    (Set.finite_singleton D) c hgraph
  let d : ({D} : Set (ClosedDC M)) := ⟨D, Set.mem_singleton D⟩
  let x : VF M := ⟨c d, himage.proper (c d) (Set.mem_range_self d)⟩
  have he : Set.range c = {x.val} := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      have hed : e = d := Subtype.ext (Set.mem_singleton_iff.mp e.property)
      exact congrArg c hed
    · rintro rfl
      exact Set.mem_range_self d
  refine ⟨x, ?_, hmem d⟩
  change GammaParameters.DefinableAtBase B .vf {x.val}
  rw [← he]
  exact himage

/-- Corollary 2.21 (`open:disc:def:point`) over a genuine real/Gamma ground
base. The original-base proper intersection produces an original-base
definable point. The reused theorem in fact needs no generation assumption. -/
theorem lemma_2_21 (h00 : M ⊨ Axioms.ACVF00) (B : ParameterBase M)
    (A D : Set M) (hA : GammaParameters.DefinableAtBase B .vf A)
    (hD : GammaParameters.DefinableAtBase B .vf D) (hball : IsBall D)
    (hne : (A ∩ D).Nonempty) (hproper : A ∩ D ⊂ D) :
    ∃ x ∈ D, GammaParameters.DefinableClosureAtBase B .vf x :=
  GammaParameters.lemma_3_11_gamma_base h00 B (A ∩ D) D (hA.inter hD) hne hball hproper

end DiamondIntegral.Section2
