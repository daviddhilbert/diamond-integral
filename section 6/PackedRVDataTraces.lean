import «section 6».ProgramRVDataTraces
import «section 6».FiniteRVDataPacking

/-! Encode a complete heterogeneous finite data trace in one definable
RV row. Equality of packed rows recovers every traced family; separate
row bounds give a bound for this row, without any uniform VF-base bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p : ℕ}

def rvTraceMaxArity (D : List (RVDataTemplate (M := M) S p)) : ℕ := Finset.univ.sup (fun i : Fin D.length => (D.get i).1)

theorem rvTraceArity_le (D : List (RVDataTemplate (M := M) S p)) (i : Fin D.length) : (D.get i).1 ≤ rvTraceMaxArity D :=
  Finset.le_sup (f := fun i : Fin D.length => (D.get i).1) (Finset.mem_univ i)

def packedRVTrace (D : List (RVDataTemplate (M := M) S p)) :
    RVSetParameterTemplate (M := M) S p (rvTraceMaxArity D+D.length) :=
  packedRVDataFamily (fun i : Fin D.length => (D.get i).2) (rvTraceMaxArity D)

theorem packedRVTrace_doublyBounded (D : List (RVDataTemplate (M := M) S p)) (a : Fin p → M)
    (hD : RVTraceRowsBounded a D) : RVValueDoublyBounded ((packedRVTrace D).fibre a).carrier :=
  packedRVDataFamily_doublyBounded (fun i : Fin D.length => (D.get i).2) _ a
    (fun i => hD (D.get i) (List.get_mem D i))

theorem trace_rows_eq_of_packed_eq (h00 : M ⊨ Axioms.ACVF00)
    (D : List (RVDataTemplate (M := M) S p)) (a b : Fin p → M)
    (he : ((packedRVTrace D).fibre a).carrier=((packedRVTrace D).fibre b).carrier) :
    ∀ T ∈ D,(T.2.fibre a).carrier=(T.2.fibre b).carrier := by
  intro T hT
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hT
  have h := constituent_rows_eq_of_packed_eq h00 (fun i : Fin D.length => (D.get i).2)
    (rvTraceArity_le D) a b he i
  cases hi
  exact h

def restrictRVTrace (D : List (RVDataTemplate (M := M) S p))
    (X : Set (Fin p → M)) (hX : S.Definable LRV X) : List (RVDataTemplate (M := M) S p) :=
  D.map (fun T => ⟨T.1,T.2.restrictParameters X hX⟩)

theorem restrictRVTrace_bounded (D : List (RVDataTemplate (M := M) S p))
    (X : Set (Fin p → M)) (hX : S.Definable LRV X) (a : Fin p → M)
    (hD : a ∈ X → RVTraceRowsBounded a D) : RVTraceRowsBounded a (restrictRVTrace D X hX) := by
  intro T hT
  obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hT
  rw [RVSetParameterTemplate.restrictParameters_fibre]
  by_cases ha : a ∈ X
  · obtain ⟨γ,hγ⟩ := hD ha U hU
    exact ⟨γ,fun u hu => hγ u hu.2⟩
  · exact ⟨1,fun _ h => (ha h.1).elim⟩

end DiamondIntegral.Section6
