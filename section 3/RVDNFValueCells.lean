import «section 3».RVValueCellCover
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

abbrev RVDNFValueCellIndex (D : LiteralDNF I R (Fin n)) :=
  Σ q : Fin D.length, ((D[q]).toFinset → Bool)

instance rvDNFValueCellIndex_finite (D : LiteralDNF I R (Fin n)) : Finite (RVDNFValueCellIndex D) := by
  unfold RVDNFValueCellIndex
  infer_instance

def rvDNFValueCell (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (j : RVDNFValueCellIndex D) :
    Set (Fin n → (CanonicalRV.RVSort M)ˣ) := rvClauseValueCell (D[j.1]).toFinset a r j.2

theorem rvDNFValueCells_cover (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    PolarityDNF.holds (RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M))) D ↔
      ∃ j : RVDNFValueCellIndex D, x ∈ rvDNFValueCell D a r j := by
  constructor
  · rintro ⟨C,hC,hx⟩
    obtain ⟨q,hq⟩ := List.getElem_of_mem hC
    let i : Fin D.length := ⟨q,hq.1⟩
    have hi : D[i] = C := hq.2
    have hc : ∀ L ∈ (D[i]).toFinset, RVLiteral.comparison a r (fun k => (x k : CanonicalRV.RVSort M)) L := by
      intro L hL
      apply hx L
      rw [← hi]
      exact List.mem_toFinset.mp hL
    obtain ⟨b,hb⟩ := (rvClauseValueCells_cover (D[i]).toFinset a r x).mp hc
    exact ⟨⟨i,b⟩,hb⟩
  · rintro ⟨⟨q,b⟩,hx⟩
    refine ⟨D[q],List.getElem_mem q.isLt,?_⟩
    intro L hL
    exact hx.1 L (List.mem_toFinset.mpr hL)

theorem rvDNFValueCells_finite (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) :
    (Set.range (rvDNFValueCell D a r)).Finite := Set.finite_range _

theorem rvDNF_clause_certificate (D : LiteralDNF I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (hD : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      LiteralDNF.Certified a r (fun i => (x i : CanonicalRV.RVSort M)) D)
    (q : Fin D.length) :
    ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ,
      (∀ L ∈ (D[q]).toFinset, RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L) →
      ∀ L ∈ (D[q]).toFinset, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L := by
  intro x hx L hL
  exact hD x (D[q]) (List.getElem_mem q.isLt) (fun L hL => hx L (List.mem_toFinset.mpr hL)) L
    (List.mem_toFinset.mp hL)
end DiamondIntegral.Section3
