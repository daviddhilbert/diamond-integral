import IntegrationSection5.CellUnaryPreparations
import IntegrationSection5.ProductStandardComparison
import IntegrationSection4.CellRectangles

/-! Actual standard contractions and RV[2] comparison for every rectangular
cell, including singleton factors and degenerate graph rectangles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {R : Set (VF (M := M) × VF (M := M))}

theorem rectangle_eq_projections (D E : Set (VF (M := M))) (hR : R = D ×ˢ E) :
    R = first R ×ˢ second R := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,hp,rfl⟩,⟨p,hp,rfl⟩⟩
  · rintro ⟨⟨q,hq,hqp⟩,⟨z,hz,hzp⟩⟩
    have hqD := ((Set.ext_iff.mp hR q).mp hq).1
    have hzE := ((Set.ext_iff.mp hR z).mp hz).2
    exact (Set.ext_iff.mp hR p).mpr ⟨hqp ▸ hqD,hzp ▸ hzE⟩

theorem constant_position_rectangle
    {f : VF (M := M) → VF (M := M)} {t : RV (M := M)} (h : CellData R f t)
    (hc : ∀ a ∈ first R, ∀ b ∈ first R, f a = f b) : R = first R ×ˢ second R := by
  obtain ⟨p,hp⟩ := CellRectangles.nonempty h
  have hpF : p.1 ∈ first R := ⟨p,hp,rfl⟩
  have he : R = first R ×ˢ BalancedFibres.translatedRV t (f p.1) :=
    CellRectangles.rectangle_of_fibres R _ (fun a ha => (h.fibres a ha).trans (by rw [hc a ha p.1 hpF]))
  exact rectangle_eq_projections _ _ he

theorem lemma_5_7_rectangle {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ) (F : VFFieldBase G.real)
    (hR : GammaSetDefinable G (cellPointSet R)) (hRect : R = first R ×ˢ second R) :
    ∃ W : Set M, ∃ AR : DefSet (M := M) W 2 0, carrier AR = cellPointSet R ∧
      ∃ C12 : StandardContraction AR (Equiv.refl _),
      ∃ C21 : StandardContraction AR (Equiv.swap 0 1),
        Nonempty (C12.contractionObject ≅ C21.contractionObject) := by
  obtain ⟨P⟩ := cell_unary_preparations hs h00 hsmall F R hR
  have hSource : carrier P.source = cellPointSet (first R ×ˢ second R) :=
    P.source_eq.trans (congrArg cellPointSet hRect)
  have hSG : GammaSetDefinable G (carrier P.source) := P.source_eq.symm ▸ hR
  obtain ⟨C12,C21,e⟩ := product_standard_contractions (first R) (second R)
    P.sourceD_eq P.sourceE_eq P.specialD P.specialE P.gammaD P.gammaE P.pullbackD P.pullbackE
    P.source hSource hSG
  exact ⟨P.codes,P.source,P.source_eq,C12,C21,e⟩

end IntegrationInACVF.Section5
