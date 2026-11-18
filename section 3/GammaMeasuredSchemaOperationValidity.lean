import «section 3».GammaMeasuredTypedRowValidity
import «section 3».GammaMeasuredGeometricSchemata
import IntegrationSection6.GammaRawElementarySchemaBridge

/-! Existing coproduct and elementary formulas preserve Gamma quotient
density validity. The proofs reuse their native exact row descriptions;
finite structural bounds remain those supplied by native presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaMeasuredRVSchema.coprod_valid_of_bound
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (G : GammaMeasuredRVSchema hc B p b (k+1) sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z) (L : ℕ)
    (hObj : ((F.coprodFormula G).withBound L).object.valid z) :
    ((F.coprodFormula G).withBound L).valid z := by
  have hRows (w : Fin (1+(a+b)) → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
      ((F.coprodFormula G).withBound L).rowDensity z w c ↔
        (∃ x, F.rowDensity z x c ∧ @rvLeftTag M N hN a b x = w) ∨
        ∃ y, G.rowDensity z y c ∧ @rvRightTag M N hN b a y = w :=
    F.toRVTemplate.coprod_rowDensity G.toRVTemplate z hF.1.1 w (gammaVolumeCodeRV c)
  apply GammaMeasuredRVSchema.valid_of_typed _ z hObj
  · intro w hw
    rcases (F.object.coprod_row_domain_formula G.object z hF.1.1 w).mp hw with
      ⟨x,hx,ht⟩ | ⟨y,hy,ht⟩
    · obtain ⟨c,hcValue⟩ := F.rowDensity_exists z hF ⟨x,hx⟩
      exact ⟨c,(hRows w c).mpr (Or.inl ⟨x,hcValue,ht⟩)⟩
    · obtain ⟨c,hcValue⟩ := G.rowDensity_exists z hG ⟨y,hy⟩
      exact ⟨c,(hRows w c).mpr (Or.inr ⟨y,hcValue,ht⟩)⟩
  · intro w c hw
    apply (F.object.coprod_row_domain_formula G.object z hF.1.1 w).mpr
    rcases (hRows w c).mp hw with ⟨x,hx,ht⟩ | ⟨y,hy,ht⟩
    · exact Or.inl ⟨x,F.rowDensity_support z hF x c hx,ht⟩
    · exact Or.inr ⟨y,G.rowDensity_support z hG y c hy,ht⟩
  · intro w c hw d
    rcases (hRows w c).mp hw with ⟨x,hx,ht⟩ | ⟨y,hy,ht⟩
    · have hClass := F.rowDensity_same_value z hF ⟨x,F.rowDensity_support z hF x c hx⟩ c hx d
      constructor
      · intro hd
        rcases (hRows w d).mp hd with ⟨x',hx',ht'⟩ | ⟨y,hy,ht'⟩
        · have he : x' = x := @rvLeftTag_injective M N hN a b _ _ (ht'.trans ht.symm)
          subst x'
          exact hClass.mp hx'
        · exact False.elim (@rvTag_disjoint M N hN a b x y (ht.trans ht'.symm))
      · intro hd
        exact (hRows w d).mpr (Or.inl ⟨x,hClass.mpr hd,ht⟩)
    · have hClass := G.rowDensity_same_value z hG ⟨y,G.rowDensity_support z hG y c hy⟩ c hy d
      constructor
      · intro hd
        rcases (hRows w d).mp hd with ⟨x,hx,ht'⟩ | ⟨y',hy',ht'⟩
        · exact False.elim (@rvTag_disjoint M N hN a b x y (ht'.trans ht.symm))
        · have he : y' = y := @rvRightTag_injective M N hN b a _ _ (ht'.trans ht.symm)
          subst y'
          exact hClass.mp hy'
      · intro hd
        exact (hRows w d).mpr (Or.inr ⟨y,hClass.mpr hd,ht⟩)

theorem GammaMeasuredRVSchema.elementary_valid_of_bound
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp)
    (z : Fin p → M) (hF : F.valid z) (L : ℕ)
    (hObj : (F.elementaryFormula.withBound L).object.valid z) :
    (F.elementaryFormula.withBound L).valid z := by
  have hRows (w : Fin (a+1) → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
      (F.elementaryFormula.withBound L).rowDensity z w c ↔
        F.rowDensity z (w ∘ Fin.castAdd 1) c ∧ w ∈ F.elementaryFormula.object.rowDomain z :=
    F.elementary_rowDensity z hF.1.1 w c
  apply GammaMeasuredRVSchema.valid_of_typed _ z hObj
  · intro w hw
    have hx : w ∘ Fin.castAdd 1 ∈ F.object.rowDomain z := by
      change Fin.append z (rvValues (w ∘ Fin.castAdd 1)) ∈ F.object.domain
      have h := hw.1
      rw [rawElementaryHead_append] at h
      exact h
    obtain ⟨c,hcValue⟩ := F.rowDensity_exists z hF ⟨w ∘ Fin.castAdd 1,hx⟩
    exact ⟨c,(hRows w c).mpr ⟨hcValue,hw⟩⟩
  · intro w c hw
    exact ((hRows w c).mp hw).2
  · intro w c hw d
    obtain ⟨hcValue,hD⟩ := (hRows w c).mp hw
    have hx := F.rowDensity_support z hF _ c hcValue
    exact (hRows w d).trans ((and_iff_left hD).trans
      (F.rowDensity_same_value z hF ⟨w ∘ Fin.castAdd 1,hx⟩ c hcValue d))

theorem GammaMeasuredRVSchema.exists_valid_coprod_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (G : GammaMeasuredRVSchema hc B p b (k+1) sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z) :
    ∃ L : ℕ, ((F.coprodFormula G).withBound L).valid z := by
  obtain ⟨P⟩ := F.object.realize z hF.1
  obtain ⟨Q⟩ := G.object.realize z hG.1
  obtain ⟨L,hL⟩ := F.object.exists_valid_coprod_bound hκ hs hr hg G.object z hF.1.1
    (F.object.valid_row_support hF.1) (G.object.valid_row_support hG.1) P Q
  exact ⟨L,F.coprod_valid_of_bound G z hF hG L hL⟩

end DiamondIntegral.Section3
