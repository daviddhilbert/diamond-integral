import «section 5».CylindricalFibreCertificates

/-! A Gamma family with one fixed cylindrical fibre shape integrates to
that shape's Euler factor times its base, for arbitrary definable bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic GammaCellSections GammaCellUnboundedSections
open GammaIntegerFamilies GammaWeightedFamilies GammaIndicators GammaFamilyIntegration GammaIteratedIntegral

def CylinderFibreKind.eulerFactor (shape : CylinderFibreKind) (kind : EulerKind) : ℤ :=
  match shape with
  | .graph => 1
  | .band => -1
  | .upperRay | .lowerRay => kind.rayValue
  | .line => kind.lineValue

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_cylinder_integrateFirst
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (kind : EulerKind) {n : ℕ} (shape : CylinderFibreKind)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (R : Set (Fin (n+1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hproj : ∀ z ∈ R, Fin.tail z ∈ I)
    (hfibre : ∀ y ∈ I, shape.Describes (fun t => Fin.cons t y ∈ R)) :
    integrateFirst h00 hκ hs B hr hγ kind n (indicatorFamily B R hR) =
      shape.eulerFactor kind • indicatorFamily B I hI := by
  have hex (y : Fin n → Values.Gamma (M := M)) :
      ∃ a : Fin shape.endpoints → Values.Gamma (M := M),
        y ∈ I → shape.ordered a ∧ ∀ t, Fin.cons t y ∈ R ↔ shape.condition a t := by
    by_cases hy : y ∈ I
    · obtain ⟨a, ha, he⟩ := hfibre y hy
      exact ⟨a, fun _ => ⟨ha, he⟩⟩
    · exact ⟨fun _ => 1, fun h => (hy h).elim⟩
  choose a ha using hex
  have hrow (z : Fin (n+1) → Values.Gamma (M := M)) :
      z ∈ R ↔ Fin.tail z ∈ I ∧ shape.condition (a (Fin.tail z)) (z 0) := by
    constructor
    · intro hz
      have hy := hproj z hz
      refine ⟨hy, ((ha _ hy).2 (z 0)).mp ?_⟩
      simpa only [Fin.cons_self_tail] using hz
    · rintro ⟨hy, hz⟩
      simpa only [Fin.cons_self_tail] using ((ha _ hy).2 (z 0)).mpr hz
  cases shape with
  | graph =>
    have he : R = graphCell I (fun y => a y 0) := Set.ext hrow
    subst R
    simpa only [CylinderFibreKind.eulerFactor, one_zsmul] using
      integrateFirst_graph h00 hκ hs B hr hγ kind I hI (fun y => a y 0) hR
  | band =>
    have he : R = bandCell I (fun y => a y 0) (fun y => a y 1) := Set.ext hrow
    subst R
    simpa only [CylinderFibreKind.eulerFactor, neg_one_zsmul] using
      integrateFirst_band h00 hκ hs B hr hγ kind I hI (fun y => a y 0) (fun y => a y 1)
        (fun y hy => (ha y hy).1) hR
  | upperRay =>
    have he : R = upperRayCell I (fun y => a y 0) := Set.ext hrow
    subst R
    exact integrateFirst_upperRay h00 hκ hs B hr hγ kind I hI (fun y => a y 0) hR
  | lowerRay =>
    have he : R = lowerRayCell I (fun y => a y 0) := Set.ext hrow
    subst R
    exact integrateFirst_lowerRay h00 hκ hs B hr hγ kind I hI (fun y => a y 0) hR
  | line =>
    have he : R = lineCell I := by
      ext z
      simpa only [CylinderFibreKind.condition, and_true, lineCell, Set.mem_ofPred_eq] using hrow z
    subst R
    exact integrateFirst_line h00 hκ hs B hr hγ kind I hI hR

theorem gamma_cylinder_integrateAll
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (kind : EulerKind) {n : ℕ} (shape : CylinderFibreKind)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (R : Set (Fin (n+1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hproj : ∀ z ∈ R, Fin.tail z ∈ I)
    (hfibre : ∀ y ∈ I, shape.Describes (fun t => Fin.cons t y ∈ R)) :
    integrateAll h00 hκ hs B hr hγ kind (n+1) (indicatorFamily B R hR) =
      shape.eulerFactor kind * integrateAll h00 hκ hs B hr hγ kind n (indicatorFamily B I hI) := by
  change integrateAll h00 hκ hs B hr hγ kind n
    (integrateFirst h00 hκ hs B hr hγ kind n (indicatorFamily B R hR)) = _
  rw [gamma_cylinder_integrateFirst h00 hκ hs B hr hγ kind shape I hI R hR hproj hfibre, map_zsmul]
  exact zsmul_eq_mul _ _

end DiamondIntegral.Section5
