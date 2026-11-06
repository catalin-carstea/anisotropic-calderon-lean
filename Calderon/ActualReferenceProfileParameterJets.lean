import Calderon.ProfileParameterJetBounds
import Calderon.ActualScalarPrincipalAdjoint
import Calderon.ReferenceWeightedApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConformalDepth
open ReferenceWeightedApproximation

/-- One fixed-background cap for the actual profile parameter map, selected
before the conformal and profile parameters. Only the three existing radius
jet bounds and the printed smallness/first-derivative hypotheses are used. -/
theorem exists_reference_radius_parameter_uniform_jet_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ amplitude : ℝ, 0 < amplitude →
      ∀ p : ℕ, 1 ≤ p → ∀ y ∈ K,
      let R := referenceRadius δ amplitude p L
      let beta := actualReferenceBeta g L lam δ amplitude p y
      let tR : R3 → (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ) :=
        fun z => ((lam,(z,R z)),fderiv ℝ R z)
      1 ≤ beta → R y * beta^2 ≤ 1 → ‖fderiv ℝ R y‖ ≤ 1 →
      ContDiff ℝ ∞ tR ∧ ‖iteratedFDeriv ℝ 1 tR y‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2 tR y‖ ≤ C * beta := by
  obtain ⟨C2,hC2,hjets2⟩ :=
    exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds g hg L hL K hK 2
  obtain ⟨C3,hC3,hjets3⟩ :=
    exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds g hg L hL K hK 3
  let C := 1+C2+C3
  have hCap1 : max 1 C2 ≤ C := by
    apply max_le <;> dsimp [C] <;> linarith only [hC2,hC3]
  have hCap2 : max C2 C3 ≤ C := by
    apply max_le <;> dsimp [C] <;> linarith only [hC2,hC3]
  refine ⟨C,by dsimp [C]; linarith only [hC2,hC3],?_⟩
  intro lam hlam δ hδ hδ1 amplitude hAmplitude p hp y hy R beta tR hbeta hsmall hDR
  have hb0 : 0 ≤ beta := zero_le_one.trans hbeta
  have h2raw : ‖iteratedFDeriv ℝ 2 R y‖ ≤ C2*R y*beta^2 := by
    simpa only [R,beta,actualReferenceBeta] using
      (hjets2 lam hlam δ hδ hδ1 amplitude hAmplitude p hp y hy).1
  have h3raw : ‖iteratedFDeriv ℝ 3 R y‖ ≤ C3*R y*beta^3 := by
    simpa only [R,beta,actualReferenceBeta] using
      (hjets3 lam hlam δ hδ hδ1 amplitude hAmplitude p hp y hy).1
  have h2 : ‖iteratedFDeriv ℝ 2 R y‖ ≤ C2 := calc
    _ ≤ C2*R y*beta^2 := h2raw
    _ = C2*(R y*beta^2) := by ring
    _ ≤ C2*1 := mul_le_mul_of_nonneg_left hsmall hC2.le
    _ = C2 := mul_one _
  have h3 : ‖iteratedFDeriv ℝ 3 R y‖ ≤ C3*beta := calc
    _ ≤ C3*R y*beta^3 := h3raw
    _ = (C3*(R y*beta^2))*beta := by ring
    _ ≤ (C3*1)*beta := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall hC3.le) hb0
    _ = C3*beta := by ring
  have hSmooth : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ amplitude p L hδ hAmplitude
  have hj := profile_parameter_map_jet_bounds R hSmooth lam y beta C2 C3 hbeta hDR h2 h3
  exact ⟨hj.1,hj.2.1.trans hCap1,
    hj.2.2.trans (mul_le_mul_of_nonneg_right hCap2 hb0)⟩

end OAI.AnisotropicCalderon.ConformalDepth
