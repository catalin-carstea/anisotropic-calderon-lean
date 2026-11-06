import Calderon.RadiusTwoEuclideanCollar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! EXPANSION.json precedes the actual compact pole cutoff and both physical normalizations. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open EnergyBridge

lemma exists_radiusTwo_compact_pole_cutoff (q : R3) (hq : ‖(2 : ℝ) • q‖ < 2) :
    ∃ b : ℝ, ∃ chi : SmoothData, ∃ M epsilon delta : ℝ,
      1 ≤ b ∧ ‖(2 : ℝ) • q‖ < b ∧ b < 2 ∧
      HasCompactSupport chi.1 ∧ 0 ≤ M ∧
      (∀ z : R3, |chi.1 z| ≤ M) ∧ (∀ z : R3, ‖gradient chi.1 z‖ ≤ M) ∧
      (∀ z ∈ radiusTwoCollarOpens b, chi.1 z = 1) ∧
      0 < epsilon ∧ (∀ z : R3, dist z ((2 : ℝ) • q) < epsilon → chi.1 z = 0) ∧
      0 < delta ∧ (∀ z : R3, dist ((1/2 : ℝ) • z) q < delta → chi.1 z = 0) := by
  let r : ℝ := max 1 ‖(2 : ℝ) • q‖
  let s : ℝ := (r+2)/2
  let b : ℝ := (s+2)/2
  have hr1 : 1 ≤ r := le_max_left _ _
  have hrq : ‖(2 : ℝ) • q‖ ≤ r := le_max_right _ _
  have hr2 : r < 2 := max_lt (by norm_num) hq
  have hrs : r < s := by dsimp only [s]; linarith
  have hs2 : s < 2 := by dsimp only [s]; linarith
  have hsb : s < b := by dsimp only [b]; linarith
  have hb2 : b < 2 := by dsimp only [b]; linarith
  have hs0 : 0 < s := by linarith
  let outer : ContDiffBump (0 : R3) := ⟨2,3,by norm_num,by norm_num⟩
  let inner : ContDiffBump (0 : R3) := ⟨s,b,hs0,hsb⟩
  let chi : SmoothData := ⟨(fun z : R3 => outer z - inner z),outer.contDiff.sub inner.contDiff⟩
  have hCompact : HasCompactSupport chi.1 := outer.hasCompactSupport.sub inner.hasCompactSupport
  obtain ⟨M,hM,hAbs,hGrad⟩ := (chi.2.of_le (by simp)).exists_abs_le_and_norm_gradient_le hCompact
  have hZero : ∀ z : R3, ‖z‖ ≤ s → chi.1 z = 0 := by
    intro z hz
    have hOuter : outer z = 1 := by
      apply outer.one_of_mem_closedBall
      change dist z (0 : R3) ≤ (2 : ℝ)
      rw [dist_zero_right]
      exact hz.trans hs2.le
    have hInner : inner z = 1 := by
      apply inner.one_of_mem_closedBall
      change dist z (0 : R3) ≤ s
      simpa only [dist_zero_right] using hz
    change outer z - inner z = 0
    rw [hOuter,hInner,sub_self]
  have hOne : ∀ z ∈ radiusTwoCollarOpens b, chi.1 z = 1 := by
    intro z hz
    have hOuter : outer z = 1 := by
      apply outer.one_of_mem_closedBall
      change dist z (0 : R3) ≤ (2 : ℝ)
      simpa only [dist_zero_right] using hz.2.le
    have hInner : inner z = 0 := by
      apply inner.zero_of_le_dist
      change b ≤ dist z (0 : R3)
      simpa only [dist_zero_right] using hz.1.le
    change outer z - inner z = 1
    rw [hOuter,hInner,sub_zero]
  let epsilon : ℝ := s - ‖(2 : ℝ) • q‖
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; linarith
  have hNear : ∀ z : R3, dist z ((2 : ℝ) • q) < epsilon → chi.1 z = 0 := by
    intro z hz
    have hTri : ‖z‖ ≤ dist z ((2 : ℝ) • q) + ‖(2 : ℝ) • q‖ := by
      calc
        ‖z‖ = ‖(z - (2 : ℝ) • q) + (2 : ℝ) • q‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - (2 : ℝ) • q‖ + ‖(2 : ℝ) • q‖ := norm_add_le _ _
        _ = dist z ((2 : ℝ) • q) + ‖(2 : ℝ) • q‖ := by rw [dist_eq_norm]
    apply hZero z
    dsimp only [epsilon] at hz
    linarith
  let delta : ℝ := epsilon/2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hVan : ∀ z : R3, dist ((1/2 : ℝ) • z) q < delta → chi.1 z = 0 := by
    intro z hz
    have hScale : dist z ((2 : ℝ) • q) = 2 * dist ((1/2 : ℝ) • z) q := by
      calc
        dist z ((2 : ℝ) • q) = dist ((2 : ℝ) • ((1/2 : ℝ) • z)) ((2 : ℝ) • q) := by
          rw [smul_smul]
          norm_num
        _ = ‖(2 : ℝ)‖ * dist ((1/2 : ℝ) • z) q := dist_smul₀ _ _ _
        _ = 2 * dist ((1/2 : ℝ) • z) q := by norm_num
    apply hNear z
    rw [hScale]
    dsimp only [delta] at hz
    linarith
  exact ⟨b,chi,M,epsilon,delta,by linarith,by linarith,hb2,hCompact,hM,hAbs,hGrad,
    hOne,hepsilon,hNear,hdelta,hVan⟩

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.exists_radiusTwo_compact_pole_cutoff
