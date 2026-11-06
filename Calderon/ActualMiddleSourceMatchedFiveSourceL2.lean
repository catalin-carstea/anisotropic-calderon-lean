import Calderon.ActualMiddleSourceMatchedCutoff
import Calderon.ActualFiveSourceLocalL2FromNativeMoment
import Calderon.ActualFiveSourceSliceSmoothness

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile SphereHarmonic

/-- The exact source cutoff is retained unchanged in the actual five-source
local L² consequence. The density bound remains a separate explicit premise
with its constant fixed before spatial dilation and shrinking radius. -/
theorem exists_actual_middle_source_matched_five_source_local_L2_le_of_density_bound
    (S : KnownSideSourceData) (L Rstar : ℝ)
    (cover : NativeNormalCover S L)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℕ) (hL : 0 < L) (hRstar : 0 < Rstar) (hp : 24 ≤ p) :
    ∃ tb : ℝ, 0 < tb ∧ 3 * tb < depthPrimitive L (1/8) (1/4) ∧
      let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
        referenceDepth L y ≤ 2 * tb}
      IsCompact K ∧ K ⊆ interior cylinder ∧
      ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        range chi ⊆ Icc 0 1 ∧ tsupport chi ⊆ interior cylinder ∧
        ∃ W : Set R3, IsOpen W ∧ K ⊆ W ∧
          (∀ z ∈ W, chi z = 1) ∧
          tsupport (fderiv ℝ chi) ⊆
            {z : R3 | z 2 < -(1/4 : ℝ)} ∪
              {z : R3 | tb < referenceDepth L z} ∧
          ∃ rho : ℝ, 0 < rho ∧
            (∀ delta : ℝ, 0 < delta → ∀ y ∈ K,
              referenceRadius delta Rstar p L y < rho →
                let s := (referenceRadius delta Rstar p L y) ^ ((1 : ℝ) / 23)
                closedBall y s ⊆ W ∧ closedBall y s ⊆ interior cylinder ∧
                closedBall y s ⊆ closedBall (0 : R3) 3 ∧
                ∀ z ∈ closedBall y s, chi z = 1) ∧
          ∀ (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
            (etaA : ℝ) (U : Set (ℝ × R3)), IsOpen U →
            Icc (-etaA) etaA ×ˢ cylinder ⊆ U →
            (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U)) →
            (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) →
          ∀ (C B : ℝ), 0 ≤ C → 0 ≤ B →
          ∀ (μ : Measure R3) [IsFiniteMeasureOnCompacts μ],
          ∀ lam ∈ Icc (-etaA) etaA,
          ∀ delta : ℝ, 0 < delta →
          ∀ (Psi : R3 → SphereSobolev (3/2 : ℝ)),
            ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
            (∀ k : Fin 5, ∀ i : Fin cover.count,
              ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                |R2 k (y,lam)-R1 k (y,lam)| ≤
                  C * (referenceRadius delta Rstar p L y)^2 *
                    ‖(sphereSobolevZeroEquiv hO hD).symm
                      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖) →
            eLpNorm (fun z : R3 => chi z •
              (sphereSobolevZeroEquiv hO hD).symm
                (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi z)))
              2 (μ.restrict cylinder) ≤ ENNReal.ofReal B →
          ∀ y ∈ K,
            let r := referenceRadius delta Rstar p L y
            let s := r ^ ((1 : ℝ) / 23)
            r < rho →
            ∀ k : Fin 5,
            (eLpNorm (fun z : R3 => R1 k (z,lam)-R2 k (z,lam)) 2
              (μ.restrict (ball y s))).toReal ≤
              (((3/2 : ℝ)^p)^2 * C * B) * r^2 := by
  obtain ⟨tb,htb,hthree,hKcompact,hKinside,chi,hChi,hChiCompact,hRange,
    hChiSupport,W,hWopen,hKW,hWOne,hDerivRegion,rhoC,hrhoC,hCutoff⟩ :=
    exists_actual_middle_source_matched_cutoff L Rstar p hL hRstar
  obtain ⟨rhoM,hrhoM,hLocal⟩ :=
    exists_local_five_source_eLpNorm_le_native_density_moment
      S L Rstar cover hO hD p hRstar hp
  let rho : ℝ := min rhoC rhoM
  have hrho : 0 < rho := lt_min hrhoC hrhoM
  refine ⟨tb,htb,hthree,hKcompact,hKinside,chi,hChi,hChiCompact,hRange,
    hChiSupport,W,hWopen,hKW,hWOne,hDerivRegion,rho,hrho,?_,?_⟩
  · intro delta hDelta y hy hrsmall
    exact hCutoff delta hDelta y hy (hrsmall.trans_le (min_le_left _ _))
  · intro R1 R2 etaA U hU hStrip hR1 hR2 C B hC hB μ hFinite lam hLam
      delta hDelta Psi hPsi hPsiCompact hMoment hDensity y hy
    dsimp
    intro hrsmall k
    have hSource := continuousOn_actual_five_source_difference_of_joint_strip
      R1 R2 etaA U hU hStrip hR1 hR2 lam hLam
    have hY : y ∈ closedBall (0 : R3) 3 := by
      have hyC : y ∈ cylinder := interior_subset (hKinside hy)
      have hn := norm_le_two_of_mem_cylinder y hyC
      apply mem_closedBall_zero_iff.mpr
      linarith
    have hGeom := hCutoff delta hDelta y hy
      (hrsmall.trans_le (min_le_left _ _))
    dsimp at hGeom
    have hSmall : referenceRadius delta Rstar p L y < rhoM :=
      hrsmall.trans_le (min_le_right _ _)
    have hRaw := hLocal R1 R2 lam Psi hPsi hPsiCompact hSource μ chi
      hChi.continuous C hC delta hDelta hMoment y hY hSmall
      (ball_subset_closedBall.trans (hGeom.2.1.trans interior_subset))
      (ball_subset_closedBall.trans hGeom.2.2.1)
      (fun z hz => hGeom.2.2.2 z (ball_subset_closedBall hz)) k
    have hRhsFinite : ENNReal.ofReal (((3/2 : ℝ)^p * referenceRadius delta Rstar p L y)^2) *
        (ENNReal.ofReal C * ENNReal.ofReal B) ≠ (⊤ : ℝ≥0∞) := by finiteness
    have hScaled : eLpNorm (fun z : R3 => R1 k (z,lam)-R2 k (z,lam)) 2
        (μ.restrict (ball y ((referenceRadius delta Rstar p L y)^((1 : ℝ)/23)))) ≤
        ENNReal.ofReal (((3/2 : ℝ)^p * referenceRadius delta Rstar p L y)^2) *
          (ENNReal.ofReal C * ENNReal.ofReal B) :=
      hRaw.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hDensity (by positivity)) (by positivity))
    have hReal := ENNReal.toReal_mono hRhsFinite hScaled
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hB] at hReal
    convert hReal using 1 <;> ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
