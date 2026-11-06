import Calderon.ActualMiddleSourceMatchedH8LateDensity
import Calderon.CoordinateH8FrechetRecovery

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile SphereHarmonic
  CoordinateBootstrapJets NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth

/-- The checked actual metric recovery supplies the H8 source-jet sum for the
same five source families; only the separate angular density bound remains. -/
theorem exists_actual_middle_source_matched_five_source_coordinateH8_le_three_halves_of_metric_recovery_for_late_density_bound
    (S : KnownSideSourceData) (L Rstar : ℝ)
    (cover : NativeNormalCover S L)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℕ) (hL : 0 < L) (hRstar : 0 < Rstar) (hp : 24 ≤ p)
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (etaA : ℝ) (hEtaA : 0 < etaA) (U : Set (ℝ × R3))
    (hU : IsOpen U)
    (hStrip : Icc (-etaA) etaA ×ˢ cylinder ⊆ U)
    (hR1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U))
    (hR2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U))
    (CA C : ℝ) (hCA : 1 ≤ CA) (hC : 0 ≤ C)
    (hRecovery : ∀ lam ∈ Icc (-etaA) etaA, ∀ n : ℕ, n ≤ 8 → ∀ y ∈ cylinder,
      ‖iteratedFDeriv ℝ n
        (fun x => referenceNormalizedPrincipalDifference S.g1 S.g2 L lam x) y‖ ≤
        CA * ∑ i ∈ Finset.range (n+1), (Nat.choose n i : ℝ) *
          ∑ k : Fin 5, ‖iteratedFDeriv ℝ (n-i+2)
            (fun x => R1 k (x,lam)-R2 k (x,lam)) y‖) :
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
      (∀ B : ℝ, 0 ≤ B → ∃ rho Cstar : ℝ, 0 < rho ∧ 0 < Cstar ∧
      (∀ delta : ℝ, 0 < delta → ∀ y ∈ K,
        referenceRadius delta Rstar p L y < rho →
          let s := (referenceRadius delta Rstar p L y) ^ ((1 : ℝ) / 23)
          closedBall y s ⊆ W ∧ closedBall y s ⊆ interior cylinder ∧
          closedBall y s ⊆ closedBall (0 : R3) 3 ∧
          ∀ z ∈ closedBall y s, chi z = 1) ∧
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
          2 (volume.restrict cylinder) ≤ ENNReal.ofReal B →
      ∀ y ∈ K, referenceRadius delta Rstar p L y < rho →
        coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
          Cstar * (referenceRadius delta Rstar p L y)^(3/2 : ℝ))  := by
  obtain ⟨BH,hBH,hJetBound⟩ :=
    exists_coordinateH8_le_source_jet_sum_of_binomial_recovery
  let CH : ℝ := BH * CA
  have hCH : 0 ≤ CH := mul_nonneg (by linarith) (by linarith)
  have hH8 : ∀ lam ∈ Icc (-etaA) etaA, ∀ y ∈ cylinder,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        CH * ∑ k : Fin 5, ∑ n ∈ Finset.range 11,
          ‖iteratedFDeriv ℝ n
            (fun x => R1 k (x,lam)-R2 k (x,lam)) y‖ := by
    intro lam hLam y hy
    have hMetricSmooth : ContDiff ℝ ∞
        (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      exact contDiff_referenceNormalizedPrincipalDifference_entry
        S.g1 S.g2 S.g1_admissible S.g2_admissible L lam i j
    let F : Fin 5 → R3 → ℝ := fun k x => R1 k (x,lam)-R2 k (x,lam)
    have hRaw := hJetBound
      (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) hMetricSmooth
      F CA (by linarith) y
      (fun n hn => hRecovery lam hLam n hn y hy)
    simpa [CH,F,mul_assoc] using hRaw
  exact exists_actual_middle_source_matched_five_source_coordinateH8_le_three_halves_for_late_density_bound
    S L Rstar cover hO hD p hL hRstar hp R1 R2 etaA hEtaA U hU hStrip hR1 hR2
    CH C hCH hC hH8

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
