import Calderon.ActualMiddleSourceMatchedFiveSourceL2
import Calderon.ActualFiveSourceSpatialC45Cap
import Calderon.ActualTaylorInterpolation

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile SphereHarmonic
  CoordinateBootstrapJets NormalizedPrincipalMetric

/-- The exact Section 06 middle-set gain for the original five scalar sources,
taking the separate uniform angular-density norm bound as a hypothesis. The same
cutoff chosen with the native moment remains in that density hypothesis. -/
theorem exists_actual_middle_source_matched_five_source_coordinateH8_le_three_halves_for_late_density_bound
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
    (CH C : ℝ) (hCH : 0 ≤ CH) (hC : 0 ≤ C)
    (hH8 : ∀ lam ∈ Icc (-etaA) etaA, ∀ y ∈ cylinder,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        CH * ∑ k : Fin 5, ∑ n ∈ Finset.range 11,
          ‖iteratedFDeriv ℝ n
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
          Cstar * (referenceRadius delta Rstar p L y)^(3/2 : ℝ)) := by
  obtain ⟨T,hT,hInterp⟩ :=
    OAI.AnisotropicCalderon.LocalPolynomialInterpolation.exists_uniform_taylor44_jet_le_three_halves_of_local_L2_bound
  obtain ⟨M,hM1,hM⟩ :=
    exists_uniform_spatial_iteratedFDeriv45_five_source_bound
      R1 R2 etaA hEtaA U hU hStrip hR1 hR2
  obtain ⟨tb,htb,hthree,hKcompact,hKinside,chi,hChi,hChiCompact,hRange,
    hChiSupport,W,hWopen,hKW,hWOne,hDerivRegion,rhoL,hrhoL,hGeometry,hLocal⟩ :=
    exists_actual_middle_source_matched_five_source_local_L2_le_of_density_bound
      S L Rstar cover hO hD p hL hRstar hp
  refine ⟨tb,htb,hthree,hKcompact,hKinside,chi,hChi,hChiCompact,hRange,
    hChiSupport,W,hWopen,hKW,hWOne,hDerivRegion,?_⟩
  intro B hB
  let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
    referenceDepth L y ≤ 2 * tb}
  let rho : ℝ := min rhoL 1
  have hrho : 0 < rho := lt_min hrhoL (by norm_num)
  let A : ℝ := (((3/2 : ℝ)^p)^2 * C * B)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let Cstar : ℝ := (CH+1) * ((5*11 : ℝ) * T * (A+M))
  have hCstar : 0 < Cstar := by
    dsimp [Cstar]
    have hAM : 0 < A+M := by linarith
    positivity
  have hGeometryRho : ∀ delta : ℝ, 0 < delta → ∀ y ∈ K,
      referenceRadius delta Rstar p L y < rho →
        let s := (referenceRadius delta Rstar p L y) ^ ((1 : ℝ) / 23)
        closedBall y s ⊆ W ∧ closedBall y s ⊆ interior cylinder ∧
        closedBall y s ⊆ closedBall (0 : R3) 3 ∧
        ∀ z ∈ closedBall y s, chi z = 1 := by
    intro delta hDelta y hy hrsmall
    exact hGeometry delta hDelta y hy (hrsmall.trans_le (min_le_left _ _))
  refine ⟨rho,Cstar,hrho,hCstar,hGeometryRho,?_⟩
  intro lam hLam delta hDelta Psi hPsi hPsiCompact hMoment hDensity y hy hrsmall
  let r : ℝ := referenceRadius delta Rstar p L y
  let s : ℝ := r ^ ((1 : ℝ)/23)
  have hr : 0 < r := referenceRadius_pos delta Rstar p L y hDelta hRstar
  have hs : 0 < s := Real.rpow_pos_of_pos hr _
  have hr1 : r ≤ 1 := (hrsmall.trans_le (min_le_right _ _)).le
  have hrL : r < rhoL := hrsmall.trans_le (min_le_left _ _)
  have hGeom := hGeometry delta hDelta y hy hrL
  dsimp at hGeom
  have hBallCyl : closedBall y s ⊆ cylinder :=
    hGeom.2.1.trans interior_subset
  let V : Set R3 := (fun x : R3 => (lam,x)) ⁻¹' U
  have hVopen : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hVCyl : cylinder ⊆ V := fun x hx => hStrip ⟨hLam,hx⟩
  have hyCyl : y ∈ cylinder := interior_subset (hKinside hy)
  have hyV : y ∈ V := hVCyl hyCyl
  have hBallV : closedBall y s ⊆ V := hBallCyl.trans hVCyl
  have hSlice : ContDiff ℝ ∞ (fun x : R3 => (x,lam)) :=
    contDiff_id.prodMk contDiff_const
  have hRange : MapsTo (fun x : R3 => (x,lam)) V (Prod.swap ⁻¹' U) :=
    fun _ hx => hx
  let F : Fin 5 → R3 → ℝ := fun k x => R1 k (x,lam)-R2 k (x,lam)
  have hProfiles (k : Fin 5) : ContDiffOn ℝ ∞ (F k) V :=
    ((hR1 k).comp hSlice.contDiffOn hRange).sub
      ((hR2 k).comp hSlice.contDiffOn hRange)
  have hL2 (k : Fin 5) :
      (eLpNorm (F k) 2 (volume.restrict (ball y s))).toReal ≤ A*r^2 := by
    simpa [F,r,s,A] using
      (hLocal R1 R2 etaA U hU hStrip hR1 hR2 C B hC hB
        volume lam hLam delta hDelta Psi hPsi hPsiCompact hMoment hDensity
        y hy hrL k)
  have hJets (k : Fin 5) (n : ℕ) (hn : n ≤ 10) :
      ‖iteratedFDeriv ℝ n (F k) y‖ ≤ T*(A+M)*r^(3/2 : ℝ) := by
    apply hInterp (F k) V y r A M n hVopen (hProfiles k) hyV hr hr1 hA
      (by linarith) hBallV
    · intro x hx
      exact hM k lam hLam x (hBallCyl hx)
    · exact hL2 k
    · exact hn
  have hMetric := hH8 lam hLam y hyCyl
  have hSum :
      (∑ k : Fin 5, ∑ n ∈ Finset.range 11,
        ‖iteratedFDeriv ℝ n (F k) y‖) ≤
      (5*11 : ℝ) * (T*(A+M)*r^(3/2 : ℝ)) := by
    calc
      _ ≤ ∑ k : Fin 5, ∑ n ∈ Finset.range 11,
        T*(A+M)*r^(3/2 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro n hn
          exact hJets k n (by have := Finset.mem_range.mp hn; omega)
      _ = (5*11 : ℝ) * (T*(A+M)*r^(3/2 : ℝ)) := by simp; ring
  calc
    coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y
        ≤ CH * (∑ k : Fin 5, ∑ n ∈ Finset.range 11,
          ‖iteratedFDeriv ℝ n (F k) y‖) := by simpa [F] using hMetric
    _ ≤ CH * ((5*11 : ℝ) * (T*(A+M)*r^(3/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hSum hCH
    _ ≤ (CH+1) * ((5*11 : ℝ) * (T*(A+M)*r^(3/2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = Cstar * r^(3/2 : ℝ) := by dsimp [Cstar]; ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
