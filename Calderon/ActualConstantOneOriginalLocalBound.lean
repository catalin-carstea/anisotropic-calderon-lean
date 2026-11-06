import Calderon.ActualConstantOneUniformHalfBound
import Calderon.ActualRadiusBootstrapSmallJets
import Calderon.ActualReferenceGaugeRadialInverse
import Calderon.ActualJacobiCompactExtensionRoom
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth CoordinateBootstrapJets NormalizedPrincipalMetric ReferenceWeightedApproximation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace sphereSobolevInclusionL
  referencePhysicalDensityOperator referenceConstantOnePhysicalDensityHalfInRoom
  referenceHighDensityFirstAction sphereSobolevConstantOne

include hg in
private theorem original_constant_local_room_germ
    (hreg : FixedDirichletRegularity) (hρ : 0 < ρ)
    (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) (R : R3 → ℝ) (hR : Continuous R)
    (hPos : ∀ z : R3, 0 < R z) (y : R3) (hy : ‖y-y0‖ < ρ) (hr : |R y| < ρ) :
    ∀ᶠ z in 𝓝 y, ‖z-y0‖ ≤ ρ ∧ R z ≠ 0 ∧
      (q,(z,R z)) ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible ∧
      ∀ t ∈ uIcc (0:ℝ) (R z), (q,(z,t)) ∈
        referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
  have hyEvent : ∀ᶠ z in 𝓝 y, ‖z-y0‖ < ρ :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
  have hrEvent : ∀ᶠ z in 𝓝 y, |R z| < ρ :=
    (isOpen_lt hR.abs continuous_const).mem_nhds hr
  filter_upwards [hyEvent,hrEvent] with z hz hzr
  have hz4 : ‖z-y0‖ ≤ 4*ρ := hz.le.trans (by linarith)
  have hr4 : |R z| ≤ 4*ρ := hzr.le.trans (by linarith)
  have hAt := referenceRadialEndpointInvertibleLocus_mem_on_actual_room
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q hq z hz4 (R z) hr4
  refine ⟨hz.le,(hPos z).ne',⟨hq,?_,abs_le.mp hzr.le⟩,hAt.2.1,?_⟩
  · simpa only [mem_closedBall,dist_eq_norm] using hz.le
  · intro t ht
    have ht0 : 0 ≤ t := (uIcc_of_le (hPos z).le ▸ ht).1
    have htR : t ≤ R z := (uIcc_of_le (hPos z).le ▸ ht).2
    have ht4 : |t| ≤ 4*ρ := by rw [abs_of_nonneg ht0]; linarith [le_abs_self (R z)]
    exact referenceRadialEndpointInvertibleLocus_mem_on_actual_room
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q hq z hz4 t ht4

theorem exists_uniform_original_constant_one_local_half_bound_of_bootstrap
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (hL : 0 < L) (hρ : 0 < ρ) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → ∀ y : R3, ‖y-y0‖ < ρ →
      coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) y ≤
        eps*referenceRadius delta Rstar p L y →
      referenceRadius delta Rstar p L y*(actualReferenceBeta g L q delta Rstar p y)^2 ≤ eps →
      ∃ v : SphereSobolev (1/2:ℝ), ‖v‖ ≤ C0 ∧
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v =
          referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            g2 q (referenceRadius delta Rstar p L) (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y := by
  let K : Set (ℝ × (R3 × ℝ)) := Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hInvK : ∀ t ∈ K, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,(t.2,x.val))).IsInvertible := by
    rintro ⟨q,y,r⟩ ⟨hq,hy,hr⟩ x
    have hyρ : ‖y-y0‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have hrρ : |r| ≤ ρ := abs_le.mpr hr
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall
      g hg L y0 Φ B ε C ρ H a w hData q hq y (hyρ.trans (by linarith)) r (hrρ.trans (by linarith)) x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  obtain ⟨E⟩ := exists_referenceJacobiCompactExtensionRoom
    g hg L y0 Φ B ε C ρ H a w hData K hK hInvK
  obtain ⟨d,hd,hdρ,hd1,C0,hC0,hBound⟩ :=
    exists_uniform_referenceConstantOnePhysicalDensityHalfInRoom_bound
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 g2 hg2 hreg
  let d0 := min d (ρ/2)
  have hd0 : 0 < d0 := lt_min hd (by positivity)
  obtain ⟨p0,hp0,eps0,heps0,heps01,hSmall⟩ :=
    exists_uniform_referenceRadius_small_ordinary_jets_of_bootstrap
      g hg (closedBall y0 ρ) (isCompact_closedBall _ _) L hL d0 hd0
  refine ⟨p0,hp0,eps0,heps0,heps01,C0,hC0,?_⟩
  intro p hp q hq delta hdelta hdelta1 Rstar hRstar eps heps hepsSmall y hy hPrincipal hRadius
  let R := referenceRadius delta Rstar p L
  have hR : ContDiff ℝ ∞ R := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual
    delta Rstar p L hdelta hRstar
  have hPos (z : R3) : 0 < R z := referenceRadius_pos delta Rstar p L z hdelta hRstar
  have hyK : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy.le
  obtain ⟨hRsmall,hDR,hD2R⟩ := hSmall p hp q hq delta hdelta hdelta1 Rstar hRstar eps heps hepsSmall y hyK hRadius
  have hr : |R y| < ρ := hRsmall.trans_lt ((min_le_right d (ρ/2)).trans_lt (by linarith))
  let v := referenceConstantOnePhysicalDensityHalfInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 g2 q R y
  have hPointInv := hInvK (q,(y,R y)) ⟨hq,hyK,abs_le.mp hr.le⟩
  refine ⟨v,?_,?_⟩
  · exact hBound q hq delta hdelta Rstar hRstar p eps heps (hepsSmall.trans heps01) y hy.le
      (hRsmall.trans (min_le_left d (ρ/2))) hDR hD2R hPointInv hPrincipal
  · exact sphereSobolevInclusionL_referenceConstantOnePhysicalDensityHalfInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 g2 hreg q hq R hR y
      (original_constant_local_room_germ g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hρ q hq R hR.continuous hPos y hy hr)
      hPointInv

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
