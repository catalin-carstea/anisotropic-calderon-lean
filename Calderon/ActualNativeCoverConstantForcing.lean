import Calderon.ActualConstantOneOriginalLocalBound
import Calderon.ActualCenteredNativeCover
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError
  ConformalDepth CoordinateBootstrapJets NormalizedPrincipalMetric ReferenceWeightedApproximation SphereHarmonic
attribute [local irreducible] harmonicSphereSubspace sphereSobolevInclusionL
  referencePhysicalDensityOperator sphereSobolevConstantOne

def NativeConstantForcingUniformHalfBound
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L) : Prop :=
  ∃ p0 : ℕ, 1 ≤ p0 ∧ ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
    ∀ p : ℕ, p0 ≤ p → ∀ q ∈ Icc (0:ℝ) 1,
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ Rstar : ℝ, 0 < Rstar →
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
    ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
    coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L q) y ≤
      eps*referenceRadius delta Rstar p L y →
    referenceRadius delta Rstar p L y*(actualReferenceBeta S.g1 L q delta Rstar p y)^2 ≤ eps →
    ∃ v : SphereSobolev (1/2:ℝ), ‖v‖ ≤ C0 ∧
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v =
        referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible hcalc hF hO hD τ0 S.g2 q (referenceRadius delta Rstar p L)
          (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y

theorem nativeConstantForcingUniformHalfBound_of_rho_center_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (hL : 0 < L) (cover : NativeNormalCover S L)
    (hCenter : ∀ i, ∀ y ∈ (cover.packet i).centers, ‖y-(cover.packet i).y0‖ < (cover.packet i).rho) :
    NativeConstantForcingUniformHalfBound hcalc hF hO hD τ0 S L cover := by
  have hEach (i : Fin cover.count) := exists_uniform_original_constant_one_local_half_bound_of_bootstrap
    S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
    (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
    (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
    S.g1_admissible hcalc hF hO hD τ0 S.g2 S.g2_admissible hreg hL (cover.packet i).rho_positive
  choose pi hpi ei hei hei1 ci hci hBound using hEach
  obtain ⟨pMax,hpMax⟩ := (Set.finite_range pi).bddAbove
  obtain ⟨eMin,heMin,heMinAll⟩ := Geometry.exists_pos_le_finite ei hei
  obtain ⟨cMax,hcMax⟩ := (Set.finite_range ci).bddAbove
  refine ⟨max pMax 1,le_max_right _ _,min eMin 1,lt_min heMin one_pos,min_le_right _ _,max cMax 1,le_max_right _ _,?_⟩
  intro p hp q hq delta hdelta hdelta1 Rstar hRstar eps heps hepsSmall i y hy hPrincipal hRadius
  have hpI : pi i ≤ p := ((hpMax ⟨i,rfl⟩).trans (le_max_left _ _)).trans hp
  have heI : eps ≤ ei i := hepsSmall.trans ((min_le_left _ _).trans (heMinAll i))
  obtain ⟨v,hv,hEq⟩ := hBound i p hpI q hq delta hdelta hdelta1 Rstar hRstar eps heps heI y
    (hCenter i y hy.2) hPrincipal hRadius
  exact ⟨v,hv.trans ((hcMax ⟨i,rfl⟩).trans (le_max_left _ _)),hEq⟩

theorem exists_nativeNormalCover_with_uniform_constant_forcing
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (hL : 0 < L) :
    ∃ cover : NativeNormalCover S L,
      (∀ i, ∀ y ∈ (cover.packet i).centers, ‖y-(cover.packet i).y0‖ < (cover.packet i).rho) ∧
      NativeConstantForcingUniformHalfBound hcalc hF hO hD τ0 S L cover := by
  obtain ⟨cover,hCenter⟩ := NativeCenteredCover.exists_nativeNormalCover_with_rho_center_room S L
  exact ⟨cover,hCenter,nativeConstantForcingUniformHalfBound_of_rho_center_room
    hcalc hreg hF hO hD τ0 S L hL cover hCenter⟩

theorem nativeConstantForcingUniformHalfBound_currentBootstrap
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (hBound : NativeConstantForcingUniformHalfBound hcalc hF hO hD τ0 S L cover) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∃ v : SphereSobolev (1/2:ℝ), ‖v‖ ≤ C0 ∧
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v =
          referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
            (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
            (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
            S.g1_admissible hcalc hF hO hD τ0 S.g2 q (referenceRadius delta Rstar p L)
            (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y := by
  obtain ⟨p0,hp0,eps0,heps0,heps01,C0,hC0,hPoint⟩ := hBound
  refine ⟨p0,hp0,eps0,heps0,heps01,C0,hC0,?_⟩
  intro p hp q hq delta hdelta hdelta1 Rstar hRstar eps heps hepsSmall hBootstrap i y hy
  exact hPoint p hp q hq delta hdelta hdelta1 Rstar hRstar eps heps hepsSmall i y hy
    (hBootstrap.1 y hy.1) (hBootstrap.2 delta ⟨le_rfl,hdelta1⟩ y hy.1)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
